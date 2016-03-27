#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(slice_patterns, advanced_slice_patterns)]

macro_rules! throw { ($($arg: tt)*) => { return Err(format!($($arg)*)) } }

extern crate clap;
extern crate itertools;
#[macro_use]
extern crate lazy_static;
extern crate petgraph;

#[macro_use]
extern crate rustc;
extern crate rustc_const_eval;
extern crate rustc_driver;
extern crate rustc_front;
extern crate rustc_metadata;
extern crate rustc_mir;
extern crate syntax;

mod component;
mod mir_graph;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::convert::AsRef;
use std::io;
use std::io::prelude::*;
use std::iter;
use std::fs::File;
use std::path;

use itertools::Itertools;
use petgraph::graph::{self, Graph};
use petgraph::algo::*;

use syntax::ast::{self, NodeId};
use rustc_front::hir::{self, FnDecl, Item_, PatKind};
use rustc_front::intravisit;
use rustc::mir::mir_map::MirMap;
use rustc::mir::repr::*;
use rustc::middle::cstore::CrateStore;
use rustc::middle::const_eval::ConstVal;
use rustc::middle::def_id::DefId;
use rustc::middle::subst::{ParamSpace, Subst};
use rustc::middle::traits::*;
use rustc::middle::ty::{self, Ty, TyCtxt};

use rustc_driver::driver;
use syntax::diagnostics;
use rustc::session;

use component::Component;

type TransResult = Result<String, String>;

trait ResultIterator<T, E> : Iterator<Item=Result<T, E>> where Self: Sized {
    fn collect_results(self) -> Result<std::vec::IntoIter<T>, E> {
        self.collect::<Result<Vec<_>, _>>().map(IntoIterator::into_iter)
    }
}

impl<I, T, E> ResultIterator<T, E> for I where I: Iterator<Item=Result<T, E>> { }

trait StringResultIterator<E> : Iterator<Item=Result<String, E>> where Self: Sized {
    fn join_results(self, sep: &str) -> Result<String, E> {
        self.collect_results().map(|mut it| it.join(sep))
    }
}

impl<T, E> StringResultIterator<E> for T where T: Iterator<Item=Result<String, E>> { }

fn main() {
    let matches = clap::App::new("rustabelle")
        .arg(clap::Arg::with_name("only")
             .help("only export the listed items and their dependencies")
             .long("only")
             .takes_value(true))
        .arg(clap::Arg::with_name("RUSTC_ARGS")
             .help("arguments forwarded to rustc")
             .multiple(true)
             .use_delimiter(false))
        .get_matches();

    let targets = matches.values_of("only").map(|targets| targets.map(str::to_string).collect_vec());
    let rustc_args = iter::once("rustc").chain(matches.values_of("RUSTC_ARGS").unwrap()).map(str::to_string).collect_vec();
    let rustc_matches = rustc_driver::handle_options(rustc_args).expect("error parsing rustc args");
    let options = session::config::build_session_options(&rustc_matches);
    let input = match &rustc_matches.free[..] {
        [ref file] => path::PathBuf::from(file),
        _ => panic!("expected input file"),
    };

    let cstore = std::rc::Rc::new(rustc_metadata::cstore::CStore::new(syntax::parse::token::get_ident_interner()));
    let sess = session::build_session(options, Some(input.clone()),
        diagnostics::registry::Registry::new(&rustc::DIAGNOSTICS),
        cstore.clone()
    );
    let cfg = session::config::build_configuration(&sess);
    println!("Compiling up to MIR...");
    driver::compile_input(&sess, &cstore, cfg,
        &session::config::Input::File(input),
        &None, &None, None, &driver::CompileController {
            after_analysis: driver::PhaseController {
                stop: rustc_driver::Compilation::Stop,
                callback: Box::new(|state| transpile_crate(&state, targets.as_ref()).unwrap()),
                run_callback_on_error: false,
            },
            .. driver::CompileController::basic()
        }
    );
}

/// value that indicates whether evaluating it can panic
struct MaybeValue {
    val: String,
    total: bool,
}

impl MaybeValue {
    fn total<T: Into<String>>(val: T) -> MaybeValue { MaybeValue { val: val.into(), total: true } }
    fn partial<T: Into<String>>(val: T) -> MaybeValue { MaybeValue { val: val.into(), total: false } }

    fn map<F>(self, f: F) -> MaybeValue
        where F: Fn(String) -> String {
        MaybeValue { val: f(self.val), ..self }
    }
}

fn mk_lean_name(s: &str) -> String {
    let s = s.replace("::", ".").replace(|c: char| c != '.' && !c.is_alphanumeric(), "_").trim_left_matches('_').to_owned();
    if s.ends_with("end") || s.ends_with("by") { s + "_" } else { s }
}

fn unwrap_refs<'tcx>(ty: Ty<'tcx>) -> Ty<'tcx> {
    match ty.sty {
        ty::TypeVariants::TyRef(_, ty::TypeAndMut { ty, .. }) => unwrap_refs(ty),
        _ => ty
    }
}

fn try_unwrap_mut_ref<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.sty {
        ty::TypeVariants::TyRef(_, ty::TypeAndMut { mutbl: hir::Mutability::MutMutable, ty }) =>
            Some(ty),
        _ => None
    }
}

fn format_generic_ty<It: Iterator<Item=String>>(ty: &str, generics: It) -> String {
    iter::once(ty.to_string()).chain(generics).join(" ")
}

fn get_tuple_elem<S : AsRef<str>>(value: S, idx: usize, len: usize) -> String {
    let fsts = iter::repeat(".1").take(len - idx - 1);
    let snd = if idx == 0 { None } else { Some(".2") };
    iter::once(value.as_ref()).chain(fsts).chain(snd).join("")
}

fn detuplize(val: &str, pat: &[String], cont: &str) -> String {
    match pat {
        [ref x] => format!("let {} := {} in\n{}", x, val, cont),
        _ => format!("match {} with ({}) :=\n{}end\n", val, pat.into_iter().join(", "), cont),
    }
}

struct Deps {
    crate_deps: HashSet<String>,
    def_idcs: HashMap<NodeId, graph::NodeIndex>,
    graph: Graph<NodeId, ()>,
}

impl Deps {
    fn get_def_idx(&mut self, id: NodeId) -> graph::NodeIndex {
        let Deps { ref mut def_idcs, ref mut graph, .. } = *self;
        *def_idcs.entry(id).or_insert_with(|| graph.add_node(id))
    }

    fn add_dep(&mut self, used: NodeId, user: NodeId) {
        let from = self.get_def_idx(used);
        let to = self.get_def_idx(user);
        self.graph.add_edge(from, to, ());
    }
}

pub struct Transpiler<'a, 'tcx: 'a> {
    tcx: &'a TyCtxt<'tcx>,
    mir_map: &'a MirMap<'tcx>,
    trans_results: HashMap<NodeId, TransResult>,
    deps: RefCell<Deps>,

    // inside of fns
    node_id: ast::NodeId,
    param_names: Vec<String>,
    static_params: Vec<String>,
    refs: RefCell<HashMap<usize, &'a Lvalue<'tcx>>>,
}

enum TraitImplLookup { Static(DefId), Dynamic }

fn transpile_def_id(tcx: &TyCtxt, did: DefId) -> String {
    mk_lean_name(&tcx.item_path_str(did))
}

fn transpile_node_id(tcx: &TyCtxt, node_id: ast::NodeId) -> String {
    transpile_def_id(tcx, tcx.map.local_def_id(node_id))
}

lazy_static! {
    static ref INTRINSICS: HashSet<String> = vec![
        "intrinsics.add_with_overflow",
        "intrinsics.sub_with_overflow",
        "intrinsics.mul_with_overflow",
    ].into_iter().map(str::to_string).collect();
}

impl<'a, 'tcx> Transpiler<'a, 'tcx> {
    fn add_dep(&self, did: DefId) {
        if let Some(node_id) = self.tcx.map.as_local_node_id(did) {
            self.deps.borrow_mut().add_dep(node_id, self.node_id);
        } else {
            let crate_name = self.tcx.sess.cstore.crate_name(did.krate);
            self.deps.borrow_mut().crate_deps.insert(crate_name.clone());
        }
    }

    fn transpile_def_id(&self, did: DefId) -> String {
        self.add_dep(did);
        transpile_def_id(self.tcx, did)
    }

    fn transpile_node_id(&self, node_id: ast::NodeId) -> String {
        self.transpile_def_id(self.tcx.map.local_def_id(node_id))
    }

    fn transpile_trait_ref_args(&self, trait_ref: ty::TraitRef<'tcx>) -> Result<Vec<String>, String> {
        trait_ref.substs.types.iter().map(|ty| {
            self.transpile_ty(ty)
        }).collect_results().map(Iterator::collect)
    }

    fn transpile_associated_type(&self, trait_ref: ty::TraitRef<'tcx>, name: &ast::Name) -> TransResult {
        let prefix = iter::once(self.transpile_def_id(trait_ref.def_id).replace('.', "_")).join("_");
        let prefix = mk_lean_name(&prefix);
        Ok(format!("{}_{}", prefix, name))
    }

    fn get_assoc_ty_substs(&self, def_id: DefId) -> Result<HashMap<String, String>, String> {
        self.tcx.lookup_predicates(def_id).predicates.into_iter().map(|trait_pred| Ok(match trait_pred {
            ty::Predicate::Projection(ty::Binder(proj_pred)) => {
                let assoc_ty = try!(self.transpile_associated_type(proj_pred.projection_ty.trait_ref, &proj_pred.projection_ty.item_name));
                Some((assoc_ty, try!(self.transpile_ty(&proj_pred.ty))))
            }
            _ => None,
        })).collect_results().map(|xs| xs.filter_map(|x| x).collect())
    }

    fn transpile_trait_ref_assoc_tys(&self, trait_ref: ty::TraitRef<'tcx>, assoc_ty_substs: &HashMap<String, String>) -> (Vec<String>, Vec<String>) {
        let mut free_assoc_tys = vec![];
        let assoc_tys = self.trait_predicates_without_markers(trait_ref.def_id).flat_map(|trait_pred| {
            let trait_def = self.tcx.lookup_trait_def(trait_pred.def_id());
            trait_def.associated_type_names.iter().map(|name| {
                let assoc_ty = self.transpile_associated_type(trait_ref, name).unwrap();
                match assoc_ty_substs.get(&assoc_ty) {
                    Some(assoc_ty) => assoc_ty.to_owned(),
                    _ => {
                        free_assoc_tys.push(assoc_ty.clone());
                        assoc_ty
                    }
                }
            }).collect_vec()
        }).collect();

        (assoc_tys, free_assoc_tys)
    }

    fn transpile_trait_ref(&self, trait_ref: ty::TraitRef<'tcx>, assoc_ty_substs: &HashMap<String, String>) -> TransResult {
        let associated_types = self.transpile_trait_ref_assoc_tys(trait_ref, assoc_ty_substs).0;
        Ok(iter::once(self.transpile_def_id(trait_ref.def_id)).chain(try!(self.transpile_trait_ref_args(trait_ref))).chain(associated_types).join(" "))
    }

    fn transpile_ty(&self, ty: Ty<'tcx>) -> TransResult {
        Ok(match ty.sty {
            ty::TypeVariants::TyBool => "Prop".to_string(),
            ty::TypeVariants::TyUint(ref ty) => ty.to_string(),
            //ty::TypeVariants::TyInt(ref ty) => ty.to_string(),
            //ty::TypeVariants::TyFloat(ref ty) => ty.to_string(),
            ty::TypeVariants::TyTuple(ref tys) => match &tys[..] {
                [] => "unit".to_string(),
                _ => format!("({})", try!(tys.iter().map(|ty| self.transpile_ty(ty)).join_results(" × "))),
            },
            ty::TypeVariants::TyFnDef(_, _, ref data) | ty::TypeVariants::TyFnPtr(ref data) => {
                let sig = data.sig.skip_binder();
                let muts = sig.inputs.iter().filter_map(|ty| try_unwrap_mut_ref(ty));
                let inputs = try!(sig.inputs.iter().map(|ty| self.transpile_ty(ty)).collect_results());
                let outputs = match sig.output {
                    ty::FnOutput::FnConverging(out_ty) => try!(iter::once(out_ty).chain(muts).map(|ty| self.transpile_ty(ty)).join_results(" × ")),
                    ty::FnOutput::FnDiverging => throw!("unimplemented: diverging function"),
                };
                inputs.chain(iter::once(format!("option ({})", outputs))).join(" → ")
            },
            ty::TypeVariants::TyStruct(ref adt_def, ref substs) |
            ty::TypeVariants::TyEnum(ref adt_def, ref substs) => format!("({})", format_generic_ty(
                &self.transpile_def_id(adt_def.did),
                try!(substs.types.iter().map(|ty| self.transpile_ty(ty)).collect_results())
            )),
            ty::TypeVariants::TyRef(_, ref data) => try!(self.transpile_ty(data.ty)),
            ty::TypeVariants::TyParam(ref param) => param.name.to_string(),
            ty::TypeVariants::TyProjection(ref proj) => try!(self.transpile_associated_type(proj.trait_ref, &proj.item_name)),
            ty::TypeVariants::TySlice(ref ty) => format!("(slice {})", try!(self.transpile_ty(ty))),
            ty::TypeVariants::TyTrait(_) => throw!("unimplemented: trait objects"),
            _ => match ty.ty_to_def_id() {
                Some(did) => self.transpile_def_id(did),
                None => throw!("unimplemented: ty {:?}", ty),
            }
        })
    }

    fn transpile_hir_ty(&self, ty: &hir::Ty) -> TransResult {
        self.transpile_ty(self.hir_ty_to_ty(ty))
    }

    fn trait_predicates(&self, trait_def_id: DefId) -> std::vec::IntoIter<ty::TraitPredicate<'tcx>> {
        self.tcx.lookup_predicates(trait_def_id).predicates.into_iter().filter_map(|trait_pred| match trait_pred {
            ty::Predicate::Trait(trait_pred) => Some(trait_pred.0),
            _ => None,
        }).collect_vec().into_iter()
    }

    fn is_marker_trait(&self, trait_def_id: DefId) -> bool {
        self.tcx.trait_items(trait_def_id).is_empty() &&
        self.trait_predicates(trait_def_id).all(|trait_pred| {
            trait_pred.def_id() == trait_def_id || self.is_marker_trait(trait_pred.def_id())
        })
    }

    fn trait_predicates_without_markers(&self, trait_def_id: DefId) -> std::vec::IntoIter<ty::TraitPredicate<'tcx>> {
        self.trait_predicates(trait_def_id).filter(|trait_pred| !self.is_marker_trait(trait_pred.def_id())).collect_vec().into_iter()
    }

    fn def_id(&self) -> DefId {
        self.tcx.map.local_def_id(self.node_id)
    }

    fn mir(&self) -> &'a Mir<'tcx> {
        &self.mir_map.map[&self.node_id]
    }

    fn local_name(&self, lv: &Lvalue) -> String {
        match *lv {
            Lvalue::Var(idx) => mk_lean_name(&self.mir().var_decls[idx as usize].name.as_str()),
            Lvalue::Temp(idx) => format!("t{}", idx),
            Lvalue::Arg(idx) => self.param_names[idx as usize].clone(),
            Lvalue::ReturnPointer => "ret".to_string(),
            _ => panic!("not a local: {:?}", lv),
        }
    }

    fn deref_mut(&self, lv: &Lvalue) -> Option<&Lvalue<'tcx>> {
        if let Some(lv_idx) = self.lvalue_idx(lv).ok() {
            if let Some(lv) = self.refs.borrow().get(&lv_idx) {
                return Some(lv)
            }
        }
        None
    }

    fn lvalue_name(&self, lv: &Lvalue) -> Option<String> {
        if let Some(lv) = self.deref_mut(lv) {
            return self.lvalue_name(lv)
        }

        Some(match *lv {
            Lvalue::Var(..) | Lvalue::Temp(..) | Lvalue::Arg(..) | Lvalue::ReturnPointer => self.local_name(lv),
            Lvalue::Static(did) => self.transpile_def_id(did),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                return self.lvalue_name(base),
            Lvalue::Projection(_) => return None,
        })
    }

    fn num_locals(&self) -> usize {
        self.mir().var_decls.len() + self.mir().temp_decls.len() + 1
    }

    fn locals(&self) -> Vec<String> {
        self.mir().var_decls.iter().enumerate().map(|(idx, _)| Lvalue::Var(idx as u32))
            .chain(self.mir().temp_decls.iter().enumerate().map(|(idx, _)| Lvalue::Temp(idx as u32)))
            .chain(iter::once(Lvalue::ReturnPointer))
            .map(|lv| self.local_name(&lv))
            .collect()
    }

    fn get_lvalue(&self, lv: &Lvalue<'tcx>) -> TransResult {
        if let Some(lv) = self.deref_mut(lv) {
            return self.get_lvalue(lv)
        }
        if let Some(name) = self.lvalue_name(lv) {
            return Ok(name)
        }

        match *lv {
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.get_lvalue(base),
            Lvalue::Projection(box Projection {
                elem: ProjectionElem::Field(ref field, _),
                base: Lvalue::Projection(box Projection {
                    ref base,
                    elem: ProjectionElem::Downcast(..),
                }),
            }) =>
                Ok(format!("{}_{}", try!(self.get_lvalue(base)), field.index())),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(ref field, _) }) =>
                Ok(match unwrap_refs(self.lvalue_ty(base)).sty {
                    ty::TypeVariants::TyTuple(ref tys) =>
                        get_tuple_elem(try!(self.get_lvalue(base)), field.index(), tys.len()),
                    ty::TypeVariants::TyStruct(ref adt_def, _) => {
                        if adt_def.struct_variant().is_tuple_struct() {
                            format!("match {} with {} x := x end",
                                    get_tuple_elem(try!(self.get_lvalue(base)), field.index(), adt_def.struct_variant().fields.len()),
                                    self.transpile_def_id(adt_def.did))
                        } else {
                            format!("({}.{} {})",
                                    self.transpile_def_id(adt_def.did),
                                    mk_lean_name(&adt_def.struct_variant().fields[field.index()].name.as_str()),
                                    try!(self.get_lvalue(base)))
                        }
                    }
                    ref ty => throw!("unimplemented: accessing field of {:?}", ty),
                }),
            _ => Err(format!("unimplemented: loading {:?}", lv)),
        }
    }

    fn lvalue_ty(&self, lv: &Lvalue<'tcx>) -> Ty<'tcx> {
        self.mir().lvalue_ty(self.tcx, lv).to_ty(self.tcx)
    }

    fn lvalue_idx(&self, lv: &Lvalue) -> Result<usize, String> {
        Ok(match *lv {
            Lvalue::Var(idx) => idx as usize,
            Lvalue::Temp(idx) => self.mir().var_decls.len() + idx as usize,
            Lvalue::ReturnPointer => self.num_locals() - 1,
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                try!(self.lvalue_idx(base)),
            _ => throw!("unimplemented: storing {:?}", lv),
        })
    }

    fn set_lvalue(&self, lv: &Lvalue<'tcx>, val: &str) -> TransResult {
        if let Some(lv) = self.deref_mut(lv) {
            return self.set_lvalue(lv, val)
        }
        if let Some(name) = self.lvalue_name(lv) {
            return Ok(format!("let {} := {} in\n", name, val));
        }
        match *lv {
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.set_lvalue(base, val),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(ref field, _) }) => {
                let base_name = try!(self.lvalue_name(base).ok_or_else(|| format!("ugh, nested fields assignments? {:?}", lv)));
                match unwrap_refs(self.lvalue_ty(base)).sty {
                    ty::TypeVariants::TyStruct(ref adt_def, _) => {
                        let field_name = adt_def.struct_variant().fields[field.index()].name;
                        Ok(format!("let {} := ⦃ {}, {} := {}, {} ⦄ in\n", base_name, self.transpile_def_id(adt_def.did), field_name, val, base_name))
                    },
                    ref ty => throw!("unimplemented: setting field of {:?}", ty),
                }
            }
            _ => throw!("unimplemented: setting lvalue {:?}", lv),
        }
    }

    fn set_lvalues_option<'b>(&self, lvs: Vec<&'b Lvalue<'tcx>>, val: &str, cont: &str) -> TransResult {
        let (direct_dests, indirect_dests): (Vec<_>, Vec<_>) = try!(lvs.into_iter().map(|lv| -> Result<_, String> {
            Ok(match self.lvalue_name(lv) {
                Some(name) => (name, None),
                None => (self.local_name(lv), Some(try!(self.set_lvalue(self.deref_mut(lv).unwrap(), &self.local_name(lv)))))
            })
        }).collect_results()).unzip();
        let indirect_dests = indirect_dests.into_iter().filter_map(|x| x).join("");
        Ok(format!("do tmp__ ← {};\n{}", val,
                   detuplize("tmp__", &direct_dests[..], &(indirect_dests + cont))))
    }

    fn transpile_constval(&self, val: &ConstVal) -> TransResult {
        Ok(match *val {
            ConstVal::Bool(b) => b.to_string(),
            ConstVal::Integral(i) => match i.int_type() {
                Some(syntax::attr::IntType::UnsignedInt(_)) =>
                    i.to_u64_unchecked().to_string(),
                _ => throw!("unimplemented: literal {:?}", val),
            },
            _ => throw!("unimplemented: literal {:?}", val),
        })
    }

    fn transpile_constant(&self, c: &Constant) -> TransResult {
        match c.literal {
            Literal::Value { ref value } => self.transpile_constval(value),
            _ => throw!("unimplemented: constant {:?}", c),
        }
    }

    fn get_operand(&self, op: &Operand<'tcx>) -> TransResult {
        Ok(match *op {
            Operand::Consume(ref lv) => try!(self.get_lvalue(lv)),
            Operand::Constant(ref c) => try!(self.transpile_constant(c)),
        })
    }

    fn get_rvalue(&self, rv: &Rvalue<'tcx>) -> Result<MaybeValue, String> {
        Ok(MaybeValue::total(match *rv {
            Rvalue::Use(ref op) => try!(self.get_operand(op)),
            Rvalue::UnaryOp(op, ref operand) =>
                format!("{} {}", match op {
                    UnOp::Not if self.mir().operand_ty(self.tcx, operand).is_bool() => "bool.bnot",
                    UnOp::Not => "NOT",
                    UnOp::Neg => "-",
                }, try!(self.get_operand(operand))),
            Rvalue::BinaryOp(op, ref o1, ref o2) => {
                let (so1, so2) = (try!(self.get_operand(o1)), try!(self.get_operand(o2)));
                return Ok(match op {
                    BinOp::Sub if !self.mir().operand_ty(self.tcx, o1).is_signed() => MaybeValue::partial(format!("{} {} {}", "checked.sub", so1, so2)),
                    BinOp::Div => MaybeValue::partial(format!("{} {} {}", "checked.div", so1, so2)),
                    BinOp::Rem => MaybeValue::partial(format!("{} {} {}", "checked.mod", so1, so2)),
                    BinOp::Shl => MaybeValue::partial(format!("{} {} {}", "checked.shl", so1, so2)),
                    BinOp::Shr => MaybeValue::partial(format!("{} {} {}", "checked.shr", so1, so2)),
                    _ => MaybeValue::total(format!("{} {} {}", so1, match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        BinOp::Mul => "*",
                        BinOp::BitXor => "XOR",
                        BinOp::BitAnd => "AND",
                        BinOp::BitOr => "OR",
                        BinOp::Eq => "=",
                        BinOp::Lt => "<",
                        BinOp::Le => "<=",
                        BinOp::Ne => "≠",
                        BinOp::Ge => ">=",
                        BinOp::Gt => ">",
                        _ => unreachable!(),
                    }, so2))
                })
            }
            Rvalue::Cast(CastKind::Misc, ref op, _) => try!(self.get_operand(op)),
            Rvalue::Ref(_, BorrowKind::Shared, ref lv) => try!(self.get_lvalue(lv)),
            Rvalue::Aggregate(AggregateKind::Tuple, ref ops) => {
                let mut ops = try!(ops.iter().map(|op| self.get_operand(op)).collect_results());
                format!("({})", ops.join(", "))
            }
            Rvalue::Aggregate(AggregateKind::Adt(ref adt_def, variant_idx, _), ref ops) => {
                self.add_dep(adt_def.did);

                let variant = &adt_def.variants[variant_idx];
                let ops = try!(ops.iter().map(|op| self.get_operand(op)).collect::<Result<Vec<_>, _>>());
                format!("{}{} {}",
                        self.transpile_def_id(variant.did),
                        if adt_def.adt_kind() == ty::AdtKind::Struct && !adt_def.struct_variant().is_tuple_struct() { ".mk" } else { "" },
                        ops.iter().join(" "))
            }
            _ => return Err(format!("unimplemented: rvalue {:?}", rv)),
        }))
    }

    fn transpile_statement(&self, stmt: &'a Statement<'tcx>, comp: &mut Component) -> TransResult {
        match stmt.kind {
            StatementKind::Assign(ref lv, ref rv) => {
                if let Rvalue::Ref(_, BorrowKind::Mut, ref lsource) = *rv {
                    self.refs.borrow_mut().insert(try!(self.lvalue_idx(lv)), lsource);
                    return Ok("".to_string())
                }
                if *lv != Lvalue::ReturnPointer && self.lvalue_ty(lv).is_nil() {
                    // optimization/rustc_mir workaround: don't save '()'
                    return Ok("".to_string())
                }

                if let Some(name) = self.lvalue_name(lv) {
                    comp.live_defs.insert(name);
                }

                match try!(self.get_rvalue(rv)) {
                    MaybeValue { val, total: true } => self.set_lvalue(lv, &val),
                    MaybeValue { val, total: false } =>
                        Ok(format!("do tmp__ ← {};\n{}", &val, try!(self.set_lvalue(lv, "tmp__")))),
                }
            }
        }
    }

    fn transpile_basic_block_rec(&self, bb: BasicBlock, comp: &mut Component) -> TransResult {
        if comp.header == Some(bb) {
            Ok(format!("rec__ {}\n", comp.ret_val))
        } else {
            self.transpile_basic_block(bb, comp)
        }
    }

    fn call_return_dests<'b>(&self, call: &'b Terminator<'tcx>) -> Result<Vec<&'b Lvalue<'tcx>>, String> {
        match call {
            &Terminator::Call { ref args, destination: Some((ref lv, _)), .. } => {
                let muts = try!(args.iter().map(|op| Ok(match *op {
                    Operand::Consume(ref lv) => try_unwrap_mut_ref(self.lvalue_ty(lv)).map(|_| lv),
                    Operand::Constant(_) => None,
                })).collect::<Result<Vec<_>, String>>());
                Ok(iter::once(lv).chain(muts.into_iter().filter_map(|x| x)).collect())
            }
            _ => Ok(Vec::new()),
        }
    }

    fn infer_trait_impl(&self, trait_ref: ty::TraitRef<'tcx>, callee_def_id: DefId, add_dep: bool) -> Result<TraitImplLookup, String> {
        use rustc::middle::infer;

        // FIXME
        try!(self.transpile_trait_ref_args(trait_ref));

        let span = syntax::codemap::DUMMY_SP;
        let param_env = ty::ParameterEnvironment::for_item(self.tcx, self.node_id);
        let pred = ty::Binder(trait_ref).to_poly_trait_predicate().subst(self.tcx, &param_env.free_substs);
        let dbg_param_env = format!("{:?}", param_env.caller_bounds);
        let infcx = infer::new_infer_ctxt(self.tcx, &self.tcx.tables, Some(param_env), rustc::middle::traits::ProjectionMode::Any);
        let mut selcx = SelectionContext::new(&infcx);
        let obligation = Obligation::new(ObligationCause::misc(span, ast::DUMMY_NODE_ID), pred);
        let selection = match selcx.select(&obligation) {
            Ok(x) => x.unwrap(),
            Err(err) => throw!("obligation select: {:?} {:?} {:?}", obligation, err, dbg_param_env),
        };

        match selection {
            Vtable::VtableImpl(data) => {
                if add_dep {
                    self.add_dep(data.impl_def_id);
                }

                // add dependencies for nested obligations
                for obl in &data.nested {
                    match obl.predicate {
                        ty::Predicate::Trait(ref trait_pred) if !self.is_marker_trait(trait_pred.skip_binder().def_id()) => {
                            try!(self.infer_trait_impl(trait_pred.skip_binder().trait_ref, callee_def_id, true));
                        }
                        _ => {}
                    }
                }

                Ok(TraitImplLookup::Static(data.impl_def_id))
            },
            Vtable::VtableParam(_) => Ok(TraitImplLookup::Dynamic),
            vtable => throw!("unimplemented: vtable {:?}", vtable),
        }
    }

    fn transpile_basic_block(&self, bb: BasicBlock, comp: &mut Component) -> TransResult {
        macro_rules! rec { ($bb:expr) => { try!(self.transpile_basic_block_rec($bb, comp)) } }

        if !comp.blocks.contains(&bb) {
            comp.exits.insert(bb.index());
            return Ok(format!("some {}\n", comp.ret_val))
        }
        if let Some(l) = comp.loops.clone().into_iter().find(|l| l.contains(&bb)) {
            let mut l_comp = Component::new(self, bb, l, Some(&comp));
            let (l_defs, l_uses) = try!(l_comp.defs_uses(self));
            let nonlocal_defs = self.locals().into_iter().filter(|v| comp.live_defs.contains(v) && l_defs.contains(v)).collect_vec();
            let nonlocal_uses = self.locals().into_iter().filter(|v| comp.live_defs.contains(v) && l_uses.contains(v) && !l_defs.contains(v)).collect_vec();
            let params = self.static_params.iter().chain(nonlocal_uses.iter()).join(" ");
            l_comp.ret_val = format!("({})", nonlocal_defs.iter().join(", "));
            let body = try!(self.transpile_basic_block(bb, &mut l_comp));
            let name = format!("{}.loop_{}", transpile_def_id(&self.tcx, self.def_id()), bb.index());
            let exit = match &l_comp.exits.iter().collect_vec()[..] {
                [exit] => BasicBlock::new(*exit),
                _ => throw!("Oops, multiple loop exits: {:?}", l_comp)
            };
            comp.prelude.push(format!("noncomputable definition {name} {params} rec__ tmp__ :=\n{body}",
                                      name=name, params=params, body=detuplize("tmp__", &nonlocal_defs[..], &body)));
            return Ok(format!("do tmp__ ← fix_opt ({name} {params}) {defs};\n{cont}",
                              defs=l_comp.ret_val, name=name, params=params, cont=detuplize("tmp__", &nonlocal_defs[..], &rec!(exit))));
        }

        let data = self.mir().basic_block_data(bb);
        let stmts = try!(data.statements.iter().map(|s| self.transpile_statement(s, comp)).collect::<Result<Vec<_>, _>>());
        let terminator = match data.terminator {
            Some(ref terminator) => Some(match *terminator {
                Terminator::Goto { target } =>
                    rec!(target),
                Terminator::If { ref cond, targets: (bb_if, bb_else) } =>
                    format!("if {} then\n{}else\n{}", try!(self.get_operand(cond)),
                    rec!(bb_if),
                    rec!(bb_else)),
                Terminator::Return => try!(self.return_expr()),
                Terminator::Call {
                    func: Operand::Constant(Constant { literal: Literal::Item { def_id, ref substs }, .. }),
                    ref args, destination: Some((_, target)), ..
                } => {
                    let (target_def_id, ty_args) = match self.tcx.trait_of_item(def_id) {
                        Some(trait_def_id) => {
                            // from trans::meth::trans_method_callee
                            let trait_ref = substs.to_trait_ref(self.tcx, trait_def_id);
                            match try!(self.infer_trait_impl(trait_ref, def_id, false)) {
                                TraitImplLookup::Static(impl_def_id) => {
                                    let method = match self.tcx.impl_or_trait_item(def_id) {
                                        ty::MethodTraitItem(method) => method,
                                        _ => unreachable!(),
                                    };
                                    let trait_def = self.tcx.lookup_trait_def(method.container.id());
                                    let method = trait_def.ancestors(impl_def_id).fn_defs(&self.tcx, method.name).next().unwrap().item;
                                    (method.def_id, vec![])
                                }
                                TraitImplLookup::Dynamic => {
                                    let assoc_ty_substs = try!(self.get_assoc_ty_substs(self.def_id()));
                                    (def_id, try!(self.transpile_trait_ref_args(trait_ref)).into_iter()
                                     .chain(self.transpile_trait_ref_assoc_tys(trait_ref, &assoc_ty_substs).0).collect())
                                }
                            }
                        }
                        _ => (def_id, vec![])
                    };
                    let name = self.transpile_def_id(target_def_id);
                    if name.starts_with("intrinsics.") && !INTRINSICS.contains(&name) {
                        throw!("unimplemented intrinsics: {}", name);
                    }
                    let args = try!(args.iter().map(|op| self.get_operand(op)).collect::<Result<Vec<_>, _>>());
                    let call = iter::once(name).chain(ty_args).chain(args).join(" ");
                    try!(self.set_lvalues_option(try!(self.call_return_dests(&terminator)), &call, &rec!(target)))
                }
                Terminator::Call { .. } =>
                    throw!("unimplemented: call {:?}", terminator),
                Terminator::Switch { ref discr, ref adt_def, ref targets } => {
                    let value = try!(self.get_lvalue(discr));
                    let arms: TransResult = adt_def.variants.iter().zip(targets).map(|(var, &target)| {
                        let vars = (0..var.fields.len()).into_iter().map(|i| format!("{}_{}", value, i));
                        Ok(format!("| {} :=\n{}", iter::once(self.transpile_def_id(var.did)).chain(vars).join(" "), rec!(target)))
                    }).join_results("");
                    format!("match {} with\n{}end\n", value, try!(arms))
                },
                Terminator::SwitchInt { ref discr, switch_ty: _, ref values, ref targets } => {
                    let arms: Result<_, String> = values.iter().zip(targets).map(|(val, &target)| {
                        Ok(format!("| {} :=\n{}", try!(self.transpile_constval(val)), rec!(target)))
                    }).collect_results();
                    let fallback = format!("| _ :=\n{}", rec!(*targets.last().unwrap()));
                    format!("match {} with\n{}\nend\n", try!(self.get_lvalue(discr)),
                        try!(arms).chain(iter::once(fallback)).join(""))
                },
                Terminator::Drop { target, .. } => rec!(target),
                Terminator::Resume => String::new(),
            }),
            None => None,
        };
        Ok(stmts.into_iter().chain(terminator.into_iter()).join(""))
    }

    fn hir_ty_to_ty(&self, ty: &hir::Ty) -> Ty<'tcx> {
        self.tcx.ast_ty_to_ty_cache.borrow()[&ty.id]
    }

    fn sig(&self) -> &ty::FnSig<'tcx> {
        self.tcx.node_id_to_type(self.node_id).fn_sig().skip_binder()
    }

    fn return_expr(&self) -> TransResult {
        let muts = self.sig().inputs.iter().zip(self.param_names.iter()).filter_map(|(ty, name)| {
            try_unwrap_mut_ref(ty).map(|_| name.clone())
        });
        let ret = if self.sig().output.unwrap().is_nil() { "()" } else { "ret" };
        Ok(format!("some ({})\n", iter::once(ret.to_string()).chain(muts).join(", ")))
    }

    fn transpile_fn(&mut self, name: String, decl: &FnDecl, ty_params: Vec<&hir::TyParam>, suppress_type_predicates: bool) -> TransResult {
        // FIXME... or not
        if name.starts_with("tuple._A__B__C__D") {
            return Ok("".into())
        }

        self.refs.borrow_mut().clear();
        self.param_names = decl.inputs.iter().enumerate().map(|(i, param)| match param.pat.node {
            PatKind::Ident(_, ref ident, _) => mk_lean_name(&ident.node.name.to_string()),
            _ => format!("p{}", i),
        }).collect();

        let params: Vec<_> = try!(self.param_names.iter().zip(self.mir().arg_decls.iter()).map(|(name, arg)| -> TransResult {
            Ok(format!("({} : {})", name, try!(self.transpile_ty(&arg.ty))))
        }).collect());

        let mut comp = Component::new(self, START_BLOCK, self.mir().all_basic_blocks(), None);
        let body = try!(self.transpile_basic_block(START_BLOCK, &mut comp));

        let trait_predicates = if suppress_type_predicates {
            let predicates = self.tcx.lookup_predicates(self.def_id()).predicates;
            predicates.get_slice(ParamSpace::SelfSpace).iter().chain(predicates.get_slice(ParamSpace::FnSpace)).filter_map(|pred| match pred {
                &ty::Predicate::Trait(ref trait_pred) => Some(trait_pred.skip_binder().clone()),
                _ => None
            }).collect_vec()
        } else {
            self.trait_predicates_without_markers(self.def_id()).collect_vec()
        };

        let ty_params = ty_params.iter().map(|p| format!("{} : Type", p.name));
        let ty_params = if suppress_type_predicates {
            iter::once("(Self : Type)".to_owned()).chain(ty_params.map(|p| format!("({})", p))).collect_vec()
        } else {
            ty_params.map(|p| format!("{{{}}}", p)).collect_vec()
        };
        let assoc_ty_substs = try!(self.get_assoc_ty_substs(self.def_id()));
        let trait_params = try!(trait_predicates.into_iter().map(|trait_pred| -> Result<_, String> {
            let free_assoc_tys = self.transpile_trait_ref_assoc_tys(trait_pred.trait_ref, &assoc_ty_substs).1;
            let free_assoc_tys = free_assoc_tys.into_iter().map(|ty| format!("({} : Type)", ty));
            let trait_param = format!("[{}]", try!(self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs)));
            Ok(free_assoc_tys.chain(iter::once(trait_param)))
        }).collect_results()).flat_map(|x| x);
        self.static_params = ty_params.into_iter().chain(trait_params).collect();

        let idx = self.deps.borrow_mut().get_def_idx(self.node_id);
        let is_rec = self.deps.borrow().graph.neighbors_directed(idx, petgraph::EdgeDirection::Incoming).any(|idx2| idx2 == idx);
        let body = if is_rec {
            format!("fix_opt (λ{}, {})", name, body)
        } else { body };
        let def = format!("noncomputable definition {} :=\n{}",
                          iter::once(name).chain(self.static_params.clone()).chain(params).join(" "),
                          body);
        Ok(comp.prelude.into_iter().chain(iter::once(def)).join("\n\n"))
    }

    fn transpile_generic_ty_def(name: &str, generics: &hir::Generics) -> String {
        iter::once(name.to_owned()).chain(generics.ty_params.iter().map(|p| format!("({} : Type)", p.name))).join(" ")
    }

    fn transpile_struct(&self, name: &str, data: &hir::VariantData, generics: &hir::Generics) -> TransResult {
        match *data {
            hir::VariantData::Struct(ref fields, _) => {
                let fields = try!(fields.iter().map(|f| -> TransResult {
                    Ok(format!("({} : {})", mk_lean_name(&f.name.as_str()), try!(self.transpile_hir_ty(&*f.ty))))
                }).join_results("\n"));
                Ok(format!("structure {} := mk {{}} ::\n{}",
                           Transpiler::transpile_generic_ty_def(name, generics),
                           fields))
            }
            hir::VariantData::Tuple(ref fields, _) => {
                let fields = try!(fields.iter().map(|f| {
                    self.transpile_hir_ty(&*f.ty)
                }).join_results(" × "));
                Ok(format!("inductive {} :=\nmk {{}} : {}",
                           Transpiler::transpile_generic_ty_def(name, generics),
                           fields))
            }
            _ => throw!("unimplemented: struct {:?}", data)
        }
    }

    fn transpile_enum(&self, name: &str, def: &hir::EnumDef, generics: &hir::Generics) -> TransResult {
        let applied_ty = iter::once(name.to_owned()).chain(generics.ty_params.map(|p| p.name.as_str().to_string())).join(" ");
        let variants = def.variants.iter().map(|variant| {
            Ok(match variant.node.data {
                hir::VariantData::Unit(_) =>
                    format!("| {} {{}} : {}", variant.node.name, applied_ty),
                hir::VariantData::Tuple(ref fields, _) => {
                    let fields = try!(fields.iter().map(|f| {
                        self.transpile_hir_ty(&*f.ty)
                    }).collect_results());
                    let ty = fields.chain(iter::once(applied_ty.clone())).join(" → ");
                    format!("| {} : {}", variant.node.name, ty)
                }
                ref data => throw!("unimplemented: enum variant {:?}", data)
            })
        });
        Ok(format!("inductive {} :=\n{}",
                   Transpiler::transpile_generic_ty_def(name, generics),
                   try!(variants.join_results("\n"))))
    }

    fn transpile_associated_types(&self, def_id: DefId) -> Result<Vec<String>, String> {
        self.trait_predicates_without_markers(def_id).map(|trait_pred| {
            let trait_def = self.tcx.lookup_trait_def(trait_pred.def_id());
            trait_def.associated_type_names.iter().map(|name| {
                Ok(format!("({} : Type)", try!(self.transpile_associated_type(trait_pred.trait_ref, &name))))
            }).collect_results()
        }).collect_results().map(|tys| tys.flat_map(|x| x).collect::<Vec<_>>())
    }

    fn transpile_trait(&self, trait_def_id: DefId, generics: &hir::Generics, items: &[hir::TraitItem]) -> TransResult {
        let trait_name = self.transpile_def_id(trait_def_id);

        let assoc_ty_substs = try!(self.get_assoc_ty_substs(self.def_id()));
        let supertraits = try!(
            self.trait_predicates_without_markers(trait_def_id)
            .filter(|trait_pred| trait_pred.def_id() != trait_def_id)
            .map(|trait_pred| self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs))
            .collect::<Result<Vec<_>, _>>());
        let extends = if supertraits.is_empty() { "".to_owned() } else {
            format!(" extends {}", supertraits.into_iter().join(", "))
        };

        let items = try!(items.into_iter().filter(|item| match item.node {
            hir::TraitItem_::TypeTraitItem(..) => false,
            // FIXME: Do something more clever than ignoring default method overrides
            hir::TraitItem_::MethodTraitItem(_, Some(_)) => false,
            _ => true
        })
        .map(|item| match item.node {
            hir::TraitItem_::TypeTraitItem(..) =>
                unreachable!(),
            hir::TraitItem_::MethodTraitItem(_, _) => {
                let ty = try!(self.transpile_ty(self.tcx.node_id_to_type(item.id)));
                Ok(format!("({} : {})", item.name, ty))
            }
            hir::TraitItem_::ConstTraitItem(..) =>
                throw!("unimplemented: const trait items"),
        }).collect_results()).collect_vec();
        Ok(format!("structure {} (Self : Type) {}{} {}",
                   Transpiler::transpile_generic_ty_def(
                       &format!("{} [class]", trait_name),
                       generics),
                   try!(self.transpile_associated_types(trait_def_id)).join(" "),
                   extends,
                   if items.is_empty() { "".to_owned() }
                   else { format!(":= mk () ::\n{}", items.join("\n")) }))
    }

    fn transpile_trait_impl(&self, generics: &hir::Generics, items: &[hir::ImplItem]) -> TransResult {
        let trait_ref = self.tcx.impl_trait_ref(self.def_id()).unwrap();

        let mut assoc_ty_substs = try!(self.get_assoc_ty_substs(self.def_id()));
        for item in items {
            if let hir::ImplItemKind::Type(ref ty) = item.node {
                assoc_ty_substs.insert(try!(self.transpile_associated_type(trait_ref, &item.name)), try!(self.transpile_hir_ty(ty)));
            }
        }
        let mut trait_params = try!(self.trait_predicates_without_markers(self.def_id()).map(|trait_pred| -> TransResult {
                Ok(format!(" [{}]", try!(self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs))))
        }).collect_results());

        let supertraits = try!(self.trait_predicates_without_markers(trait_ref.def_id).map(|p| p.subst(self.tcx, trait_ref.substs)).map(|trait_pred| -> Result<_, String> {
            if trait_pred.def_id() == trait_ref.def_id {
                return Ok(None);
            }
            // explicit dependency edge
            try!(self.infer_trait_impl(trait_pred.trait_ref, self.def_id(), true));
            Ok(Some(format!("(_ : {})", try!(self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs)))))
        }).collect_results()).filter_map(|x| x);

        let methods = try!(items.iter().map(|item| Ok(match item.node {
            hir::ImplItemKind::Type(_) =>
                None,
            hir::ImplItemKind::Method(..) => {
                // FIXME: Do something more clever than ignoring default method overrides
                if self.tcx.provided_trait_methods(trait_ref.def_id).iter().any(|m| m.name == item.name) {
                    None
                } else {
                    Some(format!("{} := {}", item.name, self.transpile_node_id(item.id)))
                }
            }
            hir::ImplItemKind::Const(..) =>
                throw!("unimplemented: associated const"),
        })).collect_results()).filter_map(|x| x);

        Ok(format!("noncomputable definition {}{} := ⦃\n  {}\n⦄",
                   Transpiler::transpile_generic_ty_def(
                       &format!("{} [instance]", &self.transpile_node_id(self.node_id)),
                       generics),
                   trait_params.join(""),
                   iter::once(try!(self.transpile_trait_ref(trait_ref, &assoc_ty_substs))).chain(supertraits).chain(methods).join(",\n  ")))
    }

    fn transpile_method(&mut self, node_id: NodeId, type_generics: &hir::Generics, sig: &hir::MethodSig, provided_method: bool) -> TransResult {
        self.node_id = node_id;
        let name = transpile_def_id(self.tcx, self.def_id());
        let ty_params = type_generics.ty_params.iter().chain(sig.generics.ty_params.iter()).collect();
        self.transpile_fn(name, &*sig.decl, ty_params, provided_method)
    }

    fn transpile_item(&mut self, item: &hir::Item) -> TransResult {
        self.node_id = item.id;
        let name = transpile_def_id(&self.tcx, self.def_id());
        Ok(match item.node {
            Item_::ItemFn(ref decl, _, _, _, ref generics, _) =>
                try!(self.transpile_fn(name, decl, generics.ty_params.iter().collect(), false)),
            Item_::ItemImpl(_, _, ref generics, ref base_trait, _, ref items) => {
                for ii in items {
                    if let hir::ImplItemKind::Method(ref sig, _) = ii.node {
                        self.deps.borrow_mut().get_def_idx(ii.id);
                        let res = self.transpile_method(ii.id, generics, sig, false);
                        self.trans_results.insert(ii.id, res);
                    }
                }

                self.node_id = item.id;
                match base_trait {
                    &Some(ref base_trait) if !self.is_marker_trait(self.tcx.trait_ref_to_def_id(base_trait)) =>
                        try!(self.transpile_trait_impl(generics, items)),
                    _ => "".to_string(),
                }
            }
            Item_::ItemStruct(ref data, ref generics) =>
                try!(self.transpile_struct(&name, data, generics)),
            Item_::ItemEnum(ref def, ref generics) =>
                try!(self.transpile_enum(&name, def, generics)),
            Item_::ItemTrait(_, ref generics, _, ref items) => {
                for trait_item in items {
                    if let hir::TraitItem_::MethodTraitItem(ref sig, Some(_)) = trait_item.node {
                        self.deps.borrow_mut().get_def_idx(trait_item.id);
                        let res = self.transpile_method(trait_item.id, generics, sig, true);
                        self.trans_results.insert(trait_item.id, res);
                    }
                }

                self.node_id = item.id;
                if self.is_marker_trait(self.def_id()) { "".to_string() } else {
                    try!(self.transpile_trait(self.def_id(), generics, items))
                }
            }
            Item_::ItemUse(..) | Item_::ItemMod(..) | Item_::ItemExternCrate(_) => "".to_string(),
            _ => throw!("unimplemented item type: {:?}", name),
        })
    }
}

impl<'a, 'tcx> intravisit::Visitor<'a> for Transpiler<'a, 'tcx> {
    fn visit_item(&mut self, item: &'a hir::Item) {
        self.deps.borrow_mut().get_def_idx(item.id);
        let res = self.transpile_item(item);
        self.trans_results.insert(item.id, res);
    }
}

fn transpile_crate(state: &driver::CompileState, targets: Option<&Vec<String>>) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    let crate_name = state.crate_name.expect("missing --crate-name rust arg");
    let base = path::Path::new("thys").join(crate_name);
    try!(std::fs::create_dir_all(&base));

    let mut trans = Transpiler {
        tcx: tcx,
        mir_map: &state.mir_map.unwrap(),
        trans_results: HashMap::new(),
        deps: RefCell::new(Deps {
            crate_deps: HashSet::new(),
            def_idcs: HashMap::new(),
            graph: Graph::new(),
        }),
        node_id: 0,
        param_names: Vec::new(),
        static_params: Vec::new(),
        refs: RefCell::new(HashMap::new()),
    };
    println!("Transpiling...");
    state.hir_crate.unwrap().visit_all_items(&mut trans);

    let Transpiler { deps, trans_results, .. } = trans;
    let Deps { crate_deps, graph, .. } = deps.into_inner();

    let mut crate_deps = crate_deps.into_iter().map(|c| format!("{}.export", c)).collect_vec();
    crate_deps.sort();
    let has_pre = base.join("pre.lean").exists();
    if has_pre {
        crate_deps.insert(0, format!("{}.pre", crate_name));
    }

    let mut f = try!(File::create(base.join("export.lean")));
    for dep in crate_deps {
        try!(write!(f, "import {}\n", dep));
    }
    try!(write!(f, "
open classical
open nat
open option
open prod.ops

namespace {}
", crate_name));
    if has_pre {
        try!(write!(f, "open {}\n", crate_name));
    }
    try!(write!(f, "\n"));

    let targets: Option<HashSet<NodeId>> = targets.map(|targets| {
        let targets = graph.node_indices().filter(|&ni| {
            let name = transpile_node_id(tcx, graph[ni]);
            targets.iter().any(|t| t == &name)
        });
        let rev = petgraph::visit::Reversed(&graph);
        targets.flat_map(|ni| petgraph::visit::DfsIter::new(&rev, ni)).map(|ni| graph[ni]).collect()
    });

    //try!(write!(try!(File::create("deps-un.dot")), "{:?}", petgraph::dot::Dot::new(&graph.map(|_, nid| tcx.map.local_def_id(*nid), |_, e| e))));
    let condensed = condensation(graph, false);
    //try!(write!(try!(File::create("deps.dot")), "{:?}", petgraph::dot::Dot::new(&condensed.map(|_, comp| comp.iter().map(|nid| tcx.map.local_def_id(*nid)).collect_vec(), |_, e| e))));
    let mut failed = HashSet::new();

    let ignored: HashSet<_> = vec![
        "mem.swap",
    ].into_iter().collect();

    for idx in toposort(&condensed) {
        match &condensed[idx][..] {
            [node_id] => {
                if let Some(ref targets) = targets {
                    if !targets.contains(&node_id) {
                        continue
                    }
                }

                let name = transpile_node_id(tcx, node_id);
                if ignored.contains(&name as &str) {
                    continue;
                }

                let failed_deps = condensed.neighbors_directed(idx, petgraph::EdgeDirection::Incoming).filter(|idx| failed.contains(idx)).collect_vec();
                if failed_deps.is_empty() {
                    match trans_results.get(&node_id) {
                        Some(&Ok(ref trans)) => {
                            if !trans.is_empty() {
                                try!(write!(f, "{}\n\n", trans));
                            }
                        }
                        Some(&Err(ref err)) => {
                            failed.insert(idx);
                            try!(write!(f, "/- {}: {} -/\n\n", name, err.replace("/-", "/ -")))
                        }
                        None => {}
                    }
                } else {
                    failed.insert(idx);
                    try!(write!(f, "/- {}: failed dependencies {} -/\n\n", name, failed_deps.into_iter().flat_map(|idx| &condensed[idx]).map(|&node_id| {
                        transpile_node_id(tcx, node_id)
                    }).join(", ")));
                }
            }
            component => {
                let succeeded = component.iter().filter_map(|node_id| trans_results.get(node_id).and_then(|trans| trans.as_ref().ok())).collect_vec();
                if succeeded.len() == component.len() {
                    if succeeded.iter().all(|trans| trans.starts_with("inductive")) {
                        try!(write!(f, "inductive {}\n\n", succeeded.iter().map(|trans| trans.trim_left_matches("inductive")).join("\n\nwith")));
                        continue;
                    }
                }
                failed.insert(idx);
                try!(write!(f, "/- unimplemented: circular dependencies: {}\n\n", component.iter().map(|&node_id| {
                    transpile_node_id(tcx, node_id)
                }).join(", ")));
                for &node_id in component {
                    let name = transpile_node_id(tcx, node_id);
                    match trans_results.get(&node_id) {
                        Some(&Ok(ref trans)) => {
                            try!(write!(f, "{}\n\n", trans));
                        }
                        Some(&Err(ref err)) => {
                            try!(write!(f, "{}: {}", name, err.replace("/-", "/ -")))
                        }
                        None => {}
                    }
                }
                try!(write!(f, "-/\n\n"))
            }
        }
    }

    write!(f, "end {}", crate_name)
}
