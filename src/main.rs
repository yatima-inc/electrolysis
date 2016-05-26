#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(recover, slice_patterns, advanced_slice_patterns)]

extern crate itertools;
extern crate petgraph;
extern crate toml;

#[macro_use]
extern crate rustc;
extern crate rustc_const_eval;
extern crate rustc_driver;
extern crate rustc_front;
extern crate rustc_metadata;
extern crate rustc_mir;
extern crate syntax;

mod component;
mod item_path;
mod mir_graph;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::io;
use std::io::prelude::*;
use std::iter;
use std::fs::File;
use std::path;

use itertools::Itertools;
use petgraph::graph::{self, Graph};
use petgraph::algo::*;

use syntax::ast::{self, NodeId};
use rustc_front::hir::{self, FnDecl, PatKind};
use rustc_front::intravisit;
use rustc::front;
use rustc::front::map::definitions::DefPathData;
use rustc::mir::mir_map::MirMap;
use rustc::mir::repr::*;
use rustc::middle::cstore::CrateStore;
use rustc::middle::const_eval::ConstVal;
use rustc::middle::def_id::{DefId, DefIndex};
use rustc::middle::subst::{ParamSpace, Subst, Substs};
use rustc::middle::traits::*;
use rustc::middle::ty::{self, Ty, TyCtxt};

use rustc_driver::driver;
use syntax::diagnostics;
use rustc::session;

use item_path::item_path_str;
use component::Component;

fn main() {
    let crate_name = match &std::env::args().collect_vec()[..] {
        [_, ref crate_name] => crate_name.clone(),
        _ => panic!("Expected crate name as single cmdline argument"),
    };
    let sysroot = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap()
        .stdout;
    let sysroot = path::PathBuf::from(String::from_utf8(sysroot).unwrap().trim());

    let mut config = String::new();
    let mut config_file = File::open(path::Path::new("thys").join(&crate_name).join("config.toml")).unwrap();
    config_file.read_to_string(&mut config).unwrap();
    let config: toml::Value = config.parse().unwrap();

    let rustc_args = config.lookup("rustc_args").expect("Missing config item 'rustc_args'");
    let rustc_args = iter::once("rustc").chain(rustc_args.as_str().unwrap().split(" ")).map(|s| s.to_string());
    let rustc_matches = rustc_driver::handle_options(rustc_args.collect()).expect("error parsing rustc args");
    let mut options = session::config::build_session_options(&rustc_matches);
    options.crate_name = Some(crate_name);
    options.maybe_sysroot = Some(sysroot);
    let input = match &rustc_matches.free[..] {
        [ref file] => path::PathBuf::from(file),
        _ => panic!("expected input file"),
    };

    let cstore = std::rc::Rc::new(rustc_metadata::cstore::CStore::new(syntax::parse::token::get_ident_interner()));
    let sess = session::build_session(options, Some(input.clone()),
        diagnostics::registry::Registry::new(&rustc::DIAGNOSTICS),
        cstore.clone()
    );
    let rustc_cfg = session::config::build_configuration(&sess);
    println!("Compiling up to MIR...");
    let _ = driver::compile_input(&sess, &cstore, rustc_cfg,
        &session::config::Input::File(input),
        &None, &None, None, &driver::CompileController {
            after_analysis: driver::PhaseController {
                stop: rustc_driver::Compilation::Stop,
                callback: Box::new(|state| {
                    if !sess.has_errors() {
                        transpile_crate(&state, &config).unwrap();
                    }
                }),
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
}

fn toml_value_as_str_array(val: &toml::Value) -> Vec<&str> {
    val.as_slice().unwrap().iter().map(|t| t.as_str().unwrap()).collect()
}

fn mk_lean_name<S : AsRef<str>>(s: S) -> String {
    let s = s.as_ref().replace("::", ".").replace(|c: char| c != '.' && !c.is_alphanumeric(), "_").trim_left_matches('_').to_owned();
    if s == "end" || s.ends_with(".end") || s == "by" || s.ends_with(".by") { s + "_" } else { s }
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
        [ref x] => format!("let {} ← {};\n{}", x, val, cont),
        _ => format!("match {} with ({}) :=\n{}end\n", val, pat.into_iter().join(", "), cont),
    }
}

#[derive(Default)]
struct Deps {
    crate_deps: HashSet<String>,
    def_idcs: HashMap<DefId, graph::NodeIndex>,
    new_deps: HashSet<DefId>,
    graph: Graph<DefId, ()>,
}

impl Deps {
    fn get_def_idx(&mut self, def_id: DefId) -> graph::NodeIndex {
        let Deps { ref mut def_idcs, ref mut new_deps, ref mut graph, .. } = *self;
        *def_idcs.entry(def_id).or_insert_with(|| {
            new_deps.insert(def_id);
            graph.add_node(def_id)
        })
    }

    fn add_dep(&mut self, used: DefId, user: DefId) {
        let from = self.get_def_idx(used);
        let to = self.get_def_idx(user);
        self.graph.add_edge(from, to, ());
    }
}

pub struct Transpiler<'a, 'tcx: 'a> {
    tcx: &'a TyCtxt<'tcx>,
    mir_map: &'a MirMap<'tcx>,
    trans_results: HashMap<DefId, Result<String, String>>,
    deps: RefCell<Deps>,
    config: Config<'a>,

    // inside of fns
    def_id: DefId,
    param_names: Vec<String>,
    prelude: Vec<String>,
    refs: HashMap<usize, &'a Lvalue<'tcx>>,
}

enum TraitImplLookup<'tcx> {
    Static { impl_def_id: DefId, params: Vec<String>, substs: Substs<'tcx> },
    Dynamic { param: String },
}

impl<'tcx> TraitImplLookup<'tcx> {
    fn to_string<'a>(self, trans: &Transpiler<'a, 'tcx>) -> String {
        match self {
            TraitImplLookup::Static { impl_def_id, params, substs } =>
                format!("({})", iter::once(trans.name_def_id(impl_def_id)).chain(substs.types.iter().map(|ty| {
                    trans.transpile_ty(ty)
                })).chain(params).join(" ")),
            TraitImplLookup::Dynamic { param } => param,
        }
    }
}

fn name_def_id(tcx: &TyCtxt, did: DefId) -> String {
    mk_lean_name(item_path_str(tcx, did))
}

impl<'a, 'tcx> Transpiler<'a, 'tcx> {
    fn add_dep(&self, def_id: DefId) {
        if def_id.is_local() {
            self.deps.borrow_mut().add_dep(def_id, self.def_id);
        } else {
            let crate_name = self.tcx.sess.cstore.crate_name(def_id.krate);
            self.deps.borrow_mut().crate_deps.insert(crate_name.to_string());
        }
    }

    fn name_def_id(&self, did: DefId) -> String {
        self.add_dep(did);
        name_def_id(self.tcx, did)
    }

    fn name(&self) -> String { name_def_id(self.tcx, self.def_id) }

    fn transpile_trait_ref_args(&self, trait_ref: ty::TraitRef<'tcx>) -> Vec<String> {
        trait_ref.substs.types.iter().map(|ty| {
            self.transpile_ty(ty)
        }).collect()
    }

    fn transpile_associated_type(&self, _trait_ref: ty::TraitRef<'tcx>, name: &ast::Name) -> String {
        //let prefix = self.name_def_id(trait_ref.def_id);
        format!("{}", name) //_{}", prefix, name)
    }

    fn get_assoc_ty_substs(&self, def_id: DefId) -> HashMap<String, String> {
        self.tcx.lookup_predicates(def_id).predicates.into_iter().filter_map(|trait_pred| match trait_pred {
            ty::Predicate::Projection(ty::Binder(proj_pred)) => {
                let assoc_ty = self.transpile_associated_type(proj_pred.projection_ty.trait_ref, &proj_pred.projection_ty.item_name);
                Some((assoc_ty, self.transpile_ty(&proj_pred.ty)))
            }
            _ => None,
        }).collect()
    }

    fn transpile_trait_ref_assoc_tys(&self, trait_ref: ty::TraitRef<'tcx>, assoc_ty_substs: &HashMap<String, String>) -> (Vec<String>, Vec<String>) {
        let mut free_assoc_tys = vec![];
        let assoc_tys = self.trait_predicates_without_markers(trait_ref.def_id).flat_map(|trait_pred| {
            let trait_def = self.tcx.lookup_trait_def(trait_pred.def_id());
            trait_def.associated_type_names.iter().map(|name| {
                let assoc_ty = self.transpile_associated_type(trait_pred.trait_ref, name);
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

    fn transpile_trait_ref_no_assoc_tys(&self, trait_ref: ty::TraitRef<'tcx>) -> String {
        iter::once(self.name_def_id(trait_ref.def_id)).chain(self.transpile_trait_ref_args(trait_ref)).join(" ")
    }

    fn transpile_trait_ref(&self, trait_ref: ty::TraitRef<'tcx>, assoc_ty_substs: &HashMap<String, String>) -> String {
        let associated_types = self.transpile_trait_ref_assoc_tys(trait_ref, assoc_ty_substs).0;
        iter::once(self.transpile_trait_ref_no_assoc_tys(trait_ref)).chain(associated_types).join(" ")
    }

    fn transpile_ty(&self, ty: Ty<'tcx>) -> String {
        match ty.sty {
            ty::TypeVariants::TyBool => "Prop".to_string(),
            ty::TypeVariants::TyUint(ref ty) => ty.to_string(),
            ty::TypeVariants::TyInt(ref ty) => ty.to_string(),
            //ty::TypeVariants::TyFloat(ref ty) => ty.to_string(),
            ty::TypeVariants::TyTuple(ref tys) => match &tys[..] {
                [] => "unit".to_string(),
                _ => format!("({})", tys.iter().map(|ty| self.transpile_ty(ty)).join(" × ")),
            },
            ty::TypeVariants::TyFnDef(_, _, ref data) | ty::TypeVariants::TyFnPtr(ref data) => {
                let sig = data.sig.skip_binder();
                let muts = sig.inputs.iter().filter_map(|ty| try_unwrap_mut_ref(ty));
                let inputs = sig.inputs.iter().map(|ty| self.transpile_ty(ty));
                let mut outputs = match sig.output {
                    ty::FnOutput::FnConverging(out_ty) => iter::once(out_ty).chain(muts).map(|ty| self.transpile_ty(ty)),
                    ty::FnOutput::FnDiverging => panic!("unimplemented: diverging function"),
                };
                inputs.chain(iter::once(format!("option ({})", outputs.join(" × ")))).join(" → ")
            },
            ty::TypeVariants::TyStruct(ref adt_def, ref substs) |
            ty::TypeVariants::TyEnum(ref adt_def, ref substs) => format!("({})", format_generic_ty(
                &self.name_def_id(adt_def.did),
                substs.types.iter().map(|ty| self.transpile_ty(ty))
            )),
            ty::TypeVariants::TyRef(_, ref data) => self.transpile_ty(data.ty),
            ty::TypeVariants::TyParam(ref param) => param.name.to_string(),
            ty::TypeVariants::TyProjection(ref proj) => self.transpile_associated_type(proj.trait_ref, &proj.item_name),
            ty::TypeVariants::TySlice(ref ty) => format!("(slice {})", self.transpile_ty(ty)),
            ty::TypeVariants::TyTrait(_) => panic!("unimplemented: trait objects"),
            ty::TypeVariants::TyInfer(_) => "_".to_string(), // FIXME
            _ => match ty.ty_to_def_id() {
                Some(did) => self.name_def_id(did),
                None => panic!("unimplemented: ty {:?}", ty),
            }
        }
    }

    fn trait_predicates(&self, def_id: DefId) -> std::vec::IntoIter<ty::TraitPredicate<'tcx>> {
        let mut predicates = self.tcx.lookup_predicates(def_id).predicates;
        if self.tcx.trait_of_item(def_id).is_some() {
            predicates.truncate(ParamSpace::TypeSpace, 0);
        }
        predicates.into_iter().filter_map(|trait_pred| match trait_pred {
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

    fn trait_predicates_without_markers(&self, def_id: DefId) -> std::vec::IntoIter<ty::TraitPredicate<'tcx>> {
        self.trait_predicates(def_id).filter(|trait_pred| !self.is_marker_trait(trait_pred.def_id())).collect_vec().into_iter()
    }

    fn node_id(&self) -> NodeId {
        self.tcx.map.as_local_node_id(self.def_id).unwrap()
    }

    fn mir(&self) -> &'a Mir<'tcx> {
        &self.mir_map.map[&self.node_id()]
    }

    fn local_name(&self, lv: &Lvalue) -> String {
        match *lv {
            Lvalue::Var(idx) => mk_lean_name(&*self.mir().var_decls[idx as usize].name.as_str()),
            Lvalue::Temp(idx) => format!("t{}", idx),
            Lvalue::Arg(idx) => self.param_names[idx as usize].clone(),
            Lvalue::ReturnPointer => "ret".to_string(),
            _ => panic!("not a local: {:?}", lv),
        }
    }

    fn deref_mut(&self, lv: &Lvalue) -> Option<&Lvalue<'tcx>> {
        if let Some(lv_idx) = self.lvalue_idx(lv) {
            if let Some(lv) = self.refs.get(&lv_idx) {
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
            Lvalue::Static(did) => self.name_def_id(did),
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

    fn get_lvalue(&self, lv: &Lvalue<'tcx>) -> String {
        if let Some(lv) = self.deref_mut(lv) {
            return self.get_lvalue(lv)
        }
        if let Some(name) = self.lvalue_name(lv) {
            return name
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
                format!("{}_{}", self.get_lvalue(base), field.index()),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(ref field, _) }) =>
                match unwrap_refs(self.lvalue_ty(base)).sty {
                    ty::TypeVariants::TyTuple(ref tys) =>
                        get_tuple_elem(self.get_lvalue(base), field.index(), tys.len()),
                    ty::TypeVariants::TyStruct(ref adt_def, _) => {
                        if adt_def.struct_variant().is_tuple_struct() {
                            format!("match {} with {} x := x end",
                                    get_tuple_elem(self.get_lvalue(base), field.index(), adt_def.struct_variant().fields.len()),
                                    self.name_def_id(adt_def.did))
                        } else {
                            format!("({}.{} {})",
                                    self.name_def_id(adt_def.did),
                                    mk_lean_name(&*adt_def.struct_variant().fields[field.index()].name.as_str()),
                                    self.get_lvalue(base))
                        }
                    }
                    ref ty => panic!("unimplemented: accessing field of {:?}", ty),
                },
            _ => panic!("unimplemented: loading {:?}", lv),
        }
    }

    fn lvalue_ty(&self, lv: &Lvalue<'tcx>) -> Ty<'tcx> {
        self.mir().lvalue_ty(self.tcx, lv).to_ty(self.tcx)
    }

    fn lvalue_idx(&self, lv: &Lvalue) -> Option<usize> {
        match *lv {
            Lvalue::Var(idx) => Some(idx as usize),
            Lvalue::Temp(idx) => Some(self.mir().var_decls.len() + idx as usize),
            Lvalue::ReturnPointer => Some(self.num_locals() - 1),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.lvalue_idx(base),
            _ => None,
        }
    }

    fn set_lvalue(&self, lv: &Lvalue<'tcx>, val: &str) -> String {
        if let Some(lv) = self.deref_mut(lv) {
            return self.set_lvalue(lv, val)
        }
        if let Some(name) = self.lvalue_name(lv) {
            return format!("let {} ← {};\n", name, val)
        }
        match *lv {
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.set_lvalue(base, val),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(ref field, _) }) => {
                let base_name = self.lvalue_name(base).ok_or_else(|| format!("ugh, nested fields assignments? {:?}", lv)).unwrap();
                match unwrap_refs(self.lvalue_ty(base)).sty {
                    ty::TypeVariants::TyStruct(ref adt_def, _) => {
                        let field_name = adt_def.struct_variant().fields[field.index()].name;
                        format!("let {} ← ⦃ {}, {} := {}, {} ⦄;\n", base_name, self.name_def_id(adt_def.did), field_name, val, base_name)
                    },
                    ref ty => panic!("unimplemented: setting field of {:?}", ty),
                }
            }
            _ => panic!("unimplemented: setting lvalue {:?}", lv),
        }
    }

    fn set_lvalues_option<'b>(&self, lvs: Vec<&'b Lvalue<'tcx>>, val: &str, cont: &str) -> String {
        let (direct_dests, indirect_dests): (Vec<_>, Vec<_>) = lvs.into_iter().map(|lv| {
            match self.lvalue_name(lv) {
                Some(name) => (name, None),
                None => (self.local_name(lv), Some(self.set_lvalue(self.deref_mut(lv).unwrap(), &self.local_name(lv))))
            }
        }).unzip();
        let indirect_dests = indirect_dests.into_iter().filter_map(|x| x).join("");
        format!("do tmp__ ← {};\n{}", val,
                detuplize("tmp__", &direct_dests[..], &(indirect_dests + cont)))
    }

    fn transpile_constval(&self, val: &ConstVal) -> String {
        match *val {
            ConstVal::Bool(b) => b.to_string(),
            ConstVal::Integral(i) => match i.int_type().unwrap() {
                syntax::attr::IntType::SignedInt(_) =>
                    format!("({} : int)", i.to_u64_unchecked() as i64),
                syntax::attr::IntType::UnsignedInt(_) =>
                    format!("({} : nat)", i.to_u64_unchecked()),
            },
            ConstVal::Str(ref s) => format!("\"{}\"", s),
            _ => panic!("unimplemented: literal {:?}", val),
        }
    }

    fn transpile_constant(&self, c: &Constant) -> String {
        match c.literal {
            Literal::Value { ref value } => self.transpile_constval(value),
            _ => panic!("unimplemented: constant {:?}", c),
        }
    }

    fn get_operand(&self, op: &Operand<'tcx>) -> String {
        match *op {
            Operand::Consume(ref lv) => self.get_lvalue(lv),
            Operand::Constant(ref c) => self.transpile_constant(c),
        }
    }

    fn get_rvalue(&self, rv: &Rvalue<'tcx>) -> MaybeValue {
        MaybeValue::total(match *rv {
            Rvalue::Use(Operand::Consume(Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Index(ref idx) }))) =>
                return MaybeValue::partial(format!("slice._T_.slice_SliceExt.get_unchecked {} {}", self.get_lvalue(base), self.get_operand(idx))),
            Rvalue::Use(ref op) => self.get_operand(op),
            Rvalue::UnaryOp(op, ref operand) =>
                format!("{} {}", match op {
                    UnOp::Not if self.mir().operand_ty(self.tcx, operand).is_bool() => "bool.bnot",
                    UnOp::Not => "NOT",
                    UnOp::Neg => "-",
                }, self.get_operand(operand)),
            Rvalue::BinaryOp(op, ref o1, ref o2) => {
                let (so1, so2) = (self.get_operand(o1), self.get_operand(o2));
                return match op {
                    BinOp::Sub if !self.mir().operand_ty(self.tcx, o1).is_signed() => MaybeValue::partial(format!("{} {} {}", "checked.sub", so1, so2)),
                    BinOp::Div => MaybeValue::partial(format!("{} {} {}", "checked.div", so1, so2)),
                    BinOp::Rem => MaybeValue::partial(format!("{} {} {}", "checked.mod", so1, so2)),
                    BinOp::Shl => MaybeValue::partial(format!("{} {} {}", "checked.shl", so1, so2)),
                    BinOp::Shr => MaybeValue::partial(format!("{} {} {}", "checked.shr", so1, so2)),
                    _ => MaybeValue::total(format!("{} {} {}", so1, match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        BinOp::Mul => "*",
                        BinOp::Eq => "=",
                        BinOp::Lt => "<",
                        BinOp::Le => "<=",
                        BinOp::Ne => "≠",
                        BinOp::Ge => ">=",
                        BinOp::Gt => ">",
                        _ => panic!("unimplemented: operator {:?}", op),
                    }, so2))
                }
            }
            Rvalue::Cast(CastKind::Misc, ref op, ref ty) if self.mir().operand_ty(self.tcx, op).is_integral() && ty.is_integral() => {
                format!("({}.of_num {})",
                        if ty.is_signed() { "int" } else { "nat" },
                        self.get_operand(op))
            }
            Rvalue::Ref(_, BorrowKind::Shared, ref lv) =>
                return self.get_rvalue(&Rvalue::Use(Operand::Consume(lv.clone()))),
            Rvalue::Aggregate(AggregateKind::Tuple, ref ops) => {
                let mut ops = ops.iter().map(|op| self.get_operand(op));
                format!("({})", ops.join(", "))
            }
            Rvalue::Aggregate(AggregateKind::Adt(ref adt_def, variant_idx, _), ref ops) => {
                self.add_dep(adt_def.did);

                let variant = &adt_def.variants[variant_idx];
                let mut ops = ops.iter().map(|op| self.get_operand(op));
                format!("{}{} {}",
                        self.name_def_id(variant.did),
                        if adt_def.adt_kind() == ty::AdtKind::Struct && !adt_def.struct_variant().is_tuple_struct() { ".mk" } else { "" },
                        ops.join(" "))
            }
            Rvalue::Aggregate(AggregateKind::Closure(def_id, _), ref ops) => {
                let ops = ops.into_iter().map(|op| self.get_operand(op));
                iter::once(self.name_def_id(def_id)).chain(ops).join(" ")
            }
            Rvalue::Len(ref lv) => format!("list.length {}", self.get_lvalue(lv)),
            _ => panic!("unimplemented: rvalue {:?}", rv),
        })
    }

    fn transpile_statement(&mut self, stmt: &'a Statement<'tcx>) -> String {
        match stmt.kind {
            StatementKind::Assign(ref lv, ref rv) => {
                if let Rvalue::Ref(_, BorrowKind::Mut, ref lsource) = *rv {
                    let idx = self.lvalue_idx(lv).unwrap_or_else(|| {
                        panic!("unimplemented: storing {:?}", lv)
                    });
                    self.refs.insert(idx, lsource);
                    return "".to_string()
                }
                if *lv != Lvalue::ReturnPointer && self.lvalue_ty(lv).is_nil() {
                    // optimization/rustc_mir workaround: don't save '()'
                    return "".to_string()
                }

                match self.get_rvalue(rv) {
                    MaybeValue { val, total: true } => self.set_lvalue(lv, &val),
                    MaybeValue { val, total: false } =>
                        format!("do tmp__ ← {};\n{}", &val, self.set_lvalue(lv, "tmp__")),
                }
            }
        }
    }

    fn transpile_basic_block_rec(&mut self, bb: BasicBlock, comp: &Component) -> String {
        if comp.header == Some(bb) {
            format!("some (inl {})\n", comp.state_val)
        } else if !comp.blocks.contains(&bb) {
            // leaving a loop
            format!("do tmp__ ← {};\nsome (inr tmp__)", self.transpile_basic_block(bb, &comp.outer.unwrap()))
        } else {
            self.transpile_basic_block(bb, comp)
        }
    }

    fn call_return_dests<'b>(&self, call: &'b Terminator<'tcx>) -> Vec<&'b Lvalue<'tcx>> {
        match call {
            &Terminator::Call { ref args, destination: Some((ref lv, _)), .. } => {
                let muts = args.iter().filter_map(|op| match *op {
                    Operand::Consume(ref lv) => try_unwrap_mut_ref(self.lvalue_ty(lv)).map(|_| lv),
                    Operand::Constant(_) => None,
                });
                iter::once(lv).chain(muts).collect()
            }
            _ => vec![],
        }
    }

    fn infer_trait_impl(&self, trait_ref: ty::TraitRef<'tcx>) -> TraitImplLookup<'tcx> {
        use rustc::middle::infer;

        let span = syntax::codemap::DUMMY_SP;
        let param_env = ty::ParameterEnvironment::for_item(self.tcx, self.node_id());
        let pred = ty::Binder(trait_ref).to_poly_trait_predicate().subst(self.tcx, &param_env.free_substs);
        let dbg_param_env = format!("{:?}", param_env.caller_bounds);
        let infcx = infer::new_infer_ctxt(self.tcx, &self.tcx.tables, Some(param_env), ProjectionMode::Any);
        let mut selcx = SelectionContext::new(&infcx);
        let obligation = Obligation::new(ObligationCause::misc(span, ast::DUMMY_NODE_ID), pred);
        let selection = selcx.select(&obligation).unwrap_or_else(|err| {
            panic!("obligation select: {:?} {:?} {:?}", obligation, err, dbg_param_env)
        }).unwrap();

        match selection {
            Vtable::VtableImpl(data) => {
                let nested_traits = data.nested.iter().filter_map(|obl| match obl.predicate {
                    ty::Predicate::Trait(ref trait_pred) if !self.is_marker_trait(trait_pred.skip_binder().def_id()) =>
                        Some(self.infer_trait_impl(trait_pred.skip_binder().trait_ref).to_string(self)),
                    _ => None,
                }).collect();

                let mut fulfill_cx = FulfillmentContext::new();
                for obl in data.nested {
                    fulfill_cx.register_predicate_obligation(&infcx, obl);
                }
                let substs = infer::drain_fulfillment_cx_or_panic(span, &infcx, &mut fulfill_cx, data.substs);

                TraitImplLookup::Static {
                    impl_def_id: data.impl_def_id,
                    params: nested_traits,
                    substs: substs
                }
            },
            Vtable::VtableParam(_) => {
                let param = mk_lean_name(self.transpile_trait_ref_no_assoc_tys(trait_ref)).replace('.', "_");
                TraitImplLookup::Dynamic { param: param }
            }
            Vtable::VtableClosure(_) => {
                TraitImplLookup::Dynamic {
                    param: "_".to_string()
                }
            },
            vtable => panic!("unimplemented: vtable {:?}", vtable),
        }
    }

    fn transpile_basic_block(&mut self, bb: BasicBlock, comp: &Component) -> String {
        macro_rules! rec { ($bb:expr) => { self.transpile_basic_block_rec($bb, comp) } }

        if let Some(l) = comp.loops.clone().into_iter().find(|l| l.contains(&bb)) {
            let mut l_comp = Component::new(self, bb, l, Some(&comp));
            let (defs, _) = Component::defs_uses(comp.blocks.iter().filter(|bb| !l_comp.blocks.contains(bb)), self);
            let (l_defs, l_uses) = Component::defs_uses(l_comp.blocks.iter(), self);
            let nonlocal_uses = self.locals().into_iter().filter(|v| defs.contains(v) && l_uses.contains(v) && !l_defs.contains(v));
            let state_vars = self.locals().into_iter().filter(|v| defs.contains(v) && l_defs.contains(v)).collect_vec();
            l_comp.state_val = format!("({})", state_vars.iter().join(", "));
            let name = format!("{}.loop_{}", self.name(), bb.index());
            let app = iter::once(name).chain(nonlocal_uses).join(" ");
            let body = self.transpile_basic_block(bb, &l_comp);
            self.prelude.push(format!("definition {} state__ :=\n{}", app,
                                      detuplize("state__", &state_vars, &body)));
            return format!("loop' ({}) {}", app, l_comp.state_val);
        }

        let data = self.mir().basic_block_data(bb);
        let stmts = data.statements.iter().map(|s| self.transpile_statement(s)).collect_vec();
        let terminator = match data.terminator {
            Some(ref terminator) => Some(match *terminator {
                Terminator::Goto { target } =>
                    rec!(target),
                Terminator::If { ref cond, targets: (bb_if, bb_else) } =>
                    format!("if {} then\n{} else\n{}", self.get_operand(cond),
                    rec!(bb_if),
                    rec!(bb_else)),
                Terminator::Return => self.return_expr(),
                Terminator::Call { ref func, ref args, destination: Some((_, target)), ..  } => {
                    let call = match *func {
                        Operand::Constant(Constant { literal: Literal::Item { def_id, substs, .. }, .. }) => {
                            let substs = substs.clone();
                            let (def_id, substs) = match self.tcx.trait_of_item(def_id) {
                                Some(trait_def_id) => {
                                    // from trans::meth::trans_method_callee
                                    let trait_ref = substs.to_trait_ref(self.tcx, trait_def_id);

                                    match self.infer_trait_impl(trait_ref) {
                                        TraitImplLookup::Static { impl_def_id, substs: impl_substs, .. }  => {
                                            let method = self.tcx.impl_or_trait_item(def_id).as_opt_method().unwrap();
                                            let trait_def = self.tcx.lookup_trait_def(method.container.id());
                                            let method = trait_def.ancestors(impl_def_id).fn_defs(&self.tcx, method.name).next().unwrap().item;
                                            let impl_substs = impl_substs.with_method_from(&substs);
                                            (method.def_id, if method.container.id() == impl_def_id { impl_substs } else { substs })
                                        }
                                        TraitImplLookup::Dynamic { .. } =>
                                            (def_id, substs)
                                    }
                                }
                                _ => (def_id, substs)
                            };

                            // analogous to transpile_fn

                            // TODO: should probably substitute and make explicit
                            let ty_params = self.tcx.lookup_item_type(def_id).generics.types.iter().map(|_| "_".to_string()).collect_vec();
                            let assoc_ty_substs = self.get_assoc_ty_substs(def_id);
                            let trait_params = self.trait_predicates_without_markers(def_id).flat_map(|trait_pred| {
                                let free_assoc_tys = self.transpile_trait_ref_assoc_tys(trait_pred.trait_ref, &assoc_ty_substs).1;
                                let free_assoc_tys = free_assoc_tys.into_iter().map(|_| "_".to_string());
                                let trait_param = self.infer_trait_impl(trait_pred.trait_ref.subst(self.tcx, &substs)).to_string(self);
                                free_assoc_tys.chain(iter::once(trait_param))
                            });
                            iter::once(format!("@{}", self.name_def_id(def_id))).chain(ty_params).chain(trait_params).join(" ")
                        },
                        Operand::Constant(_) => unreachable!(),
                        Operand::Consume(ref lv) => self.get_lvalue(lv),
                    };
                    let call = iter::once(call).chain(args.iter().map(|op| self.get_operand(op))).join(" ");
                    let rec = rec!(target);
                    self.set_lvalues_option(self.call_return_dests(&terminator), &call, &rec)
                }
                Terminator::Call { destination: None, .. } =>
                    "none\n".to_string(),
                Terminator::Switch { ref discr, ref adt_def, ref targets } => {
                    let value = self.get_lvalue(discr);
                    let mut arms = adt_def.variants.iter().zip(targets).map(|(var, &target)| {
                        let vars = (0..var.fields.len()).into_iter().map(|i| format!("{}_{}", value, i));
                        format!("| {} :=\n{}", iter::once(self.name_def_id(var.did)).chain(vars).join(" "), rec!(target))
                    });
                    format!("match {} with\n{}end\n", value, arms.join(" "))
                },
                Terminator::SwitchInt { ref discr, switch_ty: _, ref values, ref targets } => {
                    let arms = values.iter().zip(targets).map(|(val, &target)| {
                        format!("| {} :=\n{}", self.transpile_constval(val), rec!(target))
                    }).collect_vec();
                    let fallback = format!("| _ :=\n{}", rec!(*targets.last().unwrap()));
                    format!("match {} with\n{}\nend\n", self.get_lvalue(discr),
                            arms.into_iter().chain(iter::once(fallback)).join(""))
                },
                Terminator::Drop { target, .. } => rec!(target),
                Terminator::Resume => String::new(),
            }),
            None => None,
        };
        stmts.into_iter().chain(terminator.into_iter()).join("")
    }

    fn sig(&self) -> &ty::FnSig<'tcx> {
        self.tcx.lookup_item_type(self.def_id).ty.fn_sig().skip_binder()
    }

    fn return_expr(&self) -> String {
        let muts = self.sig().inputs.iter().zip(self.param_names.iter()).filter_map(|(ty, name)| {
            try_unwrap_mut_ref(ty).map(|_| name.clone())
        });
        let ret = if self.sig().output.unwrap().is_nil() { "()" } else { "ret" };
        format!("some ({})\n", iter::once(ret.to_string()).chain(muts).join(", "))
    }

    fn transpile_fn(&mut self, name: String, decl: &FnDecl) -> String {
        // FIXME... or not
        if name.starts_with("tuple._A__B__C__D") {
            return "".to_string()
        }

        self.refs.clear();

        self.param_names = decl.inputs.iter().enumerate().map(|(i, param)| match param.pat.node {
            PatKind::Ident(_, ref ident, _) => mk_lean_name(&ident.node.name.to_string()),
            _ => format!("p{}", i),
        }).collect();

        let params = self.param_names.iter().zip(self.mir().arg_decls.iter()).map(|(name, arg)| {
            format!("({} : {})", name, self.transpile_ty(&arg.ty))
        }).collect_vec();

        let mut comp = Component::new(self, START_BLOCK, self.mir().all_basic_blocks(), None);
        let body = self.transpile_basic_block(START_BLOCK, &mut comp);

        let ty_params = self.tcx.lookup_item_type(self.def_id).generics.types.iter().map(|p| format!("{{{} : Type}}", p.name)).collect_vec();
        let assoc_ty_substs = self.get_assoc_ty_substs(self.def_id);
        let trait_params = self.trait_predicates_without_markers(self.def_id).flat_map(|trait_pred| {
            let free_assoc_tys = self.transpile_trait_ref_assoc_tys(trait_pred.trait_ref, &assoc_ty_substs).1;
            let free_assoc_tys = free_assoc_tys.into_iter().map(|ty| format!("({} : Type)", ty));
            let trait_param = format!("[{} : {}]",
                                      mk_lean_name(self.transpile_trait_ref_no_assoc_tys(trait_pred.trait_ref)).replace('.', "_"),
                                      self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs));
            free_assoc_tys.chain(iter::once(trait_param))
        }).collect_vec();

        let idx = self.deps.borrow_mut().get_def_idx(self.def_id);
        let is_rec = self.deps.borrow().graph.neighbors_directed(idx, petgraph::EdgeDirection::Incoming).any(|idx2| idx2 == idx);
        let body = if is_rec {
            format!("fix_opt (λ{}, {})", name, body)
        } else { body };
        let prelude = self.prelude.drain(..).collect_vec();
        if prelude.is_empty() {
            let def = format!("definition {} :=\n{}",
                              iter::once(name).chain(ty_params).chain(trait_params).chain(params).join(" "),
                              body);
            prelude.into_iter().chain(iter::once(def)).join("\n\n")
        } else {
            format!("section
{}

{}

definition {} :=\n{}
end",
                    vec![ty_params, trait_params, params].into_iter().map(|p| {
                        format!("parameters {}", p.into_iter().join(" "))
                    }).join("\n"),
                    prelude.into_iter().join("\n\n"),
                    iter::once(name).join(" "), body)
        }
    }

    fn as_generic_ty_def(&self, attr: Option<&str>) -> String {
        let name = if let Some(attr) = attr { format!("{} {}", self.name(), attr) } else { self.name() };
        // traits are weird
        let generics = if let front::map::Node::NodeItem(&hir::Item { node: hir::Item_::ItemTrait(..), .. }) =
            self.tcx.map.get(self.node_id()) {
            self.tcx.lookup_trait_def(self.def_id).generics.clone()
        } else {
            self.tcx.lookup_item_type(self.def_id).generics
        };
        iter::once(name).chain(generics.types.iter().map(|p| format!("({} : Type)", p.name))).join(" ")
    }

    fn transpile_struct(&self, variant: ty::VariantDef<'tcx>) -> String {
        match variant.kind {
            ty::VariantKind::Struct => {
                let mut fields = variant.fields.iter().map(|f| {
                    format!("({} : {})", mk_lean_name(&*f.name.as_str()), self.transpile_ty(f.unsubst_ty()))
                });
                format!("structure {} := mk {{}} ::\n{}",
                        self.as_generic_ty_def(None),
                        fields.join("\n"))
            }
            ty::VariantKind::Tuple => {
                let mut fields = variant.fields.iter().map(|f| {
                    self.transpile_ty(f.unsubst_ty())
                });
                format!("inductive {} :=\nmk {{}} : {}",
                        self.as_generic_ty_def(None),
                        fields.join(" × "))
            }
            ty::VariantKind::Unit =>
                format!("structure {} := mk {{}} ::", self.as_generic_ty_def(None)),
        }
    }

    fn transpile_enum(&self, name: &str, adt_def: ty::AdtDef<'tcx>) -> String {
        let generics = adt_def.type_scheme(self.tcx).generics;
        let applied_ty = iter::once(name.to_owned()).chain(generics.types.map(|p| p.name.as_str().to_string())).join(" ");
        let mut variants = adt_def.variants.iter().map(|variant| {
            match variant.kind {
                ty::VariantKind::Unit =>
                    format!("| {} {{}} : {}", variant.name, applied_ty),
                ty::VariantKind::Tuple => {
                    let fields = variant.fields.iter().map(|f| {
                        self.transpile_ty(f.unsubst_ty())
                    });
                    let ty = fields.chain(iter::once(applied_ty.clone())).join(" → ");
                    format!("| {} {{}} : {}", variant.name, ty)
                }
                ref data => panic!("unimplemented: enum variant {:?}", data)
            }
        });
        format!("inductive {} :=\n{}", self.as_generic_ty_def(None), variants.join("\n"))
    }

    fn transpile_associated_types(&self, def_id: DefId) -> Vec<String> {
        self.trait_predicates_without_markers(def_id).flat_map(|trait_pred| {
            let trait_def = self.tcx.lookup_trait_def(trait_pred.def_id());
            trait_def.associated_type_names.iter().map(|name| {
                format!("({} : Type)", self.transpile_associated_type(trait_pred.trait_ref, &name))
            }).collect_vec()
        }).collect()
    }

    fn transpile_trait(&self, name: &str) -> String {
        if self.is_marker_trait(self.def_id) {
            return "".to_string()
        }

        let assoc_ty_substs = self.get_assoc_ty_substs(self.def_id);
        let supertraits = self.trait_predicates_without_markers(self.def_id)
            .filter(|trait_pred| trait_pred.def_id() != self.def_id)
            .map(|trait_pred| self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs))
            .collect_vec();
        let extends = if supertraits.is_empty() { "".to_owned() } else {
            format!(" extends {}", supertraits.into_iter().join(", "))
        };

        let only_path = format!("traits.\"{}\".only", name);
        let only: Option<HashSet<_>> = self.config.config.lookup(&only_path).map(|only| toml_value_as_str_array(only).into_iter().collect());
        let items = self.tcx.trait_items(self.def_id).iter().filter_map(|item| match *item {
            ty::ImplOrTraitItem::TypeTraitItem(_) => None,
            ty::ImplOrTraitItem::MethodTraitItem(ref method) => {
                // FIXME: Do something more clever than ignoring default method overrides
                if self.tcx.provided_trait_methods(self.def_id).iter().any(|m| m.name == method.name) ||
                    only.iter().any(|only| !only.contains(&*method.name.as_str())) {
                    None
                } else {
                    let ty = self.transpile_ty(self.tcx.lookup_item_type(method.def_id).ty);
                    Some(format!("({} : {})", method.name, ty))
                }
            }
            ty::ImplOrTraitItem::ConstTraitItem(_) =>
                panic!("unimplemented: const trait items"),
        }).collect_vec();
        format!("structure {} {}{} {}",
                self.as_generic_ty_def(Some("[class]")),
                self.transpile_associated_types(self.def_id).join(" "),
                extends,
                if items.is_empty() { "".to_owned() }
                else { format!(":= mk () ::\n{}", items.join("\n")) })
    }

    fn transpile_trait_impl(&self) -> String {
        let trait_ref = self.tcx.impl_trait_ref(self.def_id).unwrap();
        if self.is_marker_trait(trait_ref.def_id) {
            return "".to_string()
        }


        let mut assoc_ty_substs = self.get_assoc_ty_substs(self.def_id);
        for item in self.tcx.impl_items.borrow().get(&self.def_id).unwrap() {
            if let ty::ImplOrTraitItem::TypeTraitItem(ref assoc_ty) = self.tcx.impl_or_trait_item(item.def_id()) {
                assoc_ty_substs.insert(self.transpile_associated_type(trait_ref, &assoc_ty.name), self.transpile_ty(assoc_ty.ty.unwrap()));
            }
        }
        let mut trait_params = self.trait_predicates_without_markers(self.def_id).map(|trait_pred| {
                format!(" [{}]", self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs))
        });

        let supertraits = self.trait_predicates_without_markers(trait_ref.def_id).map(|p| p.subst(self.tcx, trait_ref.substs)).filter_map(|trait_pred| {
            if trait_pred.def_id() == trait_ref.def_id {
                return None;
            }
            // explicit dependency edge
            self.infer_trait_impl(trait_pred.trait_ref);
            Some(format!("(_ : {})", self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs)))
        });

        let only_path = format!("traits.\"{}\".only", &self.name_def_id(trait_ref.def_id));
        let only: Option<HashSet<_>> = self.config.config.lookup(&only_path).map(|only| toml_value_as_str_array(only).into_iter().collect());
        let items = self.tcx.impl_items.borrow().get(&self.def_id).unwrap().iter().filter_map(|item| match self.tcx.impl_or_trait_item(item.def_id()) {
            ty::ImplOrTraitItem::TypeTraitItem(_) =>
                None,
            ty::ImplOrTraitItem::MethodTraitItem(ref method) => {
                // FIXME: Do something more clever than ignoring default method overrides
                if self.tcx.provided_trait_methods(trait_ref.def_id).iter().any(|m| m.name == method.name) ||
                    only.iter().any(|only| !only.contains(&*method.name.as_str())) {
                    None
                } else {
                    Some(format!("{} := {}", method.name, self.name_def_id(method.def_id)))
                }
            }
            ty::ImplOrTraitItem::ConstTraitItem(_) =>
                panic!("unimplemented: const trait items"),
        }).collect_vec();

        format!("definition {}{} := ⦃\n  {}\n⦄",
                self.as_generic_ty_def(Some("[instance]")),
                trait_params.join(""),
                iter::once(self.transpile_trait_ref(trait_ref, &assoc_ty_substs)).chain(supertraits).chain(items).join(",\n  "))
    }

    fn transpile_def_id(&mut self, def_id: DefId) {
        self.def_id = def_id;
        let name = self.name();
        match self.tcx.map.def_key(def_id).disambiguated_data.data {
            DefPathData::Impl(_) => {
                if self.tcx.impl_trait_ref(def_id).is_some() {
                    self.try_transpile(|trans| trans.transpile_trait_impl())
                }
            }
            DefPathData::Type(_) => self.try_transpile(|trans| {
                // traits are weird
                if let front::map::Node::NodeItem(&hir::Item { node: hir::Item_::ItemTrait(..), .. }) =
                    trans.tcx.map.get(trans.node_id()) {
                    trans.transpile_trait(&name)
                } else {
                    match trans.tcx.lookup_item_type(def_id).ty.sty {
                        ty::TypeVariants::TyEnum(ref adt_def, _) => trans.transpile_enum(&name, adt_def),
                        ty::TypeVariants::TyStruct(ref adt_def, _) => trans.transpile_struct(adt_def.struct_variant()),
                        ty::TypeVariants::TyTrait(_) => trans.transpile_trait(&name),
                        _ => panic!("unimplemented: transpiling type {:?}", def_id),
                    }
                }
            }),
            DefPathData::Value(_) => {
                if let Some(fn_like) = front::map::blocks::FnLikeNode::from_node(self.tcx.map.get(self.node_id())) {
                    self.try_transpile(|trans| trans.transpile_fn(name, fn_like.decl()))
                }
            }
            _ => {}
        }
    }

    fn try_transpile<F : FnOnce(&mut Transpiler<'a, 'tcx>) -> String>(&mut self, f: F) {
        let name = self.name();

        if self.trans_results.contains_key(&self.def_id) || self.config.ignored.contains(&name) {
            return
        }

        self.deps.borrow_mut().get_def_idx(self.def_id); // add to dependency graph
        self.prelude.clear();
        let res = self.config.replaced.get(&name).map(|res| Ok(res.to_string()));
        let res = res.unwrap_or_else(|| {
            std::panic::recover(std::panic::AssertRecoverSafe::new(|| { f(self) })).map_err(|err| {
                match err.downcast_ref::<String>() {
                    Some(msg) => msg.clone(),
                    None => match err.downcast_ref::<&'static str>() {
                        Some(msg) => msg,
                        None      => "compiler error",
                    }.to_string(),
                }
            })
        });
        self.trans_results.insert(self.def_id, res);
        let new_deps = self.deps.borrow().def_idcs.keys().cloned().collect_vec(); // self.deps.borrow_mut().new_deps.drain()...
        for dep in new_deps {
            self.transpile_def_id(dep)
        }
    }
}

struct IdCollector {
    ids: Vec<NodeId>
}

impl<'a> intravisit::Visitor<'a> for IdCollector {
    fn visit_item(&mut self, item: &'a hir::Item) {
        if let hir::Item_::ItemDefaultImpl(_, _) = item.node {
            return // shrug
        }

        self.ids.push(item.id);
        intravisit::walk_item(self, item);
    }

    fn visit_impl_item(&mut self, ii: &'a hir::ImplItem) {
        self.ids.push(ii.id);
    }

    fn visit_trait_item(&mut self, trait_item: &'a hir::TraitItem) {
        self.ids.push(trait_item.id);
    }
}

struct Config<'a> {
    ignored: HashSet<String>,
    replaced: HashMap<String, String>,
    config: &'a toml::Value,
}

impl<'a> Config<'a> {
    fn new(config: &'a toml::Value) -> Config {
        Config {
            ignored: match config.lookup("ignore") {
                Some(ignored) => toml_value_as_str_array(ignored).into_iter().map(str::to_string).collect(),
                None => HashSet::new(),
            },
            replaced: match config.lookup("replace") {
                Some(replaced) => replaced.as_table().unwrap().iter().map(|(k, v)| {
                    (k.clone(), v.as_str().unwrap().to_string())
                }).collect(),
                None => HashMap::new(),
            },
            config: config,
        }
    }
}

fn transpile_crate(state: &driver::CompileState, config: &toml::Value) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    let crate_name = state.crate_name.unwrap();
    let base = path::Path::new("thys").join(crate_name);
    try!(std::fs::create_dir_all(&base));

    let mut trans = Transpiler {
        tcx: tcx,
        mir_map: &state.mir_map.unwrap(),
        trans_results: HashMap::new(),
        deps: Default::default(),
        config: Config::new(config),
        def_id: DefId::local(DefIndex::new(0)),
        param_names: Vec::new(),
        prelude: Vec::new(),
        refs: HashMap::new(),
    };

    println!("Transpiling...");

    let mut id_collector = IdCollector { ids: vec![] };
    state.hir_crate.unwrap().visit_all_items(&mut id_collector);

    let targets = config.lookup("targets").map(|targets| {
        toml_value_as_str_array(targets).into_iter().collect::<HashSet<_>>()
    });

    for id in id_collector.ids {
        let def_id = tcx.map.local_def_id(id);
        let name = name_def_id(tcx, def_id);
        if targets.iter().all(|targets| targets.contains(&*name)) {
            trans.transpile_def_id(def_id);
        }
    }

    let Transpiler { deps, trans_results, .. } = trans;
    let Deps { crate_deps, graph, .. } = deps.into_inner();

    let mut crate_deps = crate_deps.into_iter().map(|c| format!("{}.generated", c)).collect_vec();
    crate_deps.sort();
    let has_pre = base.join("pre.lean").exists();
    if has_pre {
        crate_deps.insert(0, format!("{}.pre", crate_name));
    }

    let mut f = try!(File::create(base.join("generated.lean")));
    for dep in crate_deps {
        try!(write!(f, "import {}\n", dep));
    }
    try!(write!(f, "import data.nat data.list

noncomputable theory

open classical
open int
open nat
open option
open prod.ops
open sum

namespace {}
", crate_name));
    if has_pre {
        try!(write!(f, "open {}\n", crate_name));
    }
    try!(write!(f, "\n"));

    try!(write!(try!(File::create("deps-un.dot")), "{:?}", &graph));
    let condensed = condensation(graph, /* make_acyclic */ true);
    //try!(write!(try!(File::create("deps.dot")), "{:?}", petgraph::dot::Dot::new(&condensed.map(|_, comp| comp.iter().map(|nid| tcx.map.local_def_id(*nid)).collect_vec(), |_, e| e))));
    let mut failed = HashSet::new();

    for idx in toposort(&condensed) {
        match &condensed[idx][..] {
            [def_id] => {
                let name = name_def_id(tcx, def_id);

                let failed_deps = condensed.neighbors_directed(idx, petgraph::EdgeDirection::Incoming).filter(|idx| failed.contains(idx)).collect_vec();
                if failed_deps.is_empty() {
                    match trans_results.get(&def_id) {
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
                    try!(write!(f, "/- {}: failed dependencies {} -/\n\n", name, failed_deps.into_iter().flat_map(|idx| &condensed[idx]).map(|&def_id| {
                        name_def_id(tcx, def_id)
                    }).join(", ")));
                }
            }
            component => {
                let succeeded = component.iter().filter_map(|def_id| trans_results.get(def_id).and_then(|trans| trans.as_ref().ok())).collect_vec();
                if succeeded.len() == component.len() {
                    if succeeded.iter().all(|trans| trans.starts_with("inductive")) {
                        try!(write!(f, "inductive {}\n\n", succeeded.iter().map(|trans| trans.trim_left_matches("inductive")).join("\n\nwith")));
                        continue;
                    }
                }
                failed.insert(idx);
                try!(write!(f, "/- unimplemented: circular dependencies: {}\n\n", component.iter().map(|&def_id| {
                    name_def_id(tcx, def_id)
                }).join(", ")));
                for &def_id in component {
                    let name = name_def_id(tcx, def_id);
                    match trans_results.get(&def_id) {
                        Some(&Ok(ref trans)) => {
                            try!(write!(f, "{}\n\n", trans));
                        }
                        Some(&Err(ref err)) => {
                            try!(write!(f, "{}: {}\n\n", name, err.replace("/-", "/ -")))
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
