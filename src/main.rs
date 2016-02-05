#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(slice_patterns)]

macro_rules! throw { ($($arg: tt)*) => { return Err(format!($($arg)*)) } }

extern crate itertools;
extern crate petgraph;

#[macro_use]
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_front;
extern crate rustc_metadata;
extern crate rustc_mir;
extern crate syntax;

mod component;
mod mir_graph;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::env;
use std::io;
use std::io::prelude::*;
use std::iter;
use std::fs::File;
use std::path;

use itertools::Itertools;
use petgraph::graph::{self, Graph};
use petgraph::algo::*;

use syntax::ast::{self, NodeId};
use rustc_front::hir::{self, FnDecl, Pat_, Item_};
use rustc_front::intravisit;
use rustc_mir::mir_map::{build_mir_for_crate, MirMap};
use rustc::front::map::Node;
use rustc::mir::repr::*;
use rustc::middle::cstore::CrateStore;
use rustc::middle::const_eval::ConstVal;
use rustc::middle::def_id::DefId;
use rustc::middle::subst::{Subst, Substs, ParamSpace};
use rustc::middle::traits::*;
use rustc::middle::ty;

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
    let krate = env::args().nth(1).unwrap();
    let crate_name = env::args().nth(2).unwrap();
    let cstore = std::rc::Rc::new(rustc_metadata::cstore::CStore::new(syntax::parse::token::get_ident_interner()));
    let sess = session::build_session(
        session::config::Options {
            crate_name: Some(crate_name),
            crate_types: vec![session::config::CrateType::CrateTypeRlib],
            maybe_sysroot: Some(path::PathBuf::from("/usr/local")),
            unstable_features: syntax::feature_gate::UnstableFeatures::Allow,
            .. session::config::basic_options()
        },
        Some(path::PathBuf::from(&krate)),
        diagnostics::registry::Registry::new(&rustc::DIAGNOSTICS),
        cstore.clone()
    );
    let cfg = session::config::build_configuration(&sess);
    println!("Compiling up to MIR...");
    driver::compile_input(&sess, &cstore, cfg,
        &session::config::Input::File(path::PathBuf::from(&krate)),
        &None, &None, None, driver::CompileController {
            after_analysis: driver::PhaseController {
                stop: rustc_driver::Compilation::Stop,
                callback: Box::new(|state| transpile_crate(&state).unwrap()),
                run_callback_on_error: false,
            },
            .. driver::CompileController::basic()
        }
    );
}

fn binop_to_string(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::BitXor => "^",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Eq => "==",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Ne => "\\<noteq>",
        BinOp::Ge => ">=",
        BinOp::Gt => ">",
    }
}

fn selector(idx: usize, len: usize) -> Vec<&'static str> {
    iter::repeat("_").take(idx)
        .chain(iter::once("x"))
        .chain(iter::repeat("_").take(len - idx - 1))
        .collect()
}

fn mk_isabelle_name(s: &str) -> String {
    s.replace(|c: char| !c.is_alphanumeric(), "_").trim_matches('_').to_string()
}

fn unwrap_refs<'tcx>(ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
    match ty.sty {
        ty::TypeVariants::TyRef(_, ty::TypeAndMut { ty, .. }) => unwrap_refs(ty),
        _ => ty
    }
}

fn try_unwrap_mut_ref<'tcx>(ty: &ty::Ty<'tcx>) -> Option<ty::Ty<'tcx>> {
    match ty.sty {
        ty::TypeVariants::TyRef(_, ty::TypeAndMut { mutbl: hir::Mutability::MutMutable, ty }) =>
            Some(ty),
        _ => None
    }
}

fn format_generic_ty<It: Iterator<Item=String>>(generics: It, ty: &str) -> String {
    match &generics.collect_vec()[..] {
        [] => ty.to_string(),
        [ref ty_arg] => format!("{} {}", ty_arg, ty),
        generics => format!("({}) {}", generics.iter().join(", "), ty),
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
    tcx: &'a ty::ctxt<'tcx>,
    mir_map: MirMap<'tcx>,
    trans_results: HashMap<NodeId, TransResult>,
    deps: RefCell<Deps>,

    // inside of fns
    node_id: ast::NodeId,
    param_names: Vec<String>,
}

fn transpile_def_id(tcx: &ty::ctxt, did: DefId) -> String {
    let mut path = tcx.item_path_str(did);
    if did.is_local() {
        path = format!("{}::{}", tcx.sess.opts.crate_name.clone().unwrap(), path);
    }
    mk_isabelle_name(&path)
}

fn transpile_node_id(tcx: &ty::ctxt, node_id: ast::NodeId) -> String {
    transpile_def_id(tcx, tcx.map.local_def_id(node_id))
}

impl<'a, 'tcx> Transpiler<'a, 'tcx> {
    fn transpile_def_id(&self, did: DefId) -> String {
        if let Some(node_id) = self.tcx.map.as_local_node_id(did) {
            self.deps.borrow_mut().add_dep(node_id, self.node_id);
        } else {
            let crate_name = self.tcx.sess.cstore.crate_name(did.krate);
            self.deps.borrow_mut().crate_deps.insert(crate_name.clone());
        }

        transpile_def_id(self.tcx, did)
    }

    fn transpile_node_id(&self, node_id: ast::NodeId) -> String {
        self.transpile_def_id(self.tcx.map.local_def_id(node_id))
    }

    fn transpile_generics(&self, generics: &hir::Generics, ty: &str) -> TransResult {
        Ok(format_generic_ty(generics.ty_params.iter().map(|p| format!("'{}", p.name)), ty))
    }

    fn transpile_trait_ref(&self, trait_ref: &ty::TraitRef<'tcx>) -> TransResult {
        let substs: Result<Vec<_>,_> = trait_ref.substs.types.iter().map(|ty| {
            self.transpile_ty(ty).map(|s| mk_isabelle_name(&s))
        }).collect();
        Ok(try!(substs).into_iter().chain(iter::once(self.transpile_def_id(trait_ref.def_id))).join("_"))
    }

    fn transpile_ty(&self, ty: ty::Ty<'tcx>) -> TransResult {
        Ok(match ty.sty {
            ty::TypeVariants::TyBool => "bool".to_string(),
            ty::TypeVariants::TyUint(ref ty) => ty.to_string(),
            ty::TypeVariants::TyInt(ref ty) => ty.to_string(),
            ty::TypeVariants::TyFloat(ref ty) => ty.to_string(),
            ty::TypeVariants::TyTuple(ref tys) => match &tys[..] {
                [] => "unit".to_string(),
                _ => format!("({})", try!(tys.iter().map(|ty| self.transpile_ty(ty)).join_results(" × "))),
            },
            ty::TypeVariants::TyBareFn(_, ref data) => {
                let sig = data.sig.skip_binder();
                let muts = sig.inputs.iter().filter_map(try_unwrap_mut_ref);
                let inputs = try!(sig.inputs.iter().map(|ty| self.transpile_ty(ty)).join_results(" => "));
                let outputs = match sig.output {
                    ty::FnOutput::FnConverging(out_ty) => try!(iter::once(out_ty).chain(muts).map(|ty| self.transpile_ty(ty)).join_results(" × ")),
                    ty::FnOutput::FnDiverging => throw!("unimplemented: diverging function"),
                };
                if inputs.is_empty() {
                    outputs
                } else {
                    format!("{} => {}", inputs, outputs)
                }
            },
            ty::TypeVariants::TyStruct(ref adt_def, ref substs) |
            ty::TypeVariants::TyEnum(ref adt_def, ref substs) => format_generic_ty(
                try!(substs.types.iter().map(|ty| self.transpile_ty(ty)).collect_results()),
                &self.transpile_def_id(adt_def.did)
            ),
            ty::TypeVariants::TyRef(_, ref data) => try!(self.transpile_ty(data.ty)),
            ty::TypeVariants::TyParam(ref param) => format!("'{}", param.name),
            ty::TypeVariants::TyProjection(ref proj) => format!("'{}__{}", try!(self.transpile_trait_ref(&proj.trait_ref)), proj.item_name),
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

    fn mir(&self) -> &Mir<'tcx> {
        &self.mir_map[&self.node_id]
    }

    fn lvalue_name(&self, lv: &Lvalue) -> Option<String> {
        Some(match *lv {
            Lvalue::Var(idx) => format!("v_{}", self.mir().var_decls[idx as usize].name),
            Lvalue::Temp(idx) => format!("t_{}", idx),
            Lvalue::Arg(idx) => self.param_names[idx as usize].clone(),
            Lvalue::Static(did) => self.transpile_def_id(did),
            Lvalue::ReturnPointer => "ret".to_string(),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                return self.lvalue_name(base),
            Lvalue::Projection(_) => return None,
        })
    }

    fn locals(&self) -> Vec<Lvalue> {
        self.mir().var_decls.iter().enumerate().map(|(idx, _)| Lvalue::Var(idx as u32))
            .chain(self.mir().temp_decls.iter().enumerate().map(|(idx, _)| Lvalue::Temp(idx as u32)))
            .chain(iter::once(Lvalue::ReturnPointer))
            .collect()
    }

    fn num_locals(&self) -> usize { self.locals().len() }

    fn get_lvalue(&self, lv: &Lvalue<'tcx>) -> TransResult {
        if let Some(name) = self.lvalue_name(lv) {
            return Ok(name)
        }
        match *lv {
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.get_lvalue(base),
            Lvalue::Projection(box Projection {
                elem: ProjectionElem::Field(ref field),
                base: Lvalue::Projection(box Projection {
                    ref base,
                    elem: ProjectionElem::Downcast(ref adt_def, variant_idx),
                }),
            }) => {
                let variant = &adt_def.variants[variant_idx];
                Ok(format!("(case {lv} of {variant} {args} => x)",
                           lv=try!(self.get_lvalue(base)),
                           variant=self.transpile_def_id(variant.did),
                           args=selector(field.index(), variant.fields.len()).join(" ")))
            }
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(ref field) }) =>
                match unwrap_refs(try!(self.lvalue_ty(base))).sty {
                    ty::TypeVariants::TyStruct(ref adt_def, _) =>
                        Ok(format!("({}_{} {})", self.transpile_def_id(adt_def.did), adt_def.struct_variant().fields[field.index()].name, try!(self.get_lvalue(base)))),
                    ref ty => throw!("unimplemented: accessing field of {:?}", ty),
                },
            _ => Err(format!("unimplemented: loading {:?}", lv)),
        }
    }

    fn lvalue_ty(&self, lv: &Lvalue<'tcx>) -> Result<ty::Ty<'tcx>, String> {
        Ok(match *lv {
            Lvalue::Var(idx) => self.mir().var_decls[idx as usize].ty,
            Lvalue::Temp(idx) => self.mir().temp_decls[idx as usize].ty,
            Lvalue::Arg(idx) => self.mir().arg_decls[idx as usize].ty,
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                return self.lvalue_ty(base),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(ref field) }) => {
                let ty = try!(self.lvalue_ty(base));
                match ty.sty {
                     ty::TypeVariants::TyStruct(ref adt_def, ref substs) =>
                         adt_def.struct_variant().fields[field.index()].ty(self.tcx, substs),
                     _ => throw!("unimplemented: type of lvalue {:?}", lv),
                }
            }
            _ => throw!("unimplemented: type of lvalue {:?}", lv),
        })
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
        if let Some(name) = self.lvalue_name(lv) {
            return Ok(format!("let {} = {} in\n", name, val));
        }
        match *lv {
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.set_lvalue(base, val),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(ref field) }) => {
                let base_name = try!(self.lvalue_name(base).ok_or_else(|| format!("ugh, nested fields assignments? {:?}", lv)));
                match unwrap_refs(try!(self.lvalue_ty(base))).sty {
                    ty::TypeVariants::TyStruct(ref adt_def, _) => {
                        let field_name = adt_def.struct_variant().fields[field.index()].name;
                        Ok(format!("let {} = {} \\<lparr> {}_{} := {} \\<rparr> in\n", base_name, base_name, self.transpile_def_id(adt_def.did), field_name, val))
                    },
                    ref ty => throw!("unimplemented: setting field of {:?}", ty),
                }
            }
            _ => throw!("unimplemented: setting lvalue {:?}", lv),
        }
    }

    fn set_lvalues<'b, It: Iterator<Item=&'b Lvalue<'tcx>>>(&self, lvs: It, val: &str) -> TransResult
        where 'tcx: 'b {
        Ok(format!("let ({}) = {} in\n",
                   try!(lvs.map(|lv| self.lvalue_name(lv).ok_or("unimplemented: non-trivial set_lvalues")).join_results(", ")),
                   val))
    }

    fn transpile_constval(&self, val: &ConstVal) -> TransResult {
        Ok(match *val {
            ConstVal::Bool(true) => "True".to_string(),
            ConstVal::Bool(false) => "False".to_string(),
            ConstVal::Int(i) => i.to_string(),
            ConstVal::Uint(i) => i.to_string(),
            _ => throw!("unimplemented: literal {:?}", val),
        })
    }

    fn get_operand(&self, op: &Operand<'tcx>) -> TransResult {
        Ok(match *op {
            Operand::Consume(ref lv) => try!(self.get_lvalue(lv)),
            Operand::Constant(ref c) => match c.literal {
                Literal::Value { ref value } => try!(self.transpile_constval(value)),
                _ => throw!("unimplemented: constant {:?}", c)
            }
        })
    }

    fn get_rvalue(&self, rv: &Rvalue<'tcx>) -> TransResult {
        match *rv {
            Rvalue::Use(ref op) => self.get_operand(op),
            Rvalue::UnaryOp(UnOp::Not, ref op) => Ok(format!("(\\<not> {})", try!(self.get_operand(op)))),
            Rvalue::UnaryOp(UnOp::Neg, ref op) => Ok(format!("(- {})", try!(self.get_operand(op)))),
            Rvalue::BinaryOp(op, ref o1, ref o2) =>
                Ok(format!("({} {} {})", try!(self.get_operand(o1)), binop_to_string(op),
                           try!(self.get_operand(o2)))),
            Rvalue::Ref(_, BorrowKind::Shared, ref lv) => self.get_lvalue(lv),
            Rvalue::Ref(_, BorrowKind::Mut, ref lv) => self.get_lvalue(lv),
            Rvalue::Aggregate(AggregateKind::Adt(ref adt_def, variant_idx, _), ref ops) => {
                let variant = &adt_def.variants[variant_idx];
                let ops = try!(ops.iter().map(|op| self.get_operand(op)).collect::<Result<Vec<_>, _>>());
                Ok(format!("({}{} {})",
                           self.transpile_def_id(variant.did),
                           if adt_def.adt_kind() == ty::AdtKind::Struct { ".make" } else { "" },
                           ops.iter().join(" ")))
            }
            _ => Err(format!("unimplemented: rvalue {:?}", rv)),
        }
    }

    fn transpile_statement(&self, stmt: &'a Statement<'tcx>, comp: &mut Component<'a, 'tcx>) -> TransResult {
        match stmt.kind {
            StatementKind::Assign(ref lv, Rvalue::Ref(_, BorrowKind::Mut, ref lsource)) => {
                comp.refs.insert(try!(self.lvalue_idx(lv)), lsource);
                self.set_lvalue(lv, &&try!(self.get_lvalue(lsource)))
                //format!("let ({lv}, {lsource}) = ({lsource}, undefined) in\n", lv=self.get_lvalue(lv), lsource=self.get_lvalue(lsource))
            }
            StatementKind::Assign(ref lv, ref rv) => {
                if *lv != Lvalue::ReturnPointer && try!(self.lvalue_ty(lv)).is_nil() {
                    // optimization/rustc_mir workaround: don't save '()'
                    Ok("".to_string())
                } else {
                    self.set_lvalue(lv, &&try!(self.get_rvalue(rv)))
                }
            }
            StatementKind::Drop(DropKind::Deep, ref lv) => {
                //match comp.refs.get(&self.lvalue_idx(lv)) {
                //    Some(lsource) => format!("let ({lsource}, {lv}) = ({lv}, undefined) in\n", lsource=lsource, lv=self.get_lvalue(lv)),
                //    None => self.set_lvalue(lv, "undefined")
                //}
                Ok(match comp.refs.get(&&try!(self.lvalue_idx(lv))) {
                    Some(lsource) => try!(self.set_lvalue(lsource, &&try!(self.get_lvalue(lv)))),
                    None => "".to_string()
                })
            }
            _ => throw!("unimplemented: statement {:?}", stmt),
        }
    }

    fn transpile_basic_block_rec(&'a self, bb: BasicBlock, comp: &mut Component<'a, 'tcx>) -> TransResult {
        if comp.header == Some(bb) {
            Ok(format!("(({}), True)", comp.nonlocal_defs.iter().join(", ")))
        } else {
            self.transpile_basic_block(bb, comp)
        }
    }

    fn call_return_dests<'b>(&self, call: &'b Terminator<'tcx>) -> Result<Vec<&'b Lvalue<'tcx>>, String> {
        match call {
            &Terminator::Call { ref args, ref kind, .. } => {
                let muts = try!(args.iter().map(|op| Ok(match *op {
                    Operand::Consume(ref lv) => try_unwrap_mut_ref(&try!(self.lvalue_ty(lv))).map(|_| lv),
                    Operand::Constant(_) => None,
                })).collect::<Result<Vec<_>, String>>());
                Ok(kind.destination().into_iter().chain(muts.into_iter().filter_map(|x| x)).collect())
            }
            _ => Ok(Vec::new()),
        }
    }

    fn transpile_trait_call(&self, caller: ast::NodeId, callee: DefId, substs: &Substs<'tcx>) -> TransResult {
        let trait_def_id = self.tcx.trait_of_item(callee).unwrap();

        // from trans::meth::trans_method_callee
        let trait_ref = substs.to_trait_ref(self.tcx, trait_def_id);

        Ok(format!("{} {}", self.transpile_def_id(callee), try!(self.infer_trait_impl(&trait_ref, caller))))
    }

    fn infer_trait_impl(&self, trait_ref: &ty::TraitRef<'tcx>, param_env: NodeId) -> TransResult {
        use rustc::middle::infer;

        let span = syntax::codemap::DUMMY_SP;
        let param_env = ty::ParameterEnvironment::for_item(self.tcx, param_env);
        let dbg_param_env = format!("{:?}", param_env.caller_bounds);
        let infcx = infer::new_infer_ctxt(self.tcx, &self.tcx.tables, Some(param_env));
        let mut selcx = SelectionContext::new(&infcx);
        let obligation =
            Obligation::new(ObligationCause::misc(span, ast::DUMMY_NODE_ID),
            ty::Binder(trait_ref.clone()).to_poly_trait_predicate());
        let selection = match selcx.select(&obligation) {
            Ok(x) => x.unwrap(),
            Err(err) => throw!("obligation select: {:?} {:?} {:?}", obligation, err, dbg_param_env),
        };

        match selection {
            Vtable::VtableImpl(data) => {
                let nested_traits = try!(data.nested.into_iter().map(|obl| Ok(match obl.predicate {
                    ty::Predicate::Trait(ref trait_pred) if !self.is_marker_trait(trait_pred.skip_binder().def_id()) => {
                        let obl = Obligation::new(ObligationCause::misc(span, ast::DUMMY_NODE_ID), trait_pred.clone());
                        match try!(selcx.select(&obl).map_err(|e| format!("obligation select: {:?} {:?}", obl, e))) {
                            Some(Vtable::VtableImpl(data)) => Some(self.transpile_def_id(data.impl_def_id)),
                            Some(Vtable::VtableParam(_)) => Some(format!("{:?}", trait_pred)),
                            Some(vtable) => throw!("unimplemented: vtable {:?}", vtable),
                            None => throw!("unfulfilled predicate: {:?}", obl),
                        }
                    }
                    _ => None,
                })).collect_results()).filter_map(|x| x);
                Ok(format!("({})", iter::once(self.transpile_def_id(data.impl_def_id)).chain(nested_traits).join(" ")))
            },
            Vtable::VtableParam(_) => {
                // FIXME very broken parameter lookup
                let param_trait_ref = try!(self.trait_predicates_without_markers(self.def_id()).filter_map(|trait_pred| {
                    let param_trait_ref = ty::Binder(trait_pred.trait_ref);
                    if supertraits(self.tcx, param_trait_ref).any(|t| t.skip_binder().def_id == trait_ref.def_id) {
                        Some(param_trait_ref)
                    } else {
                        None
                    }
                }).next().ok_or_else(|| format!("param trait lookup failed for {:?}", trait_ref)));

                self.transpile_trait_ref(&param_trait_ref.skip_binder())
            }
            vtable => throw!("unimplemented: vtable {:?}", vtable),
        }
    }

    fn transpile_basic_block(&'a self, bb: BasicBlock, comp: &mut Component<'a, 'tcx>) -> TransResult {
        macro_rules! rec { ($bb:expr) => { try!(self.transpile_basic_block_rec($bb, comp)) } }

        if !comp.blocks.contains(&bb) {
            comp.exits.push(bb);
            return Ok(format!("(({}), False)", comp.nonlocal_defs.iter().join(", ")));
        }
        if let Some(l) = comp.loops.clone().into_iter().find(|l| l.contains(&bb)) {
            let mut l_comp = try!(Component::new(self, bb, l, true));
            let body = try!(self.transpile_basic_block(bb, &mut l_comp));
            let name = format!("{}_{}", self.tcx.item_name(self.def_id()), bb.index());
            if l_comp.exits.len() != 1 {
                throw!("Oops, multiple loop exits: {:?}", l_comp);
            }
            comp.prelude.push(format!("definition {name} where \"{name} {uses} = (\\<lambda>({defs}). {body})\"",
                                      name=name,
                                      uses=l_comp.nonlocal_uses.iter().join(" "),
                                      defs=l_comp.nonlocal_defs.iter().join(", "),
                                      body=body));
            return Ok(format!("let ({muts}) = loop ({name} {immuts}) ({muts}) in\n{cont}", muts=l_comp.nonlocal_defs.iter().join(", "),
                              name=name, immuts=l_comp.nonlocal_uses.iter().join(" "), cont=rec!(l_comp.exits[0])));
        }

        let data = self.mir().basic_block_data(bb);
        let stmts = try!(data.statements.iter().map(|s| self.transpile_statement(s, comp)).collect::<Result<Vec<_>, _>>());
        let terminator = match data.terminator {
            Some(ref terminator) => Some(match *terminator {
                Terminator::Goto { target } =>
                    rec!(target),
                Terminator::If { ref cond, targets: (bb_if, bb_else) } =>
                    format!("if {} then {} else {}", try!(self.get_operand(cond)),
                    rec!(bb_if),
                    rec!(bb_else)),
                Terminator::Return => try!(self.return_expr()),
                Terminator::Call {
                    func: Operand::Constant(Constant { literal: Literal::Item { def_id, substs, .. }, .. }),
                    ref args, ref kind,
                } => {
                    let call = match self.tcx.trait_of_item(def_id) {
                        Some(_) => try!(self.transpile_trait_call(self.node_id, def_id, substs)),
                        _ => self.transpile_def_id(def_id),
                    };
                    let args = try!(args.iter().map(|op| self.get_operand(op)).collect::<Result<Vec<_>, _>>());
                    let call = match self.tcx.adt_defs.borrow().get(&def_id) {
                        Some(_) => throw!("Weird Adt call: {:?}", terminator),
                        None => format!("({} {})", call,
                                        args.into_iter().join(" "))
                    };
                    try!(self.set_lvalues(try!(self.call_return_dests(&terminator)).into_iter(), &call)) + &&rec!(kind.successors()[0])
                }
                Terminator::Call { .. } =>
                    throw!("unimplemented: call {:?}", terminator),
                Terminator::Switch { ref discr, ref adt_def, ref targets } => {
                    let arms: TransResult = adt_def.variants.iter().zip(targets).map(|(var, &target)| {
                        Ok(format!("{} {} => {}", self.transpile_def_id(var.did),
                           iter::repeat("_").take(var.fields.len()).join(" "),
                           rec!(target)))
                    }).join_results(" | ");
                    format!("case {} of {}", try!(self.get_lvalue(discr)), try!(arms))
                },
                Terminator::SwitchInt { ref discr, switch_ty: _, ref values, ref targets } => {
                    let arms: TransResult = values.iter().zip(targets).map(|(val, &target)| {
                        Ok(format!("{} => {}", try!(self.transpile_constval(val)), rec!(target)))
                    }).join_results(" | ");
                    format!("case {} of {}", try!(self.get_lvalue(discr)), try!(arms))
                },
                Terminator::Resume => String::new(),
            }),
            None => None,
        };
        Ok(stmts.into_iter().chain(terminator.into_iter()).join(""))
    }

    fn hir_ty_to_ty(&self, ty: &hir::Ty) -> ty::Ty<'tcx> {
        self.tcx.ast_ty_to_ty_cache.borrow()[&ty.id]
    }

    fn sig(&self) -> &ty::FnSig<'tcx> {
        self.tcx.node_id_to_type(self.node_id).fn_sig().skip_binder()
    }

    fn return_expr(&self) -> TransResult {
        let muts = self.sig().inputs.iter().zip(self.param_names.iter()).filter_map(|(ty, name)| {
            try_unwrap_mut_ref(ty).map(|_| name.clone())
        });
        Ok(format!("({})", iter::once("ret".to_string()).chain(muts).join(", ")))
    }

    fn transpile_fn(&mut self, name: String, decl: &FnDecl) -> TransResult {
        self.param_names = decl.inputs.iter().enumerate().map(|(i, param)| match param.pat.node {
            Pat_::PatIdent(_, ref ident, _) => ident.node.name.to_string(),
            _ => format!("p{}", i),
        }).collect();

        let mut comp = try!(Component::new(self, START_BLOCK, self.mir().all_basic_blocks(), false));
        let body = try!(self.transpile_basic_block(START_BLOCK, &mut comp));

        let trait_params = try!(self.trait_predicates_without_markers(self.def_id()).map(|trait_pred| {
                self.transpile_trait_ref(&trait_pred.trait_ref)
        }).collect_results());

        let def = format!("definition {name} where\n\"{name} {param_names} = ({body})\"",
                          name=name, param_names=trait_params.chain(self.param_names.clone()).join(" "), body=body);
        Ok(comp.prelude.into_iter().chain(iter::once(def)).join("\n\n"))
    }

    fn transpile_struct(&self, name: &str, data: &hir::VariantData, generics: &hir::Generics) -> TransResult {
        match *data {
            hir::VariantData::Struct(ref fields, _) => {
                let fields: TransResult = fields.iter().map(|f| {
                    Ok(format!("  {}_{} :: \"{}\"", name, f.node.name().unwrap(),
                               try!(self.transpile_hir_ty(&*f.node.ty))))
                }).join_results("\n");
                Ok(format!("record {} =\n{}",
                           try!(self.transpile_generics(generics, name)), try!(fields)))
            }
            _ => throw!("unimplemented: struct {:?}", data)
        }
    }

    fn transpile_enum(&self, name: &str, def: &hir::EnumDef, generics: &hir::Generics) -> TransResult {
        let variants = def.variants.iter().map(|variant| {
            Ok(match variant.node.data {
                hir::VariantData::Unit(node_id) => self.transpile_node_id(node_id),
                hir::VariantData::Tuple(ref fields, node_id) => {
                    let fields = try!(fields.iter().map(|f| -> TransResult {
                        Ok(format!("\"{}\"", try!(self.transpile_hir_ty(&*f.node.ty))))
                    }).join_results(" "));
                    format!("{} {}", self.transpile_node_id(node_id), fields)
                }
                ref data => throw!("unimplemented: enum variant {:?}", data)
            })
        });
        Ok(format!("datatype {} =\n  {}",
                   try!(self.transpile_generics(generics, name)),
                   try!(variants.into_iter().join_results("\n| "))))
    }

    fn transpile_trait(&self, trait_def_id: DefId, generics: &hir::Generics, items: &[hir::TraitItem]) -> TransResult {
        let trait_name = self.transpile_def_id(trait_def_id);

        let (assoc_ty_params, supertraits): (Vec<_>, Vec<_>) = try!(self.trait_predicates_without_markers(trait_def_id).map(|trait_pred| -> Result<_, String> {
            let trait_def = self.tcx.lookup_trait_def(trait_pred.def_id());
            let prefix = try!(self.transpile_trait_ref(&trait_pred.trait_ref));
            let ty_params = trait_def.associated_type_names.iter().map(|name| format!("'{}__{}", prefix, name)).collect_vec();
            let supertrait = if trait_pred.def_id() == trait_def_id { None } else {
                Some((prefix, format_generic_ty(
                            try!(trait_pred.trait_ref.substs.types.iter().map(|ty| self.transpile_ty(ty)).collect_results()),
                            &self.transpile_def_id(trait_pred.def_id()))))
            };
            Ok((ty_params, supertrait))
        }).collect_results()).unzip();
        let assoc_ty_params = assoc_ty_params.into_iter().flat_map(|x| x);
        let supertraits = supertraits.into_iter().filter_map(|x| x);

        let fns = try!(items.into_iter().filter_map(|item| match item.node {
            hir::TraitItem_::MethodTraitItem(_, _) => {
                Some(self.transpile_ty(self.tcx.node_id_to_type(item.id)).map(|ty| {
                    (format!("{}__{}", trait_name, item.name), ty)
                }))
            }
            _ => None,
        }).collect_results());
        Ok(format!("record {} =\n{}",
                   format_generic_ty(
                       iter::once("'Self".to_string()).chain(generics.ty_params.iter().map(|p| format!("'{}", p.name))).chain(assoc_ty_params),
                       &trait_name),
                   supertraits.chain(fns).map(|(name, ty)| {
                       format!("  {} :: \"{}\"", name, ty)
                   }).join("\n")))

    }

    fn transpile_trait_impl(&self, id: NodeId, trait_ref: &hir::TraitRef, self_ty: &hir::Ty, items: &[hir::ImplItem]) -> TransResult {
        let def_id = self.tcx.map.local_def_id(id);
        if !self.hir_ty_to_ty(self_ty).regions().is_empty() {
            throw!("ign");
        }
        let trait_def_id = self.tcx.trait_ref_to_def_id(trait_ref);
        let ty_trait_ref = self.tcx.impl_trait_ref(def_id).unwrap();
        let trait_name = self.transpile_def_id(trait_def_id);
        let supertrait_impls = try!(self.trait_predicates_without_markers(trait_def_id).map(|p| p.subst(self.tcx, ty_trait_ref.substs)).map(|trait_pred| -> Result<_, String> {
            if trait_pred.def_id() == trait_def_id {
                return Ok(None);
            }
            let field_name = try!(self.transpile_trait_ref(&trait_pred.trait_ref));
            //let mut trait_substs = trait_pred.trait_ref.substs.clone();
            //trait_substs.types.replace(ParamSpace::SelfSpace, vec![self.hir_ty_to_ty(self_ty)]);
            //let trait_ref = trait_substs.to_trait_ref(self.tcx, trait_pred.trait_ref.def_id);
            let trait_impl = try!(self.infer_trait_impl(&trait_pred.trait_ref, id));
            Ok(Some(format!("{} {}", field_name, trait_impl)))
        }).collect_results()).filter_map(|x| x);
        let methods = items.iter().filter_map(|item| match item.node {
            hir::ImplItemKind::Method(..) => {
                let name = self.transpile_node_id(item.id);
                Some(format!("  {}__{} = {}", trait_name, item.name, name))
            }
            _ => None,
        });

        Ok(format!("definition \"{} = \\<lparr>\n{}\n\\<rparr>\"", self.transpile_node_id(id), supertrait_impls.chain(methods).join(",\n")))
    }

    fn transpile_item(&mut self, item: &hir::Item) -> TransResult {
        self.node_id = item.id;
        let name = self.transpile_def_id(self.def_id());
        Ok(match item.node {
            Item_::ItemFn(ref decl, _, _, _, _, _) =>
                try!(self.transpile_fn(name, decl)),
            Item_::ItemImpl(_, _, _, ref base_trait, ref self_ty, ref items) => {
                match base_trait {
                    &Some(ref base_trait) if !self.is_marker_trait(self.tcx.trait_ref_to_def_id(base_trait)) =>
                        try!(self.transpile_trait_impl(item.id, base_trait, self_ty, items)),
                    _ => "".to_string(),
                }
            }
            Item_::ItemStruct(ref data, ref generics) =>
                try!(self.transpile_struct(&name, data, generics)),
            Item_::ItemEnum(ref def, ref generics) =>
                try!(self.transpile_enum(&name, def, generics)),
            Item_::ItemTrait(_, ref generics, _, ref items) => {
                if self.is_marker_trait(self.def_id()) { "".to_string() } else {
                    try!(self.transpile_trait(self.def_id(), generics, items))
                }
            }
            Item_::ItemUse(..) | Item_::ItemMod(..) | Item_::ItemExternCrate(_) => "".to_string(),
            _ => throw!("unimplemented item type: {:?}", name),
        })
    }

    fn transpile_method(&mut self, node_id: NodeId) -> TransResult {
        self.node_id = node_id;
        let name = self.transpile_def_id(self.def_id());
        let (name, sig) = match self.tcx.map.get(node_id) {
            Node::NodeImplItem(&hir::ImplItem { node: hir::ImplItemKind::Method(ref sig, _), .. }) => (name, sig),
            Node::NodeTraitItem(&hir::TraitItem { node: hir::MethodTraitItem(ref sig, _), .. }) =>
                (format!("{}__{}", self.transpile_def_id(self.tcx.trait_of_item(self.def_id()).unwrap()), name), sig),
            _ => unreachable!(),
        };
        self.transpile_fn(name, &*sig.decl)
    }
}

impl<'a, 'tcx> intravisit::Visitor<'a> for Transpiler<'a, 'tcx> {
    fn visit_item(&mut self, item: &'a hir::Item) {
        self.deps.borrow_mut().get_def_idx(item.id);
        let res = self.transpile_item(item);
        self.trans_results.insert(item.id, res);
        intravisit::walk_item(self, item);
    }

    fn visit_impl_item(&mut self, ii: &'a hir::ImplItem) {
        match ii.node {
            hir::ImplItemKind::Method(..) => {
                self.deps.borrow_mut().get_def_idx(ii.id);
                let res = self.transpile_method(ii.id);
                self.trans_results.insert(ii.id, res);
            }
            _ => {}
        }
    }

    fn visit_trait_item(&mut self, trait_item: &'a hir::TraitItem) {
        match trait_item.node {
            hir::TraitItem_::MethodTraitItem(_, Some(_)) => {
                self.deps.borrow_mut().get_def_idx(trait_item.id);
                let res = self.transpile_method(trait_item.id);
                self.trans_results.insert(trait_item.id, res);
            }
            _ => {}
        }
    }
}

fn transpile_crate(state: &driver::CompileState) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    let crate_name = state.crate_name.unwrap();

    println!("Building MIR...");
    let mut trans = Transpiler {
        tcx: tcx,
        mir_map: build_mir_for_crate(tcx),
        trans_results: HashMap::new(),
        deps: RefCell::new(Deps {
            crate_deps: HashSet::new(),
            def_idcs: HashMap::new(),
            graph: Graph::new(),
        }),
        node_id: 0,
        param_names: Vec::new(),
    };
    println!("Transpiling...");
    state.hir_crate.unwrap().visit_all_items(&mut trans);

    let Transpiler { deps, trans_results, .. } = trans;
    let Deps { crate_deps, graph, .. } = deps.into_inner();

    let mut crate_deps: Vec<String> = crate_deps.into_iter().map(|krate| format!("{}_export", krate)).collect();
    crate_deps.sort();
    if path::Path::new("thys").join(format!("{}_pre.thy", crate_name)).exists() {
        crate_deps.insert(0, format!("{}_pre", crate_name));
    }

    let mut f = try!(File::create(path::Path::new("thys").join(format!("{}_export.thy", crate_name))));
    try!(write!(f, "theory {}_export\nimports\n{}\nbegin\n\n", crate_name,
                crate_deps.into_iter().map(|file| format!("  {}", file)).join("\n")));

    try!(write!(try!(File::create("deps-un.dot")), "{:?}", petgraph::dot::Dot::new(&graph.map(|_, nid| tcx.map.local_def_id(*nid), |_, e| e))));
    let condensed = condensation(graph, false);
    try!(write!(try!(File::create("deps.dot")), "{:?}", petgraph::dot::Dot::new(&condensed.map(|_, comp| comp.iter().map(|nid| tcx.map.local_def_id(*nid)).collect_vec(), |_, e| e))));
    let mut failed = HashSet::new();
    for idx in toposort(&condensed) {
        match &condensed[idx][..] {
            [node_id] => {
                let name = transpile_node_id(tcx, node_id);
                let failed_deps = condensed.neighbors(idx).filter(|idx| failed.contains(idx)).collect_vec();
                if failed_deps.is_empty() {
                    match trans_results.get(&node_id) {
                        Some(&Ok(ref trans)) => {
                            if !trans.is_empty() {
                                try!(write!(f, "{}\n\n", trans));
                            }
                        }
                        Some(&Err(ref err)) => {
                            failed.insert(idx);
                            try!(write!(f, "(* {}: {} *)\n\n", name, err.replace("(*", "( *")))
                        }
                        None => {
                            failed.insert(idx);
                        }
                    }
                } else {
                    try!(write!(f, "(* {}: failed dependencies {} *)\n\n", name, failed_deps.into_iter().flat_map(|idx| &condensed[idx]).map(|&node_id| {
                        transpile_node_id(tcx, node_id)
                    }).join(", ")));
                }
            }
            component => {
                failed.insert(idx);
                try!(write!(f, "(* unimplemented: circular dependencies: {} *)\n\n", component.iter().map(|&node_id| {
                    transpile_node_id(tcx, node_id)
                }).join(", ")));
            }
        }
    }

    write!(f, "end\n")
}
