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

use std::collections::{HashMap, HashSet};
use std::env;
use std::io;
use std::io::prelude::*;
use std::iter;
use std::fs::File;
use std::path;

use itertools::Itertools;

use syntax::ast;
use rustc_front::hir;
use rustc_front::hir::{FnDecl, Pat_, BindingMode, Item_};
use rustc_mir::mir_map::build_mir_for_crate;
use rustc::mir::repr::*;
use rustc::middle::cstore::CrateStore;
use rustc::middle::const_eval::ConstVal;
use rustc::middle::def_id::DefId;
use rustc::middle::subst::{Substs, ParamSpace};
use rustc::middle::traits::*;
use rustc::middle::ty;

use rustc_driver::driver;
use syntax::diagnostics;
use rustc::session;

use component::Component;

type TransResult = Result<String, String>;

trait StringResultIterator<E> : Iterator<Item=Result<String, E>> {
    fn join_results(&mut self, sep: &str) -> Result<String, E> {
        let items = try!(self.collect::<Result<Vec<_>, _>>());
        Ok(items.iter().join(sep))
    }
}

impl<T, E> StringResultIterator<E> for T where T: Iterator<Item=Result<String, E>> { }

fn try_write(f: &mut File, name: &str, res: TransResult) -> io::Result<()> {
    match res {
        Ok(trans) => try!(write!(f, "{}\n\n", trans)),
        Err(err) => try!(write!(f, "(* {}: {} *)\n\n", name, err.replace("(*", "( *"))),
    };
    Ok(())
}

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
    driver::compile_input(sess, &cstore, cfg,
        &session::config::Input::File(path::PathBuf::from(&krate)),
        &None, &None, None, driver::CompileController {
            after_analysis: driver::PhaseController {
                stop: rustc_driver::Compilation::Stop,
                callback: Box::new(|state| transpile_crate(&state).unwrap()),
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

pub struct FnTranspiler<'a, 'tcx: 'a> {
    mod_transpiler: &'a ModuleTranspiler<'a, 'tcx>,
    node_id: ast::NodeId,
    tcx: &'a ty::ctxt<'tcx>,
    mir: &'a Mir<'tcx>,
    param_names: &'a Vec<String>,
    return_expr: String,
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

fn transpile_def_id(did: DefId, tcx: &ty::ctxt, crate_name: &str) -> String {
    // what could ever go wrong
    let mut path = tcx.item_path_str(did);
    if did.is_local() {
        path = format!("{}::{}", crate_name, path);
    }
    mk_isabelle_name(&path)
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

impl<'a, 'tcx: 'a> FnTranspiler<'a, 'tcx> {
    fn def_id(&self) -> DefId {
        self.tcx.map.local_def_id(self.node_id)
    }

    fn lvalue_name(&self, lv: &Lvalue) -> Option<String> {
        Some(match *lv {
            Lvalue::Var(idx) => format!("v_{}", self.mir.var_decls[idx as usize].name),
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
        self.mir.var_decls.iter().enumerate().map(|(idx, _)| Lvalue::Var(idx as u32))
            .chain(self.mir.temp_decls.iter().enumerate().map(|(idx, _)| Lvalue::Temp(idx as u32)))
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
            Lvalue::Var(idx) => self.mir.var_decls[idx as usize].ty,
            Lvalue::Temp(idx) => self.mir.temp_decls[idx as usize].ty,
            Lvalue::Arg(idx) => self.mir.arg_decls[idx as usize].ty,
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
            Lvalue::Temp(idx) => self.mir.var_decls.len() + idx as usize,
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

    fn transpile_def_id(&self, did: DefId) -> String {
        transpile_def_id(did, self.tcx, self.mod_transpiler.crate_name)
    }

    fn transpile_constval(&self, val: &ConstVal) -> TransResult {
        Ok(match *val {
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

    fn transpile_basic_block_rec(&self, bb: BasicBlock, comp: &mut Component<'a, 'tcx>) -> TransResult {
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

    fn is_marker_trait(&self, trait_def_id: DefId) -> bool {
        self.tcx.trait_items(trait_def_id).is_empty()
    }

    fn transpile_trait_ref(&self, trait_ref: &ty::TraitRef<'tcx>) -> TransResult {
        let substs: Result<Vec<_>,_> = trait_ref.substs.types.iter().map(|ty| {
            self.mod_transpiler.transpile_ty(ty).map(|s| mk_isabelle_name(&s))
        }).collect();
        Ok(try!(substs).into_iter().chain(iter::once(self.transpile_def_id(trait_ref.def_id))).join("_"))
    }

    fn transpile_trait_call(&self, caller: ast::NodeId, callee: DefId, substs: &Substs<'tcx>) -> TransResult {
        // FIXME ctxt::get_impl_method throws subst error
        fn get_impl_method_def_id<'tcx>(tcx: &ty::ctxt<'tcx>, impl_def_id: DefId, name: ast::Name) -> DefId {
            // there don't seem to be nicer accessors to these:
            let impl_or_trait_items_map = tcx.impl_or_trait_items.borrow();

            for impl_item in &tcx.impl_items.borrow()[&impl_def_id] {
                if let ty::MethodTraitItem(ref meth) =
                    impl_or_trait_items_map[&impl_item.def_id()] {
                        if meth.name == name {
                            return meth.def_id
                        }
                    }
            }

            // It is not in the impl - get the default from the trait.
            let trait_ref = tcx.impl_trait_ref(impl_def_id).unwrap();
            for trait_item in tcx.trait_items(trait_ref.def_id).iter() {
                if let &ty::MethodTraitItem(ref meth) = trait_item {
                    if meth.name == name {
                        return meth.def_id
                    }
                }
            }

            unreachable!()
        }

        use rustc::middle::infer;
        let trait_def_id = self.tcx.trait_of_item(callee).unwrap();

        // from trans::meth::trans_method_callee
        let trait_ref = substs.to_trait_ref(self.tcx, trait_def_id);
        let trait_ref = ty::Binder(trait_ref);

        let span = syntax::codemap::DUMMY_SP;
        let param_env = ty::ParameterEnvironment::for_item(self.tcx, caller);
        let bla = format!("{:?}", param_env.caller_bounds);
        let infcx = infer::new_infer_ctxt(self.tcx, &self.tcx.tables, Some(param_env));
        let mut selcx = SelectionContext::new(&infcx);
        let obligation =
            Obligation::new(ObligationCause::misc(span, ast::DUMMY_NODE_ID),
            trait_ref.to_poly_trait_predicate());
        let selection = match selcx.select(&obligation) {
            Ok(x) => x.unwrap(),
            Err(err) => throw!("obligation select: {:?} {:?} {:?}", obligation, err, bla),
        };

        match selection {
            Vtable::VtableImpl(data) => {
                // from trans::meth::trans_monomorphized_callee
                let impl_did = data.impl_def_id;
                let mname = match self.tcx.impl_or_trait_item(callee) {
                    ty::MethodTraitItem(method) => method.name,
                    _ => unreachable!(),
                };
                let method_def_id = get_impl_method_def_id(self.tcx, impl_did, mname);
                Ok(iter::once(self.transpile_def_id(method_def_id)).chain(try!(data.nested.into_iter().map(|obl| Ok(match obl.predicate {
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
                })).collect::<Result<Vec<_>, _>>()).into_iter().filter_map(|x| x)).join(" "))
            },
            Vtable::VtableParam(_) => {
                // FIXME very broken parameter lookup
                let param_trait_ref = try!(self.tcx.lookup_predicates(self.def_id()).predicates.into_iter().filter_map(|pred| match pred {
                    ty::Predicate::Trait(ref trait_pred) => {
                        let param_trait_ref = ty::Binder(trait_pred.skip_binder().trait_ref.clone());
                        if supertraits(self.tcx, param_trait_ref).any(|t| t.skip_binder().def_id == trait_ref.skip_binder().def_id) {
                            Some(param_trait_ref)
                        } else {
                            None
                        }
                    }
                    _ => None,
                }).next().ok_or_else(|| format!("param trait lookup failed for {:?}", trait_ref)));

                Ok(format!("{} {}", self.transpile_def_id(callee), try!(self.transpile_trait_ref(&param_trait_ref.skip_binder()))))
            }
            vtable => throw!("unimplemented: vtable {:?}", vtable),
        }
            /*let mut fulfill_cx = infcx.fulfillment_cx.borrow_mut();
              for obl in selection.nested_obligations() {
              fulfill_cx.register_predicate_obligation(&infcx, obl);
              }
              infer::drain_fulfillment_cx(&infcx, &mut fulfill_cx, &selection).map_err(|e| format!("obligation drain: {:?}", e));*/
    }

    fn transpile_basic_block(&self, bb: BasicBlock, comp: &mut Component<'a, 'tcx>) -> TransResult {
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

        let data = self.mir.basic_block_data(bb);
        let stmts = try!(data.statements.iter().map(|s| self.transpile_statement(s, comp)).collect::<Result<Vec<_>, _>>());
        let terminator = match data.terminator {
            Some(ref terminator) => Some(match *terminator {
                Terminator::Goto { target } =>
                    rec!(target),
                Terminator::If { ref cond, targets: (bb_if, bb_else) } =>
                    format!("if {} then {} else {}", try!(self.get_operand(cond)),
                    rec!(bb_if),
                    rec!(bb_else)),
                Terminator::Return => self.return_expr.clone(),
                Terminator::Call {
                    func: Operand::Constant(Constant { literal: Literal::Item { def_id, substs, .. }, .. }),
                    ref args, ref kind,
                } => {
                    let call = match self.tcx.trait_of_item(def_id) {
                        Some(trait_did) => try!(self.transpile_trait_call(self.node_id, def_id, substs)),
                        _ => self.transpile_def_id(def_id),
                    };
                    let args = try!(args.iter().map(|op| self.get_operand(op)).collect::<Result<Vec<_>, _>>());
                    let call = match self.tcx.adt_defs.borrow().get(&def_id) {
                        Some(ref adt_def) => throw!("Weird Adt call: {:?}", terminator),
                        None => format!("({} {})", call,
                                        args.into_iter().join(" "))
                    };
                    try!(self.set_lvalues(try!(self.call_return_dests(&terminator)).into_iter(), &call)) + &&rec!(kind.successors()[0])
                }
                Terminator::Call { .. } =>
                    throw!("unimplemented: call {:?}", data.terminator),
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
}

fn format_generic_ty(generics: &[String], ty: &str) -> String {
    match generics {
        [] => ty.to_string(),
        [ref ty_arg] => format!("{} {}", ty_arg, ty),
        _ => format!("({}) {}", generics.iter().join(", "), ty),
    }
}

struct ModuleTranspiler<'a, 'tcx: 'a> {
    crate_name: &'a str,
    tcx: &'a ty::ctxt<'tcx>,
    mir_map: &'a rustc_mir::mir_map::MirMap<'tcx>,
}

type TraitBounds = Vec<(String, String)>;

impl<'a, 'tcx> ModuleTranspiler<'a, 'tcx> {
    fn transpile_def_id(&self, did: DefId) -> String {
        transpile_def_id(did, self.tcx, self.crate_name)
    }

    fn transpile_generics(&self, generics: &hir::Generics, ty: &str) -> TransResult {
        Ok(format_generic_ty(&generics.ty_params.iter().map(|p| format!("'{}", p.name)).collect_vec()[..], ty))
    }

    fn transpile_ty(&self, ty: ty::Ty<'tcx>) -> TransResult {
        Ok(match ty.sty {
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
                match sig.output {
                    ty::FnOutput::FnConverging(out_ty) => {
                        format!("({} => {})", if inputs.is_empty() { "()".to_string() } else { inputs },
                                try!(iter::once(out_ty).chain(muts).map(|ty| self.transpile_ty(ty)).join_results(" × ")))
                    }
                    ty::FnOutput::FnDiverging => panic!("diverging function"),
                }
            },
            ty::TypeVariants::TyStruct(ref adt_def, ref substs) |
            ty::TypeVariants::TyEnum(ref adt_def, ref substs) => format_generic_ty(
                &try!(substs.types.get_slice(ParamSpace::TypeSpace).iter().map(|ty| self.transpile_ty(ty)).collect::<Result<Vec<_>, _>>()),
                &self.transpile_def_id(adt_def.did)
            ),
            ty::TypeVariants::TyRef(_, ref data) => try!(self.transpile_ty(data.ty)),
            ty::TypeVariants::TyParam(ref param) => format!("'{}", param.name),
            _ => match ty.ty_to_def_id() {
                Some(did) => self.transpile_def_id(did),
                None => throw!("unimplemented: ty {:?}", ty),
            }
        })
    }

    fn hir_ty_to_ty(&self, ty: &hir::Ty) -> ty::Ty<'tcx> {
        self.tcx.ast_ty_to_ty_cache.borrow()[&ty.id]
    }

    fn transpile_hir_ty(&self, ty: &hir::Ty) -> TransResult {
        self.transpile_ty(self.hir_ty_to_ty(ty))
    }

    fn transpile_fn(&self, id: ast::NodeId, decl: &FnDecl, name: &str, self_ty: Option<&hir::ExplicitSelf_>) -> TransResult {
        let param_names = try!(decl.inputs.iter().map(|param| {
            match param.pat.node {
                Pat_::PatIdent(BindingMode::BindByRef(hir::Mutability::MutMutable), _, _) =>
                   throw!("unimplemented: &mut param ({:?})", param),
                Pat_::PatIdent(_, ref ident, _) =>
                    Ok(ident.node.name.to_string()),
                _ => throw!("unimplemented: param pattern ({:?})", param),
            }
        }).collect::<Result<Vec<_>, _>>());
        let muts = decl.inputs.iter().zip(param_names.iter()).filter_map(|(param, name)| {
            if name == "self" {
                match *self_ty.unwrap() {
                    hir::ExplicitSelf_::SelfRegion(_, hir::Mutability::MutMutable, _) => Some(name.clone()),
                    hir::ExplicitSelf_::SelfExplicit(..) => panic!("unimplemented: explicit self"),
                    _ => None,
                }
            } else {
                try_unwrap_mut_ref(&self.hir_ty_to_ty(&param.ty)).map(|_| name.clone())
            }
        });
        let mir = &self.mir_map[&id];
        let trans = FnTranspiler {
            mod_transpiler: &self, node_id: id,
            tcx: self.tcx, mir: mir, param_names: &param_names,
            return_expr: format!("({})", iter::once("ret".to_string()).chain(muts).join(", ")),
        };
        let mut comp = try!(Component::new(&trans, START_BLOCK, mir.all_basic_blocks(), false));
        let body = try!(trans.transpile_basic_block(START_BLOCK, &mut comp));


        let trait_params = try!(self.tcx.lookup_predicates(trans.def_id()).predicates.into_iter().filter_map(|pred| match pred {
            ty::Predicate::Trait(ref trait_pred) if !trans.is_marker_trait(trait_pred.skip_binder().def_id()) =>
                Some(trans.transpile_trait_ref(&trait_pred.skip_binder().trait_ref)),
            _ => None
        }).collect::<Result<Vec<_>, _>>());

        let def = format!("definition {name} where\n\"{name} {param_names} = ({body})\"",
                    name=name,
                    param_names=trait_params.iter().chain(param_names.iter()).join(" "),
                    body=body,
        );
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

    fn transpile_associated_types(&self, trait_def_id: DefId, prefix: &str) -> Result<Vec<String>, String> {
        self.tcx.lookup_predicates(trait_def_id).predicates.into_iter().map(|pred| Ok(match pred {
            ty::Predicate::Trait(ty::Binder(ref trait_pred)) => {
                let trait_def = self.tcx.lookup_trait_def(trait_pred.def_id());
                let ty_param = mk_isabelle_name(&&try!(self.transpile_ty(trait_pred.self_ty())));
                trait_def.associated_type_names.iter().map(|name| format!("{}_{}", prefix, name)).chain(try!(self.transpile_associated_types(trait_pred.def_id(), &format!("{}_{}", prefix, ty_param)))).collect_vec()
            }
            _ => Vec::new()
        })).collect::<Result<Vec<_>, _>>().map(|v| v.into_iter().flat_map(|x| x).collect_vec())
    }

    fn transpile_trait(&self, f: &mut File, trait_def_id: DefId, generics: &hir::Generics, items: &[hir::TraitItem]) -> io::Result<()> {
        let trait_name = self.tcx.item_name(trait_def_id).to_string();
        println!("{}", trait_name);
        if items.is_empty() {
            return Ok(());
        }

        let fns = items.into_iter().filter_map(|item| match item.node {
            hir::TraitItem_::MethodTraitItem(_, _) => {
                Some(self.transpile_ty(self.tcx.node_id_to_type(item.id)).map(|ty| {
                    //let ty = ty.replace("'Self", "'a"); // oh well
                    format!("  {}__{} :: \"{}\"", trait_name, item.name, ty)
                }))
            }
            _ => None,
        }).join_results("\n");
        try!(try_write(f, &trait_name, fns.and_then(|fns| {
            self.transpile_associated_types(trait_def_id, "").map(|assoc_types| {
                format!("record {} =\n{}",
                        format_generic_ty(
                            &generics.ty_params.iter().map(|p| format!("'{}", p.name)).chain(assoc_types).collect_vec(),
                            &trait_name),
                        fns)
            })
        })));

        for item in items.into_iter() {
            match item.node {
                hir::TraitItem_::MethodTraitItem(ref sig, Some(_)) => {
                    let item_name = format!("{}__{}", trait_name, item.name);
                    try!(try_write(f, &item_name, self.transpile_fn(item.id, &*sig.decl, &item_name, Some(&sig.explicit_self.node))));
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn transpile_item(&self, item: &hir::Item, f: &mut File) -> io::Result<()> {
        let item_def_id = self.tcx.map.local_def_id(item.id);
        let name = format!("{}", self.transpile_def_id(item_def_id));
        match item.node {
            Item_::ItemFn(ref decl, _, _, _, _, _) =>
                try!(try_write(f, &name, self.transpile_fn(item.id, decl, &name, None))),
            Item_::ItemImpl(_, _, _, ref base_trait, _, ref items) => {
                for item in items {
                    let name = self.transpile_def_id(self.tcx.map.local_def_id(item.id));
                    match item.node {
                        hir::ImplItemKind::Method(ref sig, _) => {
                            let self_ty = match sig.explicit_self.node {
                                hir::ExplicitSelf_::SelfStatic => None,
                                ref ty => Some(ty),
                            };
                            try!(try_write(f, &name, self.transpile_fn(item.id, &sig.decl, &name, self_ty)))
                        }
                        _ => try!(write!(f, "(* unimplemented item type: {:?} *)\n\n", name)),
                    }
                }
                if !items.is_empty() {
                    if let &Some(ref base_trait) = base_trait {
                        try!(write!(f, "definition \"{} = \\<lparr>\n{}\n\\<rparr>\"\n\n", name, items.iter().map(|item| {
                            let trait_name = self.transpile_def_id(self.tcx.trait_ref_to_def_id(base_trait));
                            let name = self.transpile_def_id(self.tcx.map.local_def_id(item.id));
                            format!("  {}_{} = {}", trait_name, item.name, name)
                        }).join(",\n")));
                    }
                }
            }
            Item_::ItemExternCrate(..) | Item_::ItemUse(..) => (),
            Item_::ItemMod(ref module) =>
                try!(self.transpile_module(f, module)),
            Item_::ItemStruct(ref data, ref generics) =>
                try!(try_write(f, &name, self.transpile_struct(&name, data, generics))),
            Item_::ItemTrait(_, ref generics, _, ref items) =>
                try!(self.transpile_trait(f, item_def_id, generics, items)),
            _ => try!(write!(f, "(* unimplemented item type: {:?} *)\n\n", name)),
        };
        Ok(())
    }

    fn transpile_module(&self, f: &mut File, module: &hir::Mod) -> io::Result<()> {
        for item_id in module.item_ids.iter() {
            try!(self.transpile_item(self.tcx.map.expect_item(item_id.id), f));
        }
        Ok(())
    }
}

struct DepsCollector<'a, 'tcx: 'a> {
    tcx: &'a ty::ctxt<'tcx>,
    deps: HashSet<DefId>,
}

impl<'a, 'tcx> rustc_front::intravisit::Visitor<'a> for DepsCollector<'a, 'tcx> {
    fn visit_item(&mut self, item: &'a hir::Item) {
        match item.node {
            Item_::ItemUse(ref path) => {
                let node_id = match path.node {
                    hir::ViewPath_::ViewPathList(_, ref list) => list[0].node.id(),
                    _ => item.id,
                };
                let did = self.tcx.def_map.borrow()[&node_id].def_id();
                if !did.is_local() {
                    self.deps.insert(did);
                }
            }
            _ => {}
        }
    }
}

fn transpile_crate(state: &driver::CompileState) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    let crate_name = state.crate_name.unwrap();

    println!("Building MIR...");
    let trans = ModuleTranspiler {
        crate_name: crate_name,
        tcx: tcx,
        mir_map: &build_mir_for_crate(tcx),
    };

    println!("Transpiling...");
    let deps = {
        let mut deps_collector = DepsCollector { tcx: tcx, deps: HashSet::new() };
        state.hir_crate.unwrap().visit_all_items(&mut deps_collector);
        let mut deps: Vec<String> = deps_collector.deps.into_iter().map(|did| format!("{}_export", tcx.def_path(did)[0].data.to_string())).collect();
        deps.sort();
        if path::Path::new("thys").join(format!("{}_pre.thy", crate_name)).exists() {
            deps.insert(0, format!("{}_pre", crate_name));
        }
        deps
    };

    let mut f = try!(File::create(path::Path::new("thys").join(format!("{}_export.thy", crate_name))));
    try!(write!(f, "theory {}_export\nimports\n{}\nbegin\n\n", crate_name,
                deps.into_iter().map(|file| format!("  {}", file)).join("\n")));

    try!(trans.transpile_module(&mut f, &state.hir_crate.unwrap().module));

    write!(f, "end\n")
}
