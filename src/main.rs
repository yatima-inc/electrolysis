#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(slice_patterns)]
#![feature(path_relative_from)]

macro_rules! throw { ($($arg: tt)*) => { return Err(format!($($arg)*)) } }

extern crate itertools;
extern crate petgraph;

#[macro_use]
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_front;
extern crate rustc_mir;
extern crate syntax;
extern crate rustc_trans;

mod component;
mod mir_graph;
mod traits;

use std::collections::HashMap;
use std::env;
use std::io;
use std::io::prelude::*;
use std::iter;
use std::fs::File;
use std::path;

use itertools::Itertools;

use syntax::ast;
use rustc_front::hir;
use rustc_front::hir::{Path, FnDecl, Pat_, BindingMode, FunctionRetTy, Item, Item_};
use rustc_mir::mir_map::build_mir_for_crate;
use rustc_mir::repr::*;
use rustc::middle::const_eval::ConstVal;
use rustc::middle::def_id::DefId;
use rustc::middle::subst::ParamSpace;
use rustc::middle::ty;
use rustc::middle::ty::HasTypeFlags;

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

fn main() {
    let krate = env::args().nth(1).unwrap();
    let crate_name = env::args().nth(2).unwrap();
    let sess = session::build_session(
        session::config::Options {
            crate_name: Some(crate_name),
            crate_types: vec![session::config::CrateType::CrateTypeRlib],
            maybe_sysroot: Some(path::PathBuf::from("/usr/local")),
            unstable_features: syntax::feature_gate::UnstableFeatures::Allow,
            .. session::config::basic_options()
        },
        Some(path::PathBuf::from(&krate)),
        diagnostics::registry::Registry::new(&rustc::DIAGNOSTICS)
    );
    let cfg = session::config::build_configuration(&sess);
    println!("Compiling up to MIR...");
    driver::compile_input(sess, cfg,
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
        BinOp::Ne => "!=",
        BinOp::Ge => ">=",
        BinOp::Gt => ">",
    }
}

pub struct FnTranspiler<'a, 'tcx: 'a> {
    crate_name: &'a str,
    fn_name: String,
    tcx: &'a ty::ctxt<'tcx>,
    mir: &'a Mir<'tcx>,
    param_names: &'a Vec<String>,
}

fn selector(idx: usize, len: usize) -> Vec<&'static str> {
    iter::repeat("_").take(idx)
        .chain(iter::once("x"))
        .chain(iter::repeat("_").take(len - idx - 1))
        .collect()
}

fn transpile_def_id(did: DefId, tcx: &ty::ctxt, crate_name: &str) -> String {
    // what could ever go wrong
    let mut path = tcx.item_path_str(did);
    if did.is_local() {
        path = format!("{}::{}", crate_name, path);
    }
    path.replace("::", "_").replace("<", "_").replace(">", "_").replace(".", "_")
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
    fn lvalue_name(&self, lv: &Lvalue) -> Option<String> {
        Some(match *lv {
            Lvalue::Var(idx) => format!("{}", self.mir.var_decls[idx as usize].name),
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
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(Field::Named(ref name)) }) =>
                match unwrap_refs(try!(self.lvalue_ty(base))).sty {
                    ty::TypeVariants::TyStruct(ref adt_def, _) =>
                        Ok(format!("({}.{} {})", self.transpile_def_id(adt_def.did), name, try!(self.get_lvalue(base)))),
                    ref ty => throw!("unimplemented: accessing field of {:?}", ty),
                },
            Lvalue::Projection(box Projection {
                elem: ProjectionElem::Field(Field::Indexed(idx)),
                base: Lvalue::Projection(box Projection {
                    ref base,
                    elem: ProjectionElem::Downcast(ref adt_def, variant_idx),
                }),
            }) => {
                let variant = &adt_def.variants[variant_idx];
                Ok(format!("(case {lv} of {variant} {args} => x)",
                           lv=try!(self.get_lvalue(base)),
                           variant=self.transpile_def_id(variant.did),
                           args=selector(idx, variant.fields.len()).join(" ")))
            }
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
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(Field::Named(ref name)) }) => {
                let ty = try!(self.lvalue_ty(base));
                match ty.sty {
                     ty::TypeVariants::TyStruct(ref adt_def, ref substs) =>
                         adt_def.struct_variant().fields.iter().find(|f| &f.name == name).unwrap().ty(self.tcx, substs),
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
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(Field::Named(ref name)) }) => {
                let base_name = try!(self.lvalue_name(base).ok_or_else(|| format!("ugh, nested fields assignments? {:?}", lv)));
                match unwrap_refs(try!(self.lvalue_ty(base))).sty {
                    ty::TypeVariants::TyStruct(ref adt_def, _) =>
                        Ok(format!("let {} = {} \\<lparr> {}.{} := {} \\<rparr> in\n", base_name, base_name, self.transpile_def_id(adt_def.did), name, val)),
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
        transpile_def_id(did, self.tcx, self.crate_name)
    }

    fn get_operand(&self, op: &Operand<'tcx>) -> TransResult {
        Ok(match *op {
            Operand::Consume(ref lv) => try!(self.get_lvalue(lv)),
            Operand::Constant(ref c) => match c.literal {
                Literal::Value { value: ConstVal::Uint(i) } => i.to_string(),
                Literal::Value { .. } => throw!("unimplemented: literal {:?}", op),
                Literal::Item { def_id, substs }  => {
                    match self.tcx.trait_of_item(def_id) {
                        Some(trait_did) if !substs.has_param_types() =>
                            self.transpile_def_id(try!(traits::lookup_trait_item_impl(self.tcx, def_id, substs))),
                        _ => self.transpile_def_id(def_id),
                    }
                }
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
                Ok(format!("({} {})", self.transpile_def_id(variant.did), ops.iter().join(" ")))
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

    fn call_return_dests<'b>(&self, call: &'b CallData<'tcx>) -> Result<Vec<&'b Lvalue<'tcx>>, String> {
        let args_with_tys = try!(call.args.iter().map(|lv| {
            self.lvalue_ty(lv).map(|ty| (lv, ty))
        }).collect::<Result<Vec<_>, _>>());
        let muts = args_with_tys.into_iter().filter(|&(_, ty)| {
            try_unwrap_mut_ref(&ty).is_some()
        }).map(|(lv, _)| lv);
        Ok(iter::once(&call.destination).chain(muts).collect())
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
            let name = format!("{}_{}", self.fn_name, bb.index());
            if l_comp.exits.len() != 1 {
                throw!("Oops, multiple loop exits: {:?}", l_comp);
            }
            comp.prelude = format!("{}

definition {name} where \"{name} {uses} = (\\<lambda>({defs}). {body})\"",
                                   comp.prelude,
                                   name=name,
                                   uses=l_comp.nonlocal_uses.iter().join(" "),
                                   defs=l_comp.nonlocal_defs.iter().join(", "),
                                   body=body);
            return Ok(format!("let ({muts}) = loop ({name} {immuts}) ({muts}) in\n{cont}", muts=l_comp.nonlocal_defs.iter().join(", "),
                              name=name, immuts=l_comp.nonlocal_uses.iter().join(" "), cont=rec!(l_comp.exits[0])));
        }

        let data = self.mir.basic_block_data(bb);
        let stmts = try!(data.statements.iter().map(|s| self.transpile_statement(s, comp)).collect::<Result<Vec<_>, _>>());
        let terminator = match data.terminator {
            Terminator::Goto { target } =>
                rec!(target),
            Terminator::Panic { .. } => format!("panic"),
            Terminator::If { ref cond, ref targets } =>
                format!("if {} then {} else {}", try!(self.get_operand(cond)),
                rec!(targets[0]),
                rec!(targets[1])),
            Terminator::Return => format!("ret"),
            Terminator::Call { ref data, ref targets } => {
                let call = format!("({} {})", try!(self.get_lvalue(&data.func)),
                                   try!(data.args.iter().map(|lv| self.get_lvalue(lv)).join_results(" ")));
                try!(self.set_lvalues(try!(self.call_return_dests(data)).into_iter(), &call)) + &&rec!(targets[0])
            },
            Terminator::Switch { ref discr, ref targets } =>
                match try!(self.lvalue_ty(discr)).sty {
                    ty::TypeVariants::TyEnum(ref adt_def, _) => {
                        let arms: TransResult = adt_def.variants.iter().zip(targets).map(|(var, &target)| {
                            Ok(format!("{} {} => {}", self.transpile_def_id(var.did),
                            iter::repeat("_").take(var.fields.len()).join(" "),
                            rec!(target)))
                        }).join_results(" | ");
                        format!("case {} of {}", try!(self.get_lvalue(discr)), try!(arms))
                    }
                    _ => throw!("unimplemented: switch on {:?}", discr),
                },
            Terminator::Diverge => unreachable!(),
        };
        Ok(stmts.into_iter().chain(iter::once(terminator)).join(""))
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
    input: &'a path::Path,
    crate_name: &'a str,
    tcx: &'a ty::ctxt<'tcx>,
    mir_map: &'a rustc_mir::mir_map::MirMap<'tcx>,
}

type TraitBounds = HashMap<String, Vec<String>>;

impl<'a, 'tcx> ModuleTranspiler<'a, 'tcx> {
    fn transpile_def_id(&self, did: DefId) -> String {
        transpile_def_id(did, self.tcx, self.crate_name)
    }

    fn transpile_generics(&self, generics: &hir::Generics, ty: &str) -> TransResult {
        Ok(format!("({}) {}", generics.ty_params.iter().map(|p| format!("'{}", p.name)).join(", "), ty))
    }

    fn bounds_from_param_bounds(&self, bounds: &mut TraitBounds, name: String, param_bounds: &[hir::TyParamBound]) {
        for bound in param_bounds {
            match *bound {
                hir::TyParamBound::TraitTyParamBound(ref poly_trait_ref, hir::TraitBoundModifier::None) => {
                    let trait_ref = self.transpile_def_id(self.tcx.trait_ref_to_def_id(&poly_trait_ref.trait_ref));
                    bounds.entry(name.clone()).or_insert_with(|| Vec::new()).push(trait_ref)
                }
                _ => ()
            }
        }
    }

    fn bounds_from_generics(&self, bounds: &mut TraitBounds, generics: &hir::Generics) {

        for p in &generics.where_clause.predicates {
            match p {
                &hir::WherePredicate::BoundPredicate(ref pred) => match unwrap_refs(self.hir_ty_to_ty(&pred.bounded_ty)).sty {
                    ty::TypeVariants::TyParam(ref param) => self.bounds_from_param_bounds(bounds, param.name.to_string(), &pred.bounds),
                    _ => println!("unimplemented: non-atomic type bound {:?}", pred)
                },
                _ => (),
            }
        }
        for param in &generics.ty_params {
            self.bounds_from_param_bounds(bounds, param.name.to_string(), &param.bounds);
        }
    }

    fn transpile_ty(&self, ty: ty::Ty<'tcx>, bounds: &TraitBounds) -> TransResult {
        Ok(match ty.sty {
            ty::TypeVariants::TyUint(ref ty) => ty.to_string(),
            ty::TypeVariants::TyInt(ref ty) => ty.to_string(),
            ty::TypeVariants::TyFloat(ref ty) => ty.to_string(),
            ty::TypeVariants::TyTuple(ref tys) => match &tys[..] {
                [] => "unit".to_string(),
                _ => format!("({})", try!(tys.iter().map(|ty| self.transpile_ty(ty, bounds)).join_results(" × "))),
            },
            ty::TypeVariants::TyBareFn(_, ref data) => {
                let sig = data.sig.skip_binder();
                let muts = sig.inputs.iter().filter_map(try_unwrap_mut_ref);
                let inputs = try!(sig.inputs.iter().map(|ty| self.transpile_ty(ty, bounds)).join_results(" => "));
                match sig.output {
                    ty::FnOutput::FnConverging(out_ty) => {
                        format!("({} => {})", if inputs.is_empty() { "()".to_string() } else { inputs },
                                try!(iter::once(out_ty).chain(muts).map(|ty| self.transpile_ty(ty, bounds)).join_results(" × ")))
                    }
                    ty::FnOutput::FnDiverging => panic!("diverging function"),
                }
            },
            ty::TypeVariants::TyStruct(ref adt_def, ref substs) |
            ty::TypeVariants::TyEnum(ref adt_def, ref substs) => format_generic_ty(
                &try!(substs.types.get_slice(ParamSpace::TypeSpace).iter().map(|ty| self.transpile_ty(ty, bounds)).collect::<Result<Vec<_>, _>>()),
                &self.transpile_def_id(adt_def.did)
            ),
            ty::TypeVariants::TyRef(_, ref data) => try!(self.transpile_ty(data.ty, bounds)),
            ty::TypeVariants::TyParam(ref param) => {
                match &bounds.get(&param.name.to_string()).into_iter().flat_map(|v| v.iter()).collect::<Vec<_>>()[..] {
                    [] => format!("'{}", param.name),
                    [ref bound] => format!("'{}::{}", param.name, bound),
                    bounds => format!("'{}::{{{}}}", param.name, bounds.iter().join(",")),
                }
            }
            _ => match ty.ty_to_def_id() {
                Some(did) => self.transpile_def_id(did),
                None => throw!("unimplemented: ty {:?}", ty),
            }
        })
    }

    fn hir_ty_to_ty(&self, ty: &hir::Ty) -> ty::Ty<'tcx> {
        self.tcx.ast_ty_to_ty_cache.borrow()[&ty.id]
    }

    fn transpile_hir_ty(&self, ty: &hir::Ty, bounds: &TraitBounds) -> TransResult {
        self.transpile_ty(self.hir_ty_to_ty(ty), bounds)
    }

    fn transpile_fn(&self, id: ast::NodeId, decl: &FnDecl, name: &str, bounds: &TraitBounds, self_ty: Option<&hir::Ty>) -> TransResult {
        let params = try!(decl.inputs.iter().map(|param| {
            let ty = match param.ty.node {
                hir::Ty_::TyInfer => self_ty.unwrap(),
                _ => &*param.ty,
            };
            match param.pat.node {
                Pat_::PatIdent(BindingMode::BindByRef(hir::Mutability::MutMutable), _, _) =>
                   throw!("unimplemented: &mut param ({:?})", param),
                Pat_::PatIdent(_, ref ident, _) =>
                    Ok((ident.node.name.as_str().to_string(), ty)),
                _ => throw!("unimplemented: param pattern ({:?})", param),
            }
        }).collect::<Result<Vec<_>, _>>());
        let (param_names, param_types): (Vec<_>, Vec<_>) = params.into_iter().unzip();

        let return_ty = match decl.output {
            FunctionRetTy::DefaultReturn(_) => "()".to_string(),
            FunctionRetTy::Return(ref ty) => try!(self.transpile_hir_ty(&**ty, bounds)),
            FunctionRetTy::NoReturn(_) => throw!("no-return fn"),
        };
        let mir = &self.mir_map[&id];
        let trans = FnTranspiler {
            crate_name: self.crate_name, fn_name: name.to_string(),
            tcx: self.tcx, mir: mir, param_names: &param_names,
        };
        let mut comp = try!(Component::new(&trans, START_BLOCK, mir.all_basic_blocks(), false));
        let body = try!(trans.transpile_basic_block(START_BLOCK, &mut comp));


        Ok(format!("{prelude}

definition {name} :: \"{param_types} => {return_ty}\" where
\"{name} {param_names} = ({body})\"",
                    prelude=comp.prelude,
                    name=name,
                    param_types=try!(param_types.iter().map(|ty| self.transpile_hir_ty(ty, bounds)).join_results(" => ")),
                    return_ty=return_ty,
                    param_names=param_names.iter().join(" "),
                    body=body,
        ))
    }

    fn transpile_struct(&self, name: &str, data: &hir::VariantData, generics: &hir::Generics) -> TransResult {
        match *data {
            hir::VariantData::Struct(ref fields, _) => {
                let fields: TransResult = fields.iter().map(|f| {
                    Ok(format!("  \"{}\" :: {}", f.node.name().unwrap(),
                               try!(self.transpile_hir_ty(&*f.node.ty, &HashMap::new()))))
                }).join_results("\n");
                Ok(format!("record {} =\n{}",
                           try!(self.transpile_generics(generics, name)), try!(fields)))
            }
            _ => throw!("unimplemented: struct {:?}", data)
        }
    }

    fn transpile_trait(&self, name: &str, bounds: &TraitBounds, items: &[syntax::ptr::P<hir::TraitItem>]) -> TransResult {
        //let self_bounds = match &bounds.keys().collect::<Vec<_>>()[..] {
        //    &[] => vec![],
        //    &[param] | param.to_string == "Self" => bounds[param].clone(),
        //    _ => throw!("unimplemented: parameterized trait"),
        //};
        //let mut bounds = TraitBounds::new();
        //bounds.insert(
        Ok(format!("class {} =\n{}\n\n", name, try!(items.into_iter().map(|item| {
            match item.node {
                hir::TraitItem_::MethodTraitItem(_, None) => {
                    let ty = try!(self.transpile_ty(self.tcx.node_id_to_type(item.id), bounds));
                    let ty = ty.replace("'Self", "'a"); // oh well
                    Ok(format!("fixes {} :: \"{}\"", item.name, ty))
                }
                _ => throw!("unimplemented: trait item {:?}", item),
            }
        }).join_results("\n"))))
    }

    fn transpile_item(&self, item: &hir::Item, path: &path::Path, f: &mut File) -> io::Result<()> {
        fn try_write(f: &mut File, name: &str, res: TransResult) -> io::Result<()> {
            match res {
                Ok(trans) => try!(write!(f, "{}\n\n", trans)),
                Err(err) => try!(write!(f, "(* {}: {} *)\n\n", name, err.replace("(*", "( *"))),
            };
            Ok(())
        }

        let name = format!("{}", self.transpile_def_id(self.tcx.map.local_def_id(item.id)));
        let mut bounds = TraitBounds::new();
        match item.node {
            Item_::ItemFn(ref decl, _, _, _, ref generics, _) => {
                self.bounds_from_generics(&mut bounds, generics);
                try!(try_write(f, &name, self.transpile_fn(item.id, decl, &name, &bounds, None)))
            }
            Item_::ItemImpl(_, _, ref generics, _, ref self_ty, ref items) =>
                for item in items {
                    bounds.clear();
                    self.bounds_from_generics(&mut bounds, generics);
                    let name = format!("{}", self.transpile_def_id(self.tcx.map.local_def_id(item.id)));

                    match item.node {
                        hir::ImplItem_::MethodImplItem(ref sig, _) => {
                            self.bounds_from_generics(&mut bounds, &sig.generics);

                            let self_ty = match sig.explicit_self.node {
                                hir::ExplicitSelf_::SelfStatic => None,
                                _ => Some(&**self_ty),
                            };
                            try!(try_write(f, &name, self.transpile_fn(item.id, &sig.decl, &name, &bounds,
                                                                       self_ty)))
                        }
                        _ => try!(write!(f, "(* unimplemented item type: {:?} *)\n\n", name)),
                    }
                },
            Item_::ItemExternCrate(..) | Item_::ItemUse(..) => (),
            Item_::ItemMod(ref module) => {
                let mod_path = &self.tcx.sess.codemap().span_to_filename(module.inner);
                let mod_path = path::Path::new(mod_path);
                if mod_path == path {
                    for item in module.items.iter() {
                        try!(self.transpile_item(item, path, f));
                    }
                } else {
                    try!(self.transpile_module(module));
                }
            },
            Item_::ItemStruct(ref data, ref generics) =>
                try!(try_write(f, &name, self.transpile_struct(&name, data, generics))),
            Item_::ItemTrait(_, ref generics, ref param_bounds, ref items) => {
                let mut bounds = TraitBounds::new();
                self.bounds_from_generics(&mut bounds, generics);
                self.bounds_from_param_bounds(&mut bounds, "Self".to_string(), param_bounds);
                try!(try_write(f, &name, self.transpile_trait(&name, &bounds, items)))
            }
            _ => try!(write!(f, "(* unimplemented item type: {:?} *)\n\n", name)),
        };
        Ok(())
    }

    fn transpile_module(&self, module: &hir::Mod) -> io::Result<()> {
        let p = &self.tcx.sess.codemap().span_to_filename(module.inner);
        let p = path::Path::new(p);
        let base = self.input.parent().unwrap();
        let new_path = path::Path::new("export").join(self.crate_name).join(p.relative_from(base).unwrap()).with_extension("thy");
        std::fs::create_dir_all(new_path.parent().unwrap()).unwrap();
        let mut f = try!(File::create(&new_path));
        try!(write!(f, "theory {}
imports \"../../Rustabelle\"
begin

", p.file_stem().unwrap().to_str().unwrap()));

        for item in module.items.iter() {
            try!(self.transpile_item(item, &p, &mut f));
        }

        try!(write!(f, "end\n"));
        Ok(())
    }
}

fn transpile_crate(state: &driver::CompileState) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    println!("Building MIR...");
    let trans = ModuleTranspiler {
        input: match *state.input {
            session::config::Input::File(ref p) => p,
            _ => panic!("A file would be nice."),
        },
        crate_name: state.crate_name.unwrap(),
        tcx: tcx,
        mir_map: &build_mir_for_crate(tcx),
    };
    println!("Transpiling...");
    trans.transpile_module(&state.hir_crate.unwrap().module)
}
