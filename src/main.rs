#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(slice_patterns)]

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
use rustc_front::hir::{Crate, Path, FnDecl, Pat_, BindingMode, FunctionRetTy, Item, Item_, Ty_};
use rustc_front::print::pprust;
use rustc_mir::mir_map::build_mir_for_crate;
use rustc_mir::repr::*;
use rustc::middle::const_eval::ConstVal;
use rustc::middle::def_id::DefId;
use rustc::middle::ty;

use rustc_driver::driver;
use syntax::diagnostics;
use rustc::session;

use component::Component;
use mir_graph::mir_sccs;

type TransResult = Result<String, String>;

fn main() {
    let krate = env::args().nth(1).unwrap();
    let sess = session::build_session(
        session::config::Options {
            crate_types: vec![session::config::CrateType::CrateTypeRlib],
            maybe_sysroot: Some(path::PathBuf::from("/usr/local")),
            unstable_features: syntax::feature_gate::UnstableFeatures::Allow,
            .. session::config::basic_options()
        },
        Some(path::PathBuf::from(&krate)),
        diagnostics::registry::Registry::new(&rustc::DIAGNOSTICS)
    );
    let cfg = session::config::build_configuration(&sess);
    driver::compile_input(sess, cfg,
        &session::config::Input::File(path::PathBuf::from(&krate)),
        &None, &None, None, driver::CompileController {
            after_analysis: driver::PhaseController {
                stop: rustc_driver::Compilation::Stop,
                callback: Box::new(|state| {
                    transpile_crate(state.hir_crate.unwrap(), state.tcx.unwrap()).unwrap();
                }),
            },
            .. driver::CompileController::basic()
        }
    );
}

fn transpile_path(path: &Path) -> String {
    // what could ever go wrong
    pprust::path_to_string(path).replace("::", "_")
}

fn transpile_hir_ty(ty: &hir::Ty) -> String {
    match ty.node {
        Ty_::TyPath(None, ref path) => transpile_path(path),
        _ => panic!("unimplemented: type {:?}", ty),
    }
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

fn transpile_def_id(did: DefId, tcx: &ty::ctxt) -> String {
    // what could ever go wrong
    tcx.item_path_str(did).replace("::", "_").replace("<", "_").replace(">", "_").replace(".", "_")
}

impl<'a, 'tcx: 'a> FnTranspiler<'a, 'tcx> {
    fn lvalue_name(&self, lv: &Lvalue) -> String {
        match *lv {
            Lvalue::Var(idx) => format!("{}", self.mir.var_decls[idx as usize].name),
            Lvalue::Temp(idx) => format!("t_{}", idx),
            Lvalue::Arg(idx) => self.param_names[idx as usize].clone(),
            Lvalue::ReturnPointer => "ret".to_string(),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.lvalue_name(base),
            _ => panic!("unimplemented: naming {:?}", lv)
        }
    }

    fn locals(&self) -> Vec<Lvalue> {
        self.mir.var_decls.iter().enumerate().map(|(idx, _)| Lvalue::Var(idx as u32))
            .chain(self.mir.temp_decls.iter().enumerate().map(|(idx, _)| Lvalue::Temp(idx as u32)))
            .chain(iter::once(Lvalue::ReturnPointer))
            .collect()
    }

    fn num_locals(&self) -> usize { self.locals().len() }

    fn get_lvalue(&self, lv: &Lvalue) -> String {
        match *lv {
            Lvalue::Var(_) | Lvalue::Temp(_) | Lvalue::Arg(_) => self.lvalue_name(lv),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.get_lvalue(base),
            Lvalue::Projection(box Projection {
                elem: ProjectionElem::Field(Field::Indexed(idx)),
                base: Lvalue::Projection(box Projection {
                    ref base,
                    elem: ProjectionElem::Downcast(ref adt_def, variant_idx),
                }),
            }) => {
                let variant = &adt_def.variants[variant_idx];
                format!("(case {lv} of {variant} {args} => x)",
                      lv=self.get_lvalue(base),
                      variant=self.transpile_def_id(variant.did),
                      args=selector(idx, variant.fields.len()).join(" "))
            }
            _ => panic!("unimplemented: loading {:?}", lv)
        }
    }

    fn lvalue_ty(&self, lv: &Lvalue) -> &ty::Ty {
        match *lv {
            Lvalue::Var(idx) => &self.mir.var_decls[idx as usize].ty,
            Lvalue::Temp(idx) => &self.mir.temp_decls[idx as usize].ty,
            Lvalue::Arg(idx) => &self.mir.arg_decls[idx as usize].ty,
            _ => panic!("unimplemented: type of {:?}", lv)
        }
    }

    fn lvalue_idx(&self, lv: &Lvalue) -> usize {
        match *lv {
            Lvalue::Var(idx) => idx as usize,
            Lvalue::Temp(idx) => self.mir.var_decls.len() + idx as usize,
            Lvalue::ReturnPointer => self.num_locals() - 1,
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.lvalue_idx(base),
            _ => panic!("unimplemented: storing {:?}", lv)
        }
    }

    fn set_lvalue(&self, lv: &Lvalue, val: &str) -> String {
        format!("let {} = {} in\n", self.lvalue_name(lv), val)
    }

    fn set_lvalues<'b, It: Iterator<Item=&'b Lvalue<'tcx>>>(&self, lvs: It, val: &str) -> String
        where 'tcx: 'b {
        format!("let ({}) = {} in\n",
                lvs.map(|lv| self.lvalue_name(lv)).join(", "),
                val)
    }

    fn transpile_def_id(&self, did: DefId) -> String {
        transpile_def_id(did, self.tcx)
    }

    fn try_unwrap_mut_ref(ty: &ty::Ty<'tcx>) -> Option<ty::Ty<'tcx>> {
        match ty.sty {
            ty::TypeVariants::TyRef(_, ty::TypeAndMut { mutbl: hir::Mutability::MutMutable, ty }) =>
                Some(ty),
            _ => None
        }
    }

    fn transpile_ty(&self, ty: ty::Ty) -> String {
        match ty.sty {
            ty::TypeVariants::TyUint(ast::UintTy::TyU32) => "u32".to_string(),
            ty::TypeVariants::TyTuple(ref tys) => match &tys[..] {
                [] => "unit".to_string(),
                _ => format!("({})", tys.iter().map(|ty| self.transpile_ty(ty)).join(" × ")),
            },
            ty::TypeVariants::TyBareFn(_, ref data) => {
                let sig = data.sig.skip_binder();
                let muts = sig.inputs.iter().filter_map(FnTranspiler::try_unwrap_mut_ref);
                match sig.output {
                    ty::FnOutput::FnConverging(out_ty) => {
                        format!("({} => {})", sig.inputs.iter().map(|ty| self.transpile_ty(ty)).join(" => "),
                                iter::once(out_ty).chain(muts).map(|ty| self.transpile_ty(ty)).join(" × "))
                    }
                    ty::FnOutput::FnDiverging => panic!("diverging function"),
                }
            },
            ty::TypeVariants::TyStruct(ref adt_def, _) =>
                self.transpile_def_id(adt_def.did),
            ty::TypeVariants::TyEnum(ref adt_def, _) =>
                self.transpile_def_id(adt_def.did),
            ty::TypeVariants::TyRef(_, ref data) => self.transpile_ty(data.ty),
            _ => match ty.ty_to_def_id() {
                Some(did) => self.transpile_def_id(did),
                None => panic!("unimplemented: {:?}", ty),
            }
        }
    }

    fn get_operand(&self, op: &Operand<'tcx>) -> String {
        match *op {
            Operand::Consume(ref lv) => self.get_lvalue(lv),
            Operand::Constant(ref c) => match c.literal {
                Literal::Value { value: ConstVal::Uint(i) } => i.to_string(),
                Literal::Value { .. } => panic!("unimplemented: {:?}", op),
                Literal::Item { def_id, substs }  => {
                    if let Some(method_did) = traits::lookup_trait_item_impl(self.tcx, def_id, substs) {
                        self.transpile_def_id(method_did)
                    } else {
                        self.transpile_def_id(def_id)
                    }
                }
            }
        }
    }

    fn get_rvalue(&self, rv: &Rvalue<'tcx>) -> String {
        match *rv {
            Rvalue::Use(ref op) => self.get_operand(op),
            Rvalue::BinaryOp(op, ref o1, ref o2) =>
                format!("({} {} {})", self.get_operand(o1), binop_to_string(op),
                        self.get_operand(o2)),
            Rvalue::Ref(_, BorrowKind::Shared, ref lv) => self.get_lvalue(lv),
            Rvalue::Ref(_, BorrowKind::Mut, ref lv) => self.get_lvalue(lv),
            Rvalue::Aggregate(AggregateKind::Adt(ref adt_def, variant_idx, _), ref ops) => {
                let variant = &adt_def.variants[variant_idx];
                format!("({} {})", self.transpile_def_id(variant.did),
                        ops.iter().map(|op| self.get_operand(op)).join(" "))
            }
            _ => panic!("unimplemented: {:?}", rv),
        }
    }

    fn transpile_statement(&self, stmt: &Statement<'tcx>, comp: &mut Component) -> String {
        match stmt.kind {
            StatementKind::Assign(ref lv, Rvalue::Ref(_, BorrowKind::Mut, ref lsource)) => {
                comp.refs.insert(self.lvalue_idx(lv), self.get_lvalue(lsource));
                self.set_lvalue(lv, &self.get_lvalue(lsource))
                //format!("let ({lv}, {lsource}) = ({lsource}, undefined) in\n", lv=self.get_lvalue(lv), lsource=self.get_lvalue(lsource))
            }
            StatementKind::Assign(ref lv, ref rv) => {
                if *lv != Lvalue::ReturnPointer && self.lvalue_ty(lv).is_nil() {
                    // optimization/rustc_mir workaround: don't save '()'
                    "".to_string()
                } else {
                    self.set_lvalue(lv, &self.get_rvalue(rv))
                }
            }
            StatementKind::Drop(DropKind::Deep, ref lv) => {
                //match comp.refs.get(&self.lvalue_idx(lv)) {
                //    Some(lsource) => format!("let ({lsource}, {lv}) = ({lv}, undefined) in\n", lsource=lsource, lv=self.get_lvalue(lv)),
                //    None => self.set_lvalue(lv, "undefined")
                //}
                match comp.refs.get(&self.lvalue_idx(lv)) {
                    Some(lsource) => format!("let {} = {} in\n", lsource, self.get_lvalue(lv)),
                    None => "".to_string()
                }
            }
            _ => panic!("unimplemented: {:?}", stmt),
        }
    }

    fn transpile_basic_block_rec(&self, bb: BasicBlock, comp: &mut Component) -> String {
        if comp.header == Some(bb) {
            format!("(({}), True)", comp.nonlocal_defs.iter().join(", "))
        } else {
            self.transpile_basic_block(bb, comp)
        }
    }

    fn transpile_basic_block(&self, bb: BasicBlock, comp: &mut Component) -> String {
        macro_rules! rec { ($bb:expr) => { self.transpile_basic_block_rec($bb, comp) } }

        if !comp.blocks.contains(&bb) {
            comp.exits.push(bb);
            return format!("(({}), False)", comp.nonlocal_defs.iter().join(", "));
        }
        if let Some(l) = comp.loops.clone().into_iter().find(|l| l.contains(&bb)) {
            let mut l_comp = Component::new(self, bb, l, true);
            let body = self.transpile_basic_block(bb, &mut l_comp);
            let name = format!("{}_{}", self.fn_name, bb.index());
            assert!(l_comp.exits.len() == 1);
            comp.prelude = format!("{}

definition {name} where \"{name} {uses} = (λ({defs}). {body})\"",
                                   comp.prelude,
                                   name=name,
                                   uses=l_comp.nonlocal_uses.iter().join(" "),
                                   defs=l_comp.nonlocal_defs.iter().join(", "),
                                   body=body);
            return format!("let ({muts}) = loop ({name} {immuts}) ({muts}) in\n{cont}", muts=l_comp.nonlocal_defs.iter().join(", "),
                           name=name, immuts=l_comp.nonlocal_uses.iter().join(" "), cont=rec!(l_comp.exits[0]));
        }

        let data = self.mir.basic_block_data(bb);
        let stmts = data.statements.iter().map(|s| self.transpile_statement(s, comp)).collect_vec();
        let terminator = match data.terminator {
            Terminator::Goto { target } =>
                rec!(target),
            Terminator::Panic { .. } => format!("panic"),
            Terminator::If { ref cond, ref targets } =>
                format!("if {} then {} else {}", self.get_operand(cond),
                rec!(targets[0]),
                rec!(targets[1])),
            Terminator::Return => format!("ret"),
            Terminator::Call { ref data, ref targets } => {
                let call = format!("({} {})", self.get_lvalue(&data.func),
                                   data.args.iter().map(|lv| self.get_lvalue(lv)).join(" "));
                let muts = data.args.iter().filter(|lv| {
                    FnTranspiler::try_unwrap_mut_ref(self.lvalue_ty(lv)).is_some()
                });
                self.set_lvalues(iter::once(&data.destination).chain(muts), &call) +
                        &rec!(targets[0])
            },
            Terminator::Switch { ref discr, ref targets } =>
                if let ty::TypeVariants::TyEnum(ref adt_def, _) = self.lvalue_ty(discr).sty {
                    format!("case {} of {}", self.get_lvalue(discr),
                        adt_def.variants.iter().zip(targets).map(|(var, &target)| {
                            format!("{} {} => {}", self.transpile_def_id(var.did),
                                    iter::repeat("_").take(var.fields.len()).join(" "),
                                    rec!(target))
                        }).join(" | "))
                } else {
                    unreachable!()
                },
            _ => panic!("unimplemented: {:?}", data),
        };
        stmts.into_iter().chain(iter::once(terminator)).join("")
    }
}

fn transpile_fn<'tcx>(f: &mut Write, name: &ast::Name, decl: &FnDecl, tcx: &ty::ctxt<'tcx>, mir: &Mir<'tcx>)
        -> io::Result<()> {
    let (param_names, param_types): (Vec<_>, Vec<_>) = decl.inputs.iter().map(|param| {
        match param.pat.node {
            Pat_::PatIdent(BindingMode::BindByRef(hir::Mutability::MutMutable), _, _) =>
               panic!("unimplemented: &mut param ({:?})", param),
            Pat_::PatIdent(_, ref ident, _) =>
                (ident.node.name.as_str().to_string(), &param.ty),
            _ => panic!("unimplemented: param pattern ({:?})", param),
        }
    }).unzip();
    let return_ty = match decl.output {
        FunctionRetTy::DefaultReturn(_) => "()".to_string(),
        FunctionRetTy::Return(ref ty) => transpile_hir_ty(ty),
        FunctionRetTy::NoReturn(_) => panic!("should skip: no-return fn"),
    };

    let trans = FnTranspiler { fn_name: format!("{}", name), tcx: tcx, mir: mir, param_names: &param_names };
    let mut comp = Component::new(&trans, START_BLOCK, mir.all_basic_blocks(), false);
    let body = trans.transpile_basic_block(START_BLOCK, &mut comp);

    try!(write!(f, "{prelude}

definition {name} :: \"{param_types} => {return_ty}\" where
\"{name} {param_names} = ({body})\"

",
                prelude=comp.prelude,
                name=name,
                param_types=param_types.iter().map(|ty| transpile_hir_ty(*ty)).join(" => "),
                return_ty=return_ty,
                param_names=param_names.iter().join(" "),
                body=body,
    ));
    Ok(())
}

fn transpile_module<'tcx>(module: &hir::Mod, tcx: &ty::ctxt<'tcx>, mir_map: &rustc_mir::mir_map::MirMap<'tcx>, f: &mut File) -> io::Result<()> {
    for item in module.items.iter() {
        match item.node {
            Item_::ItemFn(ref decl, _, _, _, ref generics, _) =>
                try!(transpile_fn(f, &item.name, decl, tcx, &mir_map[&item.id])),
            Item_::ItemImpl(_, _, ref generics, _, _, ref items) =>
                for item in items {
                    match item.node {
                        hir::ImplItem_::MethodImplItem(ref sig, _) =>
                            try!(transpile_fn(f, &item.name, &sig.decl, tcx, &mir_map[&item.id])),
                        _ => println!("unimplemented: {:?}", item),
                    }
                },
            Item_::ItemExternCrate(..) | Item_::ItemUse(..) => (),
            Item_::ItemMod(ref module) => try!(transpile_module(module, tcx, mir_map, f)),
            Item_::ItemTy(ref ty, ref generics) =>
                try!(write!(f, "typedef {} = {}\n\n", 1, 2)),
            _ => println!("unimplemented: {:?}", item),
        };
    }
    Ok(())
}

fn transpile_crate(krate: &Crate, tcx: &ty::ctxt) -> io::Result<()> {
    let mut f = try!(File::create("Export.thy"));
    try!(write!(f, "theory Export
imports Rustabelle
begin

"));
    let mir_map = build_mir_for_crate(tcx);
    transpile_module(&krate.module, tcx, &mir_map, &mut f);
    try!(write!(f, "end\n"));
    return Ok(());
}
