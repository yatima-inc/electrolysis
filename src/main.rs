#![feature(rustc_private)]
#![feature(slice_patterns)]

extern crate itertools;

#[macro_use]
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_front;
extern crate rustc_mir;
extern crate syntax;

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
use rustc::middle::ty::ctxt;
use rustc::middle::ty::Ty;
use rustc::middle::ty::TypeVariants;

use rustc_driver::driver;
use syntax::diagnostics;
use rustc::session;


fn main() {
    let krate = env::args().nth(1).unwrap();
    let sess = session::build_session(
        session::config::Options {
            crate_types: vec![session::config::CrateType::CrateTypeRlib],
            maybe_sysroot: Some(path::PathBuf::from("/usr/local")),
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

struct FnTranspiler<'a, 'tcx: 'a> {
    tcx: &'a ctxt<'tcx>,
    mir: &'a Mir<'tcx>,
    param_names: &'a Vec<String>,
    return_ty: String,
}

impl<'a, 'tcx> FnTranspiler<'a, 'tcx> {
    // State = Maybe v0 * Maybe v1 * ... * Maybe t0 * ...

    fn get_locals_types(&self) -> Vec<String> {
        self.mir.var_decls.iter().map(|v| v.ty)
            .chain(self.mir.temp_decls.iter().map(|t| t.ty))
            .map(|ty| self.transpile_ty(ty))
            .chain(iter::once(self.return_ty.clone()))
            .collect()
    }

    fn num_locals(&self) -> usize { self.get_locals_types().len() }

    fn get_local(&self, idx: usize) -> String {
        format!("(let ({}) = s in the x)",
            iter::repeat("_").take(idx)
                .chain(iter::once("x"))
                .chain(iter::repeat("_").take(self.num_locals() - idx - 1))
                .join(", "))
    }

    fn get_lvalue(&self, lv: &Lvalue) -> String {
        match *lv {
            Lvalue::Var(idx) => self.get_local(idx as usize),
            Lvalue::Temp(idx) => self.get_local(self.mir.var_decls.len() + idx as usize),
            Lvalue::Arg(idx) => self.param_names[idx as usize].clone(),
            _ => panic!("unimplemented: loading {:?}", lv)
        }
    }

    fn set_local(&self, idx: usize, val: Option<&str>) -> String {
        fn mk_name(idx: usize) -> String {
            format!("s{}", idx)
        }
        format!("(let ({}) = s in ({}))",
            (0..self.num_locals()).map(mk_name).join(", "),
            (0..self.num_locals()).map(|i| {
                if i == idx {
                    match val {
                        Some(val) => format!("Some {}", val),
                        None => format!("None")
                    }
                }
                else {
                    mk_name(i)
                }
            }).join(", "))
    }

    fn set_lvalue(&self, lv: &Lvalue, val: Option<&str>) -> String {
        match *lv {
            Lvalue::Var(idx) => self.set_local(idx as usize, val),
            Lvalue::Temp(idx) => self.set_local(self.mir.var_decls.len() + idx as usize, val),
            Lvalue::ReturnPointer => self.set_local(self.num_locals() - 1, val),
            _ => panic!("unimplemented: storing {:?}", lv)
        }
    }

    fn transpile_ty(&self, ty: Ty) -> String {
        match ty.sty {
            TypeVariants::TyUint(ast::UintTy::TyU32) => "u32".to_string(),
            TypeVariants::TyTuple(ref tys) => match &tys[..] {
                [] => "unit".to_string(),
                _ => format!("({})", tys.iter().map(|ty| self.transpile_ty(ty)).join(", ")),
            },
            _ => match ty.ty_to_def_id() {
                Some(did) => self.tcx.item_path_str(did),
                None => panic!("unimplemented: {:?}", ty),
            }
        }
    }

    fn get_operand(&self, op: &Operand) -> String {
        match *op {
            Operand::Consume(ref lv) => self.get_lvalue(lv),
            Operand::Constant(ref c) => match c.literal {
                Literal::Value { value: ConstVal::Uint(i) } => i.to_string(),
                Literal::Value { .. } => panic!("unimplemented: {:?}", op),
                Literal::Item { def_id, substs }  => {
                    assert!(substs.types.iter().len() == 0);
                    self.tcx.item_path_str(def_id)
                }
            }
        }
    }

    fn transpile_rvalue(&self, rv: &Rvalue) -> String {
        match *rv {
            Rvalue::Use(ref op) => self.get_operand(op),
            Rvalue::BinaryOp(op, ref o1, ref o2) =>
                format!("({} {} {})", self.get_operand(o1), binop_to_string(op),
                        self.get_operand(o2)),
            _ => panic!("unimplemented: {:?}", rv),
        }
    }

    fn transpile_statement(&self, stmt: &Statement) -> String {
        match stmt.kind {
            StatementKind::Assign(ref lv, ref rv) => {
                let val = self.transpile_rvalue(rv);
                format!("(λcont s. cont {})", self.set_lvalue(lv, Some(&val)))
            }
            StatementKind::Drop(DropKind::Deep, ref lv) =>
                format!("(λcont s. cont {})", self.set_lvalue(lv, None)),
            _ => panic!("unimplemented: {:?}", stmt),
        }
    }

    fn transpile_basic_block(&self, bb: BasicBlock) -> String {
        let data = self.mir.basic_block_data(bb);
        let stmts = data.statements.iter().map(|s| self.transpile_statement(s));
        let terminator = match data.terminator {
            Terminator::Goto { target } =>
                self.transpile_basic_block(target),
            Terminator::Panic { .. } => format!("panic"),
            Terminator::If { ref cond, ref targets } =>
                format!("(ite {} {} {})", self.get_operand(cond),
                self.transpile_basic_block(targets[0]),
                self.transpile_basic_block(targets[1])),
                Terminator::Return => format!("id"),
                _ => panic!("unimplemented: {:?}", data),
        };
        stmts.chain(iter::once(terminator)).join(";\n")
    }
}

fn transpile_fn<'tcx>(f: &mut Write, name: &ast::Name, decl: &FnDecl, tcx: &ctxt<'tcx>, mir: &Mir<'tcx>)
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

    let transpiler = FnTranspiler { tcx: tcx, mir: mir, param_names: &param_names,
        return_ty: return_ty.clone() };

    try!(write!(f, "definition {name} :: \"{param_types} => {return_ty}\" where
\"{name} {param_names} = ({block}) (λs. {get_retval}) ({init_state})\"

",
                name=name,
                param_types=param_types.iter().map(|ty| transpile_hir_ty(*ty)).join(" => "),
                return_ty=return_ty,
                param_names=param_names.iter().join(" "),
                block=transpiler.transpile_basic_block(START_BLOCK),
                get_retval=transpiler.get_local(transpiler.num_locals() - 1),
                init_state=transpiler.get_locals_types()
                    .iter().map(|ty| format!("None::{} option", ty))
                    .join(", ")
    ));
    return Ok(());
}

fn transpile_crate(krate: &Crate, tcx: &ctxt) -> io::Result<()> {
    let mut f = try!(File::create("Export.thy"));
    try!(write!(f, "theory Export
imports Rustabelle
begin

"));
    let mir_map = build_mir_for_crate(tcx);
    for item in krate.module.items.iter() {
        if let Item {
            id, ref name,
            node: Item_::ItemFn(ref decl, _, _, _, ref generics, _), ..
        } = **item {
            try!(transpile_fn(&mut f, name, decl, tcx, mir_map.get(&id).unwrap()));
        };
    }
    try!(write!(f, "end\n"));
    return Ok(());
}
