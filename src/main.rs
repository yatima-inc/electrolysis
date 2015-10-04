#![feature(rustc_private)]
#![feature(slice_patterns)]

extern crate itertools;

#[macro_use]
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_front;
extern crate syntax;

use std::collections::HashMap;
use std::env;
use std::io;
use std::io::prelude::*;
use std::iter;
use std::iter::FromIterator;
use std::fs::File;
use std::path;

use itertools::Itertools;

use syntax::ast;
use rustc_front::hir::*;
use rustc_front::util;
use rustc_front::print::pprust;
use rustc::middle::def;
use rustc::middle::def_id::DefId;
use rustc::middle::ty::ctxt;

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

fn transpile_tyref(ty: &Ty) -> String {
    match ty.node {
        Ty_::TyPath(None, ref path) => transpile_path(path),
        _ => panic!("unimplemented: type {:?}", ty),
    }
}

fn local_get_def_id(tcx: &ctxt, node_id: ast::NodeId) -> Option<DefId> {
    match tcx.def_map.borrow().get(&node_id) {
        Some(&def::PathResolution { base_def: def::DefLocal(id, _), ..}) =>
            Some(id),
        _ => None
    }
}

struct FnTranspiler<'a, 'tcx: 'a> {
    local_idx: HashMap<DefId, usize>,
    tcx: &'a ctxt<'tcx>,
}

impl<'a, 'tcx> FnTranspiler<'a, 'tcx> {
    // C[e] :: Cont -> Cont
    // Cont = State -> RIn -> ROut
    // State = Maybe l0 * Maybe l1 * ...

    fn num_locals(&self) -> usize { self.local_idx.len() }

    fn get_local(&self, id: &DefId) -> String {
        let idx = *self.local_idx.get(id).unwrap();
        format!("(let ({}) = s in the x)",
            iter::repeat("_").take(idx)
                .chain(iter::once("x"))
                .chain(iter::repeat("_").take(self.num_locals() - idx - 1))
                .join(", "))
    }

    fn set_local(&self, id: &DefId, val: &str) -> String {
        fn mk_name(idx: usize) -> String {
            format!("s{}", idx)
        }
        let idx = *self.local_idx.get(id).unwrap();
        format!("(let ({}) = s in ({}))",
            (0..self.num_locals()).map(mk_name).join(", "),
            (0..self.num_locals()).map(
                |i| if i == idx { format!("Some({})", val.to_string()) }
                else { mk_name(i) }
            ).join(", "))
    }

    fn transpile_pat(&self, pat: &Pat, expr: &Expr) -> String {
        match pat.node {
            Pat_::PatIdent(_, _, _) =>
                format!("(λcont s. {} (λs r. cont {} ()) s)",
                    self.transpile_expr(expr),
                    self.set_local(&self.tcx.map.local_def_id(pat.id), "r")),
            _ => panic!("unimplemented: pattern ({:?})", pat)
        }
    }

    fn transpile_expr(&self, expr: &Expr) -> String {
        match expr.node {
            Expr_::ExprLit(ref lit) => match lit.node {
                ast::Lit_::LitInt(i, _) =>
                    format!("(λcont s. cont s {})", i.to_string()),
                _ => panic!("unimplemented: expr {:?}", expr),
            },
            Expr_::ExprPath(None, _) =>
                match local_get_def_id(self.tcx, expr.id) {
                    Some(id) => format!("(λcont s. cont s {})", self.get_local(&id)),
                    None => panic!("unimplemented: expr {:?}", expr),
                },
            Expr_::ExprBinary(ref op, ref e1, ref e2) =>
                format!("(lift2 (op {}) {} {})",
                        util::binop_to_string(op.node),
                        self.transpile_expr(e1), self.transpile_expr(e2)),
            Expr_::ExprMatch(ref expr, ref arms, _) => {
                if let [ref arm] = &arms[..] {
                    if let [ref pat] = &arm.pats[..] {
                        return format!("({}; {})",
                            self.transpile_pat(&*pat, expr),
                            self.transpile_expr(&*arm.body));
                    }
                }
                panic!("unimplemented: {:?}", expr)
            },
            Expr_::ExprBlock(ref block) => self.transpile_block(&**block),
            _ => panic!("unimplemented: expr {:?}", expr),
        }
    }

    fn transpile_local(&self, local: &Local) -> String {
        match local.init {
            None => "id".to_string(),
            Some(ref expr) => self.transpile_pat(&*local.pat, expr)
        }
    }

    fn transpile_stmt(&self, stmt: &Stmt) -> String {
        match stmt.node {
            Stmt_::StmtDecl(ref decl, _) => match decl.node {
                Decl_::DeclItem(_) => panic!("unimplemented: local item ({:?})", decl),
                Decl_::DeclLocal(ref local) => self.transpile_local(&**local),
            },
            Stmt_::StmtExpr(ref expr, _) | Stmt_::StmtSemi(ref expr, _) =>
                self.transpile_expr(&**expr)
        }
    }

    fn transpile_block(&self, block: &Block) -> String {
        let stmts = block.stmts.iter().map(|stmt| self.transpile_stmt(&**stmt));
        let expr = block.expr.as_ref().map(|expr| self.transpile_expr(&*expr));
        format!("({})", stmts.chain(expr).join("; "))
    }
}

fn get_locals(block: &Block, tcx: &ctxt) -> Vec<DefId> {
    struct Visitor<'a, 'tcx: 'a> {
        res: Vec<DefId>,
        tcx: &'a ctxt<'tcx>
    }
    impl<'a, 'tcx> rustc_front::visit::Visitor<'a> for Visitor<'a, 'tcx> {
        fn visit_local(&mut self, l: &Local) {
            self.res.push(self.tcx.map.local_def_id(l.pat.id));
        }
    }
    let mut v = Visitor { res: Vec::new(), tcx: tcx };
    rustc_front::visit::walk_block(&mut v, block);
    v.res
}

fn transpile_fn(f: &mut Write, name: &ast::Name, decl: &FnDecl, tcx: &ctxt, block: &Block)
        -> io::Result<()> {
    let (param_names, param_types): (Vec<_>, Vec<_>) = decl.inputs.iter().map(|param| {
        match param.pat.node {
            Pat_::PatIdent(BindingMode::BindByRef(Mutability::MutMutable), _, _) =>
                panic!("unimplemented: &mut param ({:?})", param),
            Pat_::PatIdent(_, ref ident, _) =>
                (ident.node.name.as_str().to_string(), &param.ty),
            _ => panic!("unimplemented: param pattern ({:?})", param),
        }
    }).unzip();
    let return_ty = match decl.output {
        FunctionRetTy::DefaultReturn(_) => "()".to_string(),
        FunctionRetTy::Return(ref ty) => transpile_tyref(ty),
        FunctionRetTy::NoReturn(_) => panic!("should skip: no-return fn"),
    };
    let locals = get_locals(block, tcx);
    let state = decl.inputs.iter().map(
        |param| tcx.map.local_def_id(param.pat.id)
    ).chain(locals.iter().map(DefId::clone));
    let transpiler = FnTranspiler { tcx: tcx,
        local_idx: HashMap::from_iter(state.enumerate().map(|(n, id)| (id, n)))
    };
    try!(write!(f, "definition {name} :: \"{param_types} => {return_ty}\" where
\"{name} {param_names} = {block} (λ_ ret. ret) ({init_state})\"

",
                name=name,
                param_types=param_types.iter().map(|ty| transpile_tyref(*ty)).join(" => "),
                return_ty=return_ty,
                param_names=param_names.iter().join(" "),
                block=transpiler.transpile_block(block),
                init_state=param_names.iter().map(|name| format!("Some({})", name))
                    .chain(locals.iter().map(|&id| format!("None::{} option", tcx.node_id_to_type(tcx.map.as_local_node_id(id).unwrap()))))
                    .take(transpiler.num_locals())
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
    for item in krate.module.items.iter() {
        if let Item {
            ref name,
            node: Item_::ItemFn(ref decl, _, _, _, ref generics, ref block), ..
        } = **item {
            try!(transpile_fn(&mut f, name, decl, tcx, block));
        };
    }
    try!(write!(f, "end\n"));
    return Ok(());
}
