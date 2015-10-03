#![feature(plugin_registrar, rustc_private)]

extern crate itertools;

#[macro_use]
extern crate rustc;
extern crate rustc_front;
extern crate syntax;

use std::io;
use std::io::prelude::*;
use std::fs::File;

use itertools::Itertools;

use syntax::ast;
use rustc_front::hir::*;
use rustc_front::print::pprust;
use rustc::middle::ty::ctxt;
use rustc::lint::*;

use rustc::plugin::Registry;
use syntax::codemap::Span;
use rustc_front::visit::FnKind;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_late_lint_pass(Box::new(TranspilePass));
}

struct TranspilePass;

impl LintPass for TranspilePass {
    fn get_lints(&self) -> LintArray { lint_array!() }
}

impl LateLintPass for TranspilePass {
    fn check_fn(&mut self, cx: &LateContext,
        kind: FnKind, decl: &FnDecl, _: &Block, _: Span, _: ast::NodeId) {
        transpile_fn(kind, decl, cx.tcx).unwrap();
    }
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

fn transpile_fn(kind: FnKind, decl: &FnDecl, tcx: &ctxt) -> io::Result<()> {
    let mut f = try!(File::create("Export.thy"));
    try!(write!(f, "theory Export
    imports Main
    begin
    "));
    let name = match kind {
        FnKind::ItemFn(id, _, _, _, _, _) | FnKind::Method(id, _, _) => id,
        FnKind::Closure => unreachable!(),
    };
    let params = decl.inputs.iter().map(|param| {
        match param.pat.node {
            Pat_::PatIdent(BindingMode::BindByRef(Mutability::MutMutable), _, _) =>
                panic!("unimplemented: &mut param ({:?})", param),
            Pat_::PatIdent(_, ref ident, _) =>
                (ident.node.name, &param.ty),
            _ => panic!("unimplemented: param pattern ({:?})", param),
        }
    }).collect::<Vec<_>>();
    try!(write!(f, "definition {} :: \"{} => \" where", name,
                params.iter().map(|&(_, ty)| transpile_tyref(&ty)).join(" => ")));
    return Ok(());
}
