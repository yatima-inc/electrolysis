#![feature(rustc_private)]

extern crate itertools;

#[macro_use]
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_front;
extern crate syntax;

use std::env;
use std::io;
use std::io::prelude::*;
use std::fs::File;
use std::path;

use itertools::Itertools;

use syntax::ast;
use rustc_front::hir::*;
use rustc_front::print::pprust;
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
    try!(write!(f, "definition {name} :: \"{param_types} => {return_ty}\" where
\"{name} {param_names} = {block} id [{init_state}]\"

",
                name=name,
                param_types=param_types.iter().map(|ty| transpile_tyref(*ty)).join(" => "),
                return_ty=return_ty,
                param_names=param_names.iter().join(" "),
                block="undefined",
                init_state=param_names.iter().map(|name| format!("''{n}'' |-> {n}", n=name))
                               .join(", ")
    ));
    return Ok(());
}

fn transpile_crate(krate: &Crate, tcx: &ctxt) -> io::Result<()> {
    let mut f = try!(File::create("Export.thy"));
    try!(write!(f, "theory Export
imports Main
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
    return Ok(());
}
