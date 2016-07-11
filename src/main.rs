// we require access to many rustc internals
#![feature(rustc_private)]
#![feature(box_patterns, recover, slice_patterns, advanced_slice_patterns)]

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

mod item_path;
mod joins;
mod mir_graph;
mod trans;

use std::collections::HashSet;
use std::io;
use std::io::prelude::*;
use std::iter;
use std::fs::File;
use std::path;

use itertools::Itertools;
use petgraph::algo::*;

use syntax::ast::NodeId;
use rustc_front::hir;
use rustc_front::intravisit;
use rustc::middle::cstore::CrateStore;

use rustc_driver::driver;
use syntax::diagnostics;
use rustc::session;

use trans::krate::{CrateTranspiler, name_def_id};

fn main() {
    let crate_name = match &std::env::args().collect_vec()[..] {
        [_, ref crate_name] => crate_name.clone(),
        _ => panic!("Expected crate name as single cmdline argument"),
    };

    // get rust path from rustc itself
    let sysroot = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap()
        .stdout;
    let sysroot = path::PathBuf::from(String::from_utf8(sysroot).unwrap().trim());

    // load TOML config from 'thys/$crate/config.toml'
    let mut config = String::new();
    let mut config_file = File::open(path::Path::new("thys").join(&crate_name).join("config.toml")).expect("error opening crate config");
    config_file.read_to_string(&mut config).unwrap();
    let config: toml::Value = config.parse().unwrap();

    // parse rustc options
    let rustc_args = config.lookup("rustc_args").expect("missing config item 'rustc_args'");
    let rustc_args = iter::once("rustc").chain(rustc_args.as_str().unwrap().split(" ")).map(|s| s.to_string());
    let rustc_matches = rustc_driver::handle_options(rustc_args.collect()).expect("error parsing rustc args");
    let mut options = session::config::build_session_options(&rustc_matches);
    options.crate_name = Some(crate_name);
    options.maybe_sysroot = Some(sysroot);
    let input = match &rustc_matches.free[..] {
        [ref file] => path::PathBuf::from(file),
        _ => panic!("expected input file"),
    };

    // some more rustc orchestration
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
                    transpile_crate(&state, &config).unwrap();
                }),
                run_callback_on_error: false,
            },
            .. driver::CompileController::basic()
        }
    );
}

/// Collects all node IDs of a crate
struct IdCollector {
    ids: Vec<NodeId>
}

impl<'a> intravisit::Visitor<'a> for IdCollector {
    fn visit_item(&mut self, item: &'a hir::Item) {
        if let hir::Item_::ItemDefaultImpl(_, _) = item.node {
            return // default impls don't seem to be part of the HIR map
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

fn toml_value_as_str_array(val: &::toml::Value) -> Vec<&str> {
    val.as_slice().unwrap().iter().map(|t| t.as_str().unwrap()).collect()
}

fn transpile_crate(state: &driver::CompileState, config: &toml::Value) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    let crate_name = state.crate_name.unwrap();
    let base = path::Path::new("thys").join(crate_name);

    let mut trans = CrateTranspiler::new(tcx, &state.mir_map.unwrap(), config);
    println!("Transpiling...");

    let targets = config.lookup("targets").map(|targets| {
        toml_value_as_str_array(targets).into_iter().collect::<HashSet<_>>()
    });

    // find targets' DefIds and transpile them
    let mut id_collector = IdCollector { ids: vec![] };
    state.hir_crate.unwrap().visit_all_items(&mut id_collector);
    for id in id_collector.ids {
        let def_id = tcx.map.local_def_id(id);
        let name = name_def_id(tcx, def_id);
        if targets.iter().all(|targets| targets.contains(&*name)) {
            trans.transpile(def_id);
        }
    }

    let (trans_results, trans::krate::Deps { crate_deps, graph, .. }) = trans.destruct();

    // write out theory header, importing dependencies and the pre file, if existent

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
open prod.ops
open sum
"));
    if has_pre {
        try!(write!(f, "open {}\n", crate_name));
    }
    try!(write!(f, "

namespace {}

", crate_name));

    // condensate sets of cyclic dependencies into graph nodes
    let condensed = condensation(graph, /* make_acyclic */ true);

    // write out each cyclic set, in dependencies-first order
    let mut failed = HashSet::new();
    for idx in toposort(&condensed) {
        match &condensed[idx][..] {
            // a singleton set, meaning no cyclic dependencies!
            [def_id] => {
                let name = name_def_id(tcx, def_id);

                // don't even bother writing out code that will fail because of missing dependencies
                let failed_deps = condensed.neighbors_directed(idx, petgraph::EdgeDirection::Incoming).filter(|idx| failed.contains(idx)).collect_vec();
                if failed_deps.is_empty() {
                    match trans_results[&def_id] {
                        Ok(Some(ref trans)) => {
                            try!(write!(f, "{}\n\n", trans));
                        }
                        Ok(None) => {}
                        Err(ref err) => {
                            failed.insert(idx);
                            try!(write!(f, "/- {}: {} -/\n\n", name, err.replace("/-", "/ -")))
                        }
                    }
                } else {
                    failed.insert(idx);
                    try!(write!(f, "/- {}: failed dependencies {} -/\n\n", name, failed_deps.into_iter().flat_map(|idx| &condensed[idx]).map(|&def_id| {
                        name_def_id(tcx, def_id)
                    }).join(", ")));
                }
            }

            // cyclic dependencies, oh my
            component => {
                let succeeded = component.iter().filter_map(|def_id| trans_results.get(def_id).and_then(|trans| trans.as_ref().ok())).collect_vec();
                if succeeded.len() == component.len() {
                    if succeeded.iter().all(|trans| trans.as_ref().unwrap().starts_with("inductive")) {
                        // hackishly turn ["inductive A...", "inductive B..."] into "inductive A... with B..."
                        try!(write!(f, "inductive {}\n\n", succeeded.iter().map(|trans| trans.as_ref().unwrap().trim_left_matches("inductive")).join("\n\nwith")));
                        continue;
                    }
                }
                failed.insert(idx);
                try!(write!(f, "/- unimplemented: circular dependencies: {}\n\n", component.iter().map(|&def_id| {
                    name_def_id(tcx, def_id)
                }).join(", ")));
                for &def_id in component {
                    let name = name_def_id(tcx, def_id);
                    match trans_results[&def_id] {
                        Ok(Some(ref trans)) => {
                            try!(write!(f, "{}\n\n", trans));
                        }
                        Err(ref err) => {
                            try!(write!(f, "{}: {}\n\n", name, err.replace("/-", "/ -")))
                        }
                        _ => {}
                    }
                }
                try!(write!(f, "-/\n\n"))
            }
        }
    }

    // the end!
    write!(f, "end {}", crate_name)
}
