use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::io::prelude::*;
use std::iter;

use itertools::Itertools;
use petgraph::graph::{self, Graph};
use toml;

use rustc_front::hir;
use rustc::mir::mir_map::MirMap;
use rustc::middle::def_id::DefId;
use rustc::middle::ty::{self, Ty, TyCtxt};

use item_path::item_path_str;
use trans::item::ItemTranspiler;

pub fn mk_lean_name<S : AsRef<str>>(s: S) -> String {
    let s = s.as_ref().replace("::", ".").replace(|c: char| c != '.' && !c.is_alphanumeric(), "_").trim_left_matches('_').to_owned();
    if s == "end" || s.ends_with(".end") || s == "by" || s.ends_with(".by") { s + "_" } else { s }
}

pub fn try_unwrap_mut_ref<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.sty {
        ty::TypeVariants::TyRef(_, ty::TypeAndMut { mutbl: hir::Mutability::MutMutable, ty }) =>
            Some(ty),
        _ => None
    }
}

pub fn format_generic_ty<It: Iterator<Item=String>>(ty: &str, generics: It) -> String {
    iter::once(ty.to_string()).chain(generics).join(" ")
}

pub fn name_def_id(tcx: &TyCtxt, did: DefId) -> String {
    mk_lean_name(item_path_str(tcx, did))
}

pub struct Config<'a> {
    pub ignored: HashSet<String>,
    pub replaced: HashMap<String, String>,
    pub config: &'a toml::Value,
}

impl<'a> Config<'a> {
    fn new(config: &'a toml::Value) -> Config {
        Config {
            ignored: match config.lookup("ignore") {
                Some(ignored) => ::toml_value_as_str_array(ignored).into_iter().map(str::to_string).collect(),
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

#[derive(Default)]
pub struct Deps {
    pub crate_deps: HashSet<String>,
    pub graph: Graph<DefId, ()>,
    def_idcs: HashMap<DefId, graph::NodeIndex>,
    new_deps: HashSet<DefId>,
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

pub struct CrateTranspiler<'a, 'tcx: 'a> {
    pub tcx: &'a TyCtxt<'tcx>,
    pub mir_map: &'a MirMap<'tcx>,
    pub config: Config<'a>,
    trans_results: HashMap<DefId, Result<Option<String>, String>>,
    deps: RefCell<Deps>,
}

impl<'a, 'tcx> CrateTranspiler<'a, 'tcx> {
    pub fn new(tcx: &'a TyCtxt<'tcx>, mir_map: &'a MirMap<'tcx>, config: &'a ::toml::Value) -> CrateTranspiler<'a, 'tcx> {
        CrateTranspiler {
            tcx: tcx,
            mir_map: mir_map,
            trans_results: HashMap::new(),
            deps: Default::default(),
            config: Config::new(config),
        }
    }

    pub fn destruct(self) -> (HashMap<DefId, Result<Option<String>, String>>, Deps) {
        (self.trans_results, self.deps.into_inner())
    }

    pub fn add_dep(&self, used: DefId, user: DefId) {
        if used.is_local() {
            self.deps.borrow_mut().add_dep(used, user);
        } else {
            let crate_name = self.tcx.sess.cstore.crate_name(used.krate);
            self.deps.borrow_mut().crate_deps.insert(crate_name.to_string());
        }
    }

    pub fn is_recursive(&self, def_id: DefId) -> bool {
        let idx = self.deps.borrow_mut().get_def_idx(def_id);
        self.deps.borrow().graph.neighbors_directed(idx, ::petgraph::EdgeDirection::Incoming).any(|idx2| idx2 == idx)
    }

    fn try_transpile<F : for<'b> FnOnce(ItemTranspiler<'b, 'tcx>) -> Option<String>>(&mut self, def_id: DefId, f: F) {
        let name = name_def_id(self.tcx, def_id);

        if self.trans_results.contains_key(&def_id) || self.config.ignored.contains(&name) {
            return
        }

        self.deps.borrow_mut().get_def_idx(def_id); // add to dependency graph
        let res = self.config.replaced.get(&name).map(|res| Ok(Some(res.to_string())));
        let res = res.unwrap_or_else(|| {
            ::std::panic::recover(::std::panic::AssertRecoverSafe::new(|| {
                f(ItemTranspiler { sup: self, def_id: def_id })
            })).map_err(|err| {
                match err.downcast_ref::<String>() {
                    Some(msg) => msg.clone(),
                    None => match err.downcast_ref::<&'static str>() {
                        Some(msg) => msg,
                        None      => "compiler error",
                    }.to_string(),
                }
            })
        });
        self.trans_results.insert(def_id, res);
        let new_deps = self.deps.borrow().def_idcs.keys().cloned().collect_vec(); // self.deps.borrow_mut().new_deps.drain()...
        for dep in new_deps {
            self.transpile(dep)
        }
    }

    pub fn transpile(&mut self, def_id: DefId) {
        self.try_transpile(def_id, |trans| trans.transpile_def_id())
    }
}
