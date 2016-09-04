use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use petgraph::graph::{self, Graph};
use regex::Regex;
use toml;

use rustc::hir;
use rustc::hir::def_id::DefId;
use rustc::mir::mir_map::MirMap;
use rustc::ty::{self, Ty, TyCtxt};

use item_path;
use trans::item::ItemTranspiler;

lazy_static! {
    static ref LEAN_ID: Regex = Regex::new(r"^(_|[:alpha:])(_|'|[:alpha:]|\d)*$").unwrap();
}

/// Turns Rust identifiers into Lean ones
/// `std::[T]` ~> `std.«[T]»`
pub fn mk_lean_name_from_parts<'a, It, S>(parts: It) -> String
    where It : IntoIterator<Item=&'a S>, S : AsRef<str> + 'a {
    parts.into_iter().map(|part| {
        let part = part.as_ref().replace("::", ".")
            // Lean identifiers starting with _ are reserved
            .trim_left_matches("_").to_string();
        match part.as_ref() {
            "{{constructor}}" => "mk".to_string(),
            "by" | "end" => format!("«{}»", part),
            _ if LEAN_ID.is_match(&part) => part.to_string(),
            _ => format!("«{}»", part),
        }
    }).join(".")
}

pub fn try_unwrap_mut_ref<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.sty {
        ty::TypeVariants::TyRef(_, ty::TypeAndMut { mutbl: hir::Mutability::MutMutable, ty }) =>
            Some(ty),
        _ => None
    }
}

pub fn name_def_id(tcx: TyCtxt, def_id: DefId) -> String {
    let mut buffer = Vec::new();
    ty::item_path::with_forced_absolute_paths(|| {
        item_path::push_item_path(tcx, &mut buffer, def_id);
    });
    mk_lean_name_from_parts(&buffer)
}

pub struct Config<'a> {
    pub ignored: HashSet<String>, // cache at least this one
    pub config: &'a toml::Value,
}

impl<'a> Config<'a> {
    fn new(config: &'a toml::Value) -> Config {
        Config {
            ignored: match config.lookup("ignore") {
                Some(ignored) => ::toml_value_as_str_array(ignored).into_iter().map(str::to_string).collect(),
                None => HashSet::new(),
            },
            config: config,
        }
    }
}

#[derive(Default)]
pub struct Deps {
    // other crates referenced
    pub crate_deps: HashSet<String>,
    // a graph (used -> user)
    pub graph: Graph<DefId, ()>,
    def_idcs: HashMap<DefId, graph::NodeIndex>,
    // slightly hackish: new deps in the current transpile call
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

    fn drain_new_deps(&mut self) -> Vec<DefId> {
        self.new_deps.drain().collect_vec()
    }
}

pub struct CrateTranspiler<'a, 'tcx: 'a> {
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
    pub mir_map: &'a MirMap<'tcx>,
    pub config: Config<'a>,
    trans_results: HashMap<DefId, Result<Option<String>, String>>,
    deps: RefCell<Deps>,
}

impl<'a, 'tcx> CrateTranspiler<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, mir_map: &'a MirMap<'tcx>, config: &'a ::toml::Value) -> CrateTranspiler<'a, 'tcx> {
        CrateTranspiler {
            tcx: tcx,
            mir_map: mir_map,
            trans_results: HashMap::new(),
            deps: Default::default(),
            config: Config::new(config),
        }
    }

    pub fn mk_lean_name<S : AsRef<str>>(&self, s: S) -> String {
        mk_lean_name_from_parts(&[s])
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
        // look for self-loop
        self.deps.borrow().graph.neighbors_directed(idx, ::petgraph::EdgeDirection::Incoming).any(|idx2| idx2 == idx)
    }

    pub fn transpile(&mut self, def_id: DefId, catch_panics: bool) {
        let name = name_def_id(self.tcx, def_id);

        if self.trans_results.contains_key(&def_id) {
            return
        }

        if self.config.ignored.contains(&name) {
            self.trans_results.insert(def_id, Ok(None));
            return
        }

        println!("{}...", name);
        self.deps.borrow_mut().get_def_idx(def_id); // add to dependency graph
        let res = self.config.config.lookup(&format!("replace.\"{}\"", name)).map(|res| Ok(Some(res.as_str().unwrap().to_string())));
        let res = res.unwrap_or_else(|| {
            if catch_panics {
                // HACK: catch panics from rustc libs if we use an API in a wrong way
                ::std::panic::catch_unwind(::std::panic::AssertUnwindSafe(|| {
                    ItemTranspiler { sup: self, def_id: def_id }.transpile_def_id()
                })).map_err(|err| {
                    match err.downcast_ref::<String>() {
                        Some(msg) => msg.clone(),
                        None => match err.downcast_ref::<&'static str>() {
                            Some(msg) => msg,
                            None      => "compiler error",
                        }.to_string(),
                    }
                })
            } else {
                Ok(ItemTranspiler { sup: self, def_id: def_id }.transpile_def_id())
            }
        });
        self.trans_results.insert(def_id, res);
        let new_deps = self.deps.borrow_mut().drain_new_deps();
        for dep in new_deps {
            self.transpile(dep, catch_panics)
        }
    }
}
