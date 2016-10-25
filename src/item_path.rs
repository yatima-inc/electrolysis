use rustc::hir::map::definitions::DefPathData;
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use rustc::ty::TypeVariants::*;

use itertools::Itertools;

// from ../rust/src/librustc/ty/item_path.rs, but simpler impl presentation

fn push_krate(tcx: TyCtxt, buffer: &mut Vec<String>, def_id: DefId) {
    if def_id.is_local() {
        buffer.push(tcx.sess.opts.crate_name.as_ref().unwrap().to_string());
    } else {
        buffer.push(tcx.sess.cstore.crate_name(def_id.krate).to_string());
    }
}

pub fn push_item_path(tcx: TyCtxt, buffer: &mut Vec<String>, def_id: DefId)
{
    let key = tcx.def_key(def_id);
    match key.disambiguated_data.data {
        DefPathData::CrateRoot => {
            assert!(key.parent.is_none());
            push_krate(tcx, buffer, def_id)
        }

        DefPathData::InlinedRoot(ref _root_path) => {
            //assert!(key.parent.is_none());
            //push_item_path(tcx, buffer, root_path.def_id);
            unreachable!()
        }

        data => {
            let parent_def_id = DefId { krate: def_id.krate, index: key.parent.unwrap() }; //tcx.parent_def_id(def_id).unwrap();
            match data {
                DefPathData::Impl => push_impl_path(tcx, buffer, def_id),
                DefPathData::ClosureExpr => {
                    push_item_path(tcx, buffer, parent_def_id);
                    buffer.push(format!("closure_{}", def_id.index.as_usize()))
                }
                _ => {
                    push_item_path(tcx, buffer, parent_def_id);
                    buffer.push(data.as_interned_str().to_string())
                }
            }
        }
    }
}

fn push_impl_path(tcx: TyCtxt, buffer: &mut Vec<String>, impl_def_id: DefId)
{
    let self_ty = tcx.lookup_item_type(impl_def_id).ty;
    if let Some(trait_ref) = tcx.impl_trait_ref(impl_def_id) {
        // we suppress the unnecessary parent path, but still need the crate root
        push_krate(tcx, buffer, impl_def_id);
        buffer.push(format!("{} as {}", self_ty, trait_ref))
    } else {
        let name = format!("{}", self_ty);
        match self_ty.sty {
            TyAdt(..) => {
                // `a::B<c::D>` ~> `a.«B<c::D>»`
                let sep = name.find("<").unwrap_or(name.len());
                let mut parts = name[..sep].split("::").map(ToString::to_string).collect_vec();
                *parts.last_mut().unwrap() += &name[sep..];
                buffer.extend(parts);
            }
            _ => {
                // `[T]` ~> `collections.«[T]»`
                push_krate(tcx, buffer, impl_def_id);
                buffer.push(name)
            }
        }
    }
}
