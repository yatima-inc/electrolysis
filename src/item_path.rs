use rustc::hir::map::definitions::DefPathData;
use rustc::hir::def_id::DefId;
use rustc::ty::{self, TyCtxt};

use itertools::Itertools;

// from ../rust/src/librustc/ty/item_path.rs, but simpler impl presentation

pub fn push_item_path(tcx: TyCtxt, buffer: &mut Vec<String>, def_id: DefId)
{
    let key = tcx.def_key(def_id);
    match key.disambiguated_data.data {
        DefPathData::CrateRoot => {
            assert!(key.parent.is_none());
            if !def_id.is_local() {
                buffer.push(tcx.sess.cstore.crate_name(def_id.krate).to_string());
            }
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
        if !impl_def_id.is_local() {
            buffer.push(tcx.sess.cstore.crate_name(impl_def_id.krate).to_string());
        }
        buffer.push(format!("{} as {}", self_ty, trait_ref))
    } else {
        let name = format!("{}", self_ty);
        match self_ty.sty {
            ty::TyStruct(..) | ty::TyEnum(..) => {
                // `local_crate::a::B<c::D>` ~> `a.«B<c::D>»`
                let sep = name.find("<").unwrap_or(name.len());
                let mut parts = name[..sep].split("::").map(ToString::to_string).collect_vec();
                if self_ty.ty_to_def_id().unwrap().is_local() {
                    // remove crate root
                    parts = parts.into_iter().skip(1).collect();
                }
                *parts.last_mut().unwrap() += &name[sep..];
                buffer.extend(parts);
            }
            _ => {
                // `[T]` ~> `collections.«[T]»`
                if !impl_def_id.is_local() {
                    buffer.push(tcx.sess.cstore.crate_name(impl_def_id.krate).to_string());
                }
                buffer.push(name)
            }
        }
    }
}
