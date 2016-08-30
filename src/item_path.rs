use rustc::hir::map::definitions::DefPathData;
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;

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
    // we suppress the unnecessary parent path, but still need the crate root
    if !impl_def_id.is_local() {
        buffer.push(tcx.sess.cstore.crate_name(impl_def_id.krate).to_string());
    }
    if let Some(trait_ref) = tcx.impl_trait_ref(impl_def_id) {
        buffer.push(format!("{} as {}",
                            tcx.lookup_item_type(impl_def_id).ty,
                            trait_ref))
    } else {
        buffer.push(format!("impl {}",
                            tcx.lookup_item_type(impl_def_id).ty))
    }
}
