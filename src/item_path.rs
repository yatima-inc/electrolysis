use rustc::hir::map::definitions::DefPathData;
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;

// from ../rust/src/librustc/ty/item_path.rs, but forces absolute paths, plus some minor changes

fn push(buffer: &mut String, elem: &str) {
    if !buffer.is_empty() {
        buffer.push_str("::");
    }
    buffer.push_str(elem);
}

pub fn item_path_str(tcx: TyCtxt, def_id: DefId) -> String {
    let mut path = String::new();
    push_item_path(tcx, &mut path, def_id);
    path
}

fn push_item_path(tcx: TyCtxt, buffer: &mut String, def_id: DefId)
{
    let key = tcx.map.def_key(def_id);
    match key.disambiguated_data.data {
        DefPathData::CrateRoot => {
            assert!(key.parent.is_none());
            if !def_id.is_local() {
                push(buffer, &tcx.sess.cstore.crate_name(def_id.krate));
            }
        }

        DefPathData::InlinedRoot(ref _root_path) => {
            //assert!(key.parent.is_none());
            //push_item_path(tcx, buffer, root_path.def_id);
            unreachable!()
        }

        data => {
            let parent_def_id = DefId { krate: def_id.krate, index: key.parent.unwrap() }; //tcx.parent_def_id(def_id).unwrap();
            push_item_path(tcx, buffer, parent_def_id);
            match data {
                DefPathData::Impl => push_impl_path(tcx, buffer, def_id),
                DefPathData::ClosureExpr => push(buffer, &format!("closure_{}", def_id.index.as_usize())),
                _ => push(buffer, &data.as_interned_str()),
            }
        }
    }
}

fn push_impl_path(tcx: TyCtxt, buffer: &mut String, impl_def_id: DefId)
{
    let self_ty = format!("{}", tcx.lookup_item_type(impl_def_id).ty);
    push(buffer, &self_ty);

    if let Some(trait_ref) = tcx.impl_trait_ref(impl_def_id) {
        // avoid nested :: separators
        push(buffer, &format!("{}", trait_ref).replace("::", "_"));
    }
}
