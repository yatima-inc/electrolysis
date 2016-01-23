use syntax;
use syntax::ast;
use rustc::middle::infer;
use rustc::middle::subst;
use rustc::middle::traits;
use rustc::middle::ty::*;
use rustc::middle::def_id::DefId;
//use rustc_trans::trans::monomorphize;

// copied from trans::meth
pub fn combine_impl_and_methods_tps<'tcx>(//tcx: &ctxt<'tcx>,
                                      node_substs: subst::Substs<'tcx>,
                                      rcvr_substs: subst::Substs<'tcx>)
                                      -> subst::Substs<'tcx>
{
    // Break apart the type parameters from the node and type
    // parameters from the receiver.
    let node_method = node_substs.types.split().fns;
    let subst::SeparateVecsPerParamSpace {
        types: rcvr_type,
        selfs: rcvr_self,
        fns: rcvr_method
    } = rcvr_substs.types.clone().split();
    assert!(rcvr_method.is_empty());
    subst::Substs {
        regions: subst::ErasedRegions,
        types: subst::VecPerParamSpace::new(rcvr_type, rcvr_self, node_method)
    }
}

// copied from trans::common
fn fulfill_obligation<'tcx>(tcx: &ctxt<'tcx>, trait_ref: PolyTraitRef<'tcx>)
    -> Result<traits::Vtable<'tcx, ()>, String>
{
    let span = syntax::codemap::DUMMY_SP;
    let infcx = infer::normalizing_infer_ctxt(tcx, &tcx.tables);
    let mut selcx = traits::SelectionContext::new(&infcx);
    let obligation =
        traits::Obligation::new(traits::ObligationCause::misc(span, ast::DUMMY_NODE_ID),
        trait_ref.to_poly_trait_predicate());
    let selection = match selcx.select(&obligation) {
        Ok(x) => x.unwrap(),
        Err(err) => throw!("obligation select: {:?}", err),
    };
    let mut fulfill_cx = infcx.fulfillment_cx.borrow_mut();
    let vtable = selection.map(|predicate| {
        fulfill_cx.register_predicate_obligation(&infcx, predicate);
    });
    infer::drain_fulfillment_cx(&infcx, &mut fulfill_cx, &vtable).map_err(|e| format!("obligation drain: {:?}", e))
}

pub fn lookup_trait_item_impl<'tcx>(tcx: &ctxt<'tcx>, item_did: DefId, substs: &subst::Substs<'tcx>) -> Result<DefId, String> {
    // from trans::meth::trans_method_callee
    let trait_did = tcx.trait_of_item(item_did).unwrap();
    let trait_substs = substs.clone().method_to_trait();
    let trait_substs = tcx.mk_substs(trait_substs);
    let trait_ref = TraitRef::new(trait_did, trait_substs);
    let trait_ref = Binder(trait_ref);
    match try!(fulfill_obligation(tcx, trait_ref)) {
        traits::Vtable::VtableImpl(data) => {
            // from trans::meth::trans_monomorphized_callee
            let impl_did = data.impl_def_id;
            let mname = match tcx.impl_or_trait_item(item_did) {
                MethodTraitItem(method) => method.name,
                _ => unreachable!(),
            };
            let callee_substs = combine_impl_and_methods_tps(/*tcx, */substs.clone(), data.substs);

            let mth = tcx.get_impl_method(impl_did, callee_substs, mname);
            Ok(mth.method.def_id)
        },
        vtable => throw!("unimplemented: vtable {:?}", vtable),
    }
}
