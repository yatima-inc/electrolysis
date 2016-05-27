use std::collections::{HashMap, HashSet};
use std::iter;
use std::ops::Deref;

use itertools::Itertools;

use syntax::ast::{self, NodeId};
use rustc_front::hir::{self, FnDecl, PatKind};
use rustc::front;
use rustc::front::map::definitions::DefPathData;
use rustc::middle::def_id::DefId;
use rustc::middle::subst::{ParamSpace, Subst, Substs};
use rustc::middle::traits::*;
use rustc::middle::ty::{self, Ty};

use trans::krate::{self, CrateTranspiler};

pub enum TraitImplLookup<'tcx> {
    Static { impl_def_id: DefId, params: Vec<String>, substs: Substs<'tcx> },
    Dynamic { param: String },
}

impl<'tcx> TraitImplLookup<'tcx> {
    pub fn to_string<'a>(self, trans: &ItemTranspiler<'a, 'tcx>) -> String {
        match self {
            TraitImplLookup::Static { impl_def_id, params, substs } =>
                format!("({})", iter::once(trans.name_def_id(impl_def_id)).chain(substs.types.iter().map(|ty| {
                    trans.transpile_ty(ty)
                })).chain(params).join(" ")),
            TraitImplLookup::Dynamic { param } => param,
        }
    }
}

pub struct ItemTranspiler<'a, 'tcx: 'a> {
    pub sup: &'a CrateTranspiler<'a, 'tcx>,
    pub def_id: DefId,
}

impl<'a, 'tcx> Deref for ItemTranspiler<'a, 'tcx> {
    type Target = krate::CrateTranspiler<'a, 'tcx>;

    fn deref(&self) -> &krate::CrateTranspiler<'a, 'tcx> {
        self.sup
    }
}

impl<'a, 'tcx> ItemTranspiler<'a, 'tcx> {
    pub fn name(&self) -> String { krate::name_def_id(self.tcx, self.def_id) }
    pub fn node_id(&self) -> NodeId {
        self.tcx.map.as_local_node_id(self.def_id).unwrap()
    }

    pub fn add_dep(&self, def_id: DefId) {
        self.sup.add_dep(def_id, self.def_id)
    }

    pub fn name_def_id(&self, did: DefId) -> String {
        self.add_dep(did);
        krate::name_def_id(self.tcx, did)
    }

    fn transpile_trait_ref_args(&self, trait_ref: ty::TraitRef<'tcx>) -> Vec<String> {
        trait_ref.substs.types.iter().map(|ty| {
            self.transpile_ty(ty)
        }).collect()
    }

    fn transpile_associated_type(&self, _trait_ref: ty::TraitRef<'tcx>, name: &ast::Name) -> String {
        //let prefix = self.name_def_id(trait_ref.def_id);
        format!("{}", name) //_{}", prefix, name)
    }

    pub fn get_assoc_ty_substs(&self, def_id: DefId) -> HashMap<String, String> {
        self.tcx.lookup_predicates(def_id).predicates.into_iter().filter_map(|trait_pred| match trait_pred {
            ty::Predicate::Projection(ty::Binder(proj_pred)) => {
                let assoc_ty = self.transpile_associated_type(proj_pred.projection_ty.trait_ref, &proj_pred.projection_ty.item_name);
                Some((assoc_ty, self.transpile_ty(&proj_pred.ty)))
            }
            _ => None,
        }).collect()
    }

    pub fn transpile_trait_ref_assoc_tys(&self, trait_ref: ty::TraitRef<'tcx>, assoc_ty_substs: &HashMap<String, String>) -> (Vec<String>, Vec<String>) {
        let mut free_assoc_tys = vec![];
        let assoc_tys = self.trait_predicates_without_markers(trait_ref.def_id).flat_map(|trait_pred| {
            let trait_def = self.tcx.lookup_trait_def(trait_pred.def_id());
            trait_def.associated_type_names.iter().map(|name| {
                let assoc_ty = self.transpile_associated_type(trait_pred.trait_ref, name);
                match assoc_ty_substs.get(&assoc_ty) {
                    Some(assoc_ty) => assoc_ty.to_owned(),
                    _ => {
                        free_assoc_tys.push(assoc_ty.clone());
                        assoc_ty
                    }
                }
            }).collect_vec()
        }).collect();

        (assoc_tys, free_assoc_tys)
    }

    pub fn transpile_trait_ref_no_assoc_tys(&self, trait_ref: ty::TraitRef<'tcx>) -> String {
        iter::once(self.name_def_id(trait_ref.def_id)).chain(self.transpile_trait_ref_args(trait_ref)).join(" ")
    }

    pub fn transpile_trait_ref(&self, trait_ref: ty::TraitRef<'tcx>, assoc_ty_substs: &HashMap<String, String>) -> String {
        let associated_types = self.transpile_trait_ref_assoc_tys(trait_ref, assoc_ty_substs).0;
        iter::once(self.transpile_trait_ref_no_assoc_tys(trait_ref)).chain(associated_types).join(" ")
    }

    pub fn transpile_ty(&self, ty: Ty<'tcx>) -> String {
        match ty.sty {
            ty::TypeVariants::TyBool => "Prop".to_string(),
            ty::TypeVariants::TyUint(ref ty) => ty.to_string(),
            ty::TypeVariants::TyInt(ref ty) => ty.to_string(),
            //ty::TypeVariants::TyFloat(ref ty) => ty.to_string(),
            ty::TypeVariants::TyTuple(ref tys) => match &tys[..] {
                [] => "unit".to_string(),
                _ => format!("({})", tys.iter().map(|ty| self.transpile_ty(ty)).join(" × ")),
            },
            ty::TypeVariants::TyFnDef(_, _, ref data) | ty::TypeVariants::TyFnPtr(ref data) => {
                let sig = data.sig.skip_binder();
                let muts = sig.inputs.iter().filter_map(|i| krate::try_unwrap_mut_ref(i));
                let inputs = sig.inputs.iter().map(|ty| self.transpile_ty(ty));
                let mut outputs = match sig.output {
                    ty::FnOutput::FnConverging(out_ty) => iter::once(out_ty).chain(muts).map(|ty| self.transpile_ty(ty)),
                    ty::FnOutput::FnDiverging => panic!("unimplemented: diverging function"),
                };
                inputs.chain(iter::once(format!("option ({})", outputs.join(" × ")))).join(" → ")
            },
            ty::TypeVariants::TyStruct(ref adt_def, ref substs) |
            ty::TypeVariants::TyEnum(ref adt_def, ref substs) => format!("({})", krate::format_generic_ty(
                &self.name_def_id(adt_def.did),
                substs.types.iter().map(|ty| self.transpile_ty(ty))
            )),
            ty::TypeVariants::TyRef(_, ref data) => self.transpile_ty(data.ty),
            ty::TypeVariants::TyParam(ref param) => param.name.to_string(),
            ty::TypeVariants::TyProjection(ref proj) => self.transpile_associated_type(proj.trait_ref, &proj.item_name),
            ty::TypeVariants::TySlice(ref ty) => format!("(slice {})", self.transpile_ty(ty)),
            ty::TypeVariants::TyTrait(_) => panic!("unimplemented: trait objects"),
            ty::TypeVariants::TyInfer(_) => "_".to_string(), // FIXME
            _ => match ty.ty_to_def_id() {
                Some(did) => self.name_def_id(did),
                None => panic!("unimplemented: ty {:?}", ty),
            }
        }
    }

    fn trait_predicates(&self, def_id: DefId) -> ::std::vec::IntoIter<ty::TraitPredicate<'tcx>> {
        let mut predicates = self.tcx.lookup_predicates(def_id).predicates;
        if self.tcx.trait_of_item(def_id).is_some() {
            predicates.truncate(ParamSpace::TypeSpace, 0);
        }
        predicates.into_iter().filter_map(|trait_pred| match trait_pred {
            ty::Predicate::Trait(trait_pred) => Some(trait_pred.0),
            _ => None,
        }).collect_vec().into_iter()
    }

    fn is_marker_trait(&self, trait_def_id: DefId) -> bool {
        self.tcx.trait_items(trait_def_id).is_empty() &&
        self.trait_predicates(trait_def_id).all(|trait_pred| {
            trait_pred.def_id() == trait_def_id || self.is_marker_trait(trait_pred.def_id())
        })
    }

    pub fn trait_predicates_without_markers(&self, def_id: DefId) -> ::std::vec::IntoIter<ty::TraitPredicate<'tcx>> {
        self.trait_predicates(def_id).filter(|trait_pred| !self.is_marker_trait(trait_pred.def_id())).collect_vec().into_iter()
    }

    pub fn infer_trait_impl(&self, trait_ref: ty::TraitRef<'tcx>) -> TraitImplLookup<'tcx> {
        use rustc::middle::infer;

        let span = ::syntax::codemap::DUMMY_SP;
        let param_env = ty::ParameterEnvironment::for_item(self.tcx, self.node_id());
        let pred = ty::Binder(trait_ref).to_poly_trait_predicate().subst(self.tcx, &param_env.free_substs);
        let dbg_param_env = format!("{:?}", param_env.caller_bounds);
        let infcx = infer::new_infer_ctxt(self.tcx, &self.tcx.tables, Some(param_env), ProjectionMode::Any);
        let mut selcx = SelectionContext::new(&infcx);
        let obligation = Obligation::new(ObligationCause::misc(span, ast::DUMMY_NODE_ID), pred);
        let selection = selcx.select(&obligation).unwrap_or_else(|err| {
            panic!("obligation select: {:?} {:?} {:?}", obligation, err, dbg_param_env)
        }).unwrap();

        match selection {
            Vtable::VtableImpl(data) => {
                let nested_traits = data.nested.iter().filter_map(|obl| match obl.predicate {
                    ty::Predicate::Trait(ref trait_pred) if !self.is_marker_trait(trait_pred.skip_binder().def_id()) =>
                        Some(self.infer_trait_impl(trait_pred.skip_binder().trait_ref).to_string(self)),
                    _ => None,
                }).collect();

                let mut fulfill_cx = FulfillmentContext::new();
                for obl in data.nested {
                    fulfill_cx.register_predicate_obligation(&infcx, obl);
                }
                let substs = infer::drain_fulfillment_cx_or_panic(span, &infcx, &mut fulfill_cx, data.substs);

                TraitImplLookup::Static {
                    impl_def_id: data.impl_def_id,
                    params: nested_traits,
                    substs: substs
                }
            },
            Vtable::VtableParam(_) => {
                let param = krate::mk_lean_name(self.transpile_trait_ref_no_assoc_tys(trait_ref)).replace('.', "_");
                TraitImplLookup::Dynamic { param: param }
            }
            Vtable::VtableClosure(_) => {
                TraitImplLookup::Dynamic {
                    param: "_".to_string()
                }
            },
            vtable => panic!("unimplemented: vtable {:?}", vtable),
        }
    }

    fn as_generic_ty_def(&self, attr: Option<&str>) -> String {
        let name = if let Some(attr) = attr { format!("{} {}", self.name(), attr) } else { self.name() };
        // traits are weird
        let generics = if let front::map::Node::NodeItem(&hir::Item { node: hir::Item_::ItemTrait(..), .. }) =
            self.tcx.map.get(self.node_id()) {
            self.tcx.lookup_trait_def(self.def_id).generics.clone()
        } else {
            self.tcx.lookup_item_type(self.def_id).generics
        };
        iter::once(name).chain(generics.types.iter().map(|p| format!("({} : Type)", p.name))).join(" ")
    }

    fn transpile_struct(&self, variant: ty::VariantDef<'tcx>) -> String {
        match variant.kind {
            ty::VariantKind::Struct => {
                let mut fields = variant.fields.iter().map(|f| {
                    format!("({} : {})", krate::mk_lean_name(&*f.name.as_str()), self.transpile_ty(f.unsubst_ty()))
                });
                format!("structure {} := mk {{}} ::\n{}",
                        self.as_generic_ty_def(None),
                        fields.join("\n"))
            }
            ty::VariantKind::Tuple => {
                let mut fields = variant.fields.iter().map(|f| {
                    self.transpile_ty(f.unsubst_ty())
                });
                format!("inductive {} :=\nmk {{}} : {}",
                        self.as_generic_ty_def(None),
                        fields.join(" × "))
            }
            ty::VariantKind::Unit =>
                format!("structure {} := mk {{}} ::", self.as_generic_ty_def(None)),
        }
    }

    fn transpile_enum(&self, name: &str, adt_def: ty::AdtDef<'tcx>) -> String {
        let generics = adt_def.type_scheme(self.tcx).generics;
        let applied_ty = iter::once(name.to_owned()).chain(generics.types.map(|p| p.name.as_str().to_string())).join(" ");
        let mut variants = adt_def.variants.iter().map(|variant| {
            match variant.kind {
                ty::VariantKind::Unit =>
                    format!("| {} {{}} : {}", variant.name, applied_ty),
                ty::VariantKind::Tuple => {
                    let fields = variant.fields.iter().map(|f| {
                        self.transpile_ty(f.unsubst_ty())
                    });
                    let ty = fields.chain(iter::once(applied_ty.clone())).join(" → ");
                    format!("| {} {{}} : {}", variant.name, ty)
                }
                ref data => panic!("unimplemented: enum variant {:?}", data)
            }
        });
        format!("inductive {} :=\n{}", self.as_generic_ty_def(None), variants.join("\n"))
    }

    fn transpile_associated_types(&self, def_id: DefId) -> Vec<String> {
        self.trait_predicates_without_markers(def_id).flat_map(|trait_pred| {
            let trait_def = self.tcx.lookup_trait_def(trait_pred.def_id());
            trait_def.associated_type_names.iter().map(|name| {
                format!("({} : Type)", self.transpile_associated_type(trait_pred.trait_ref, &name))
            }).collect_vec()
        }).collect()
    }

    fn transpile_trait(&self, name: &str) -> String {
        let assoc_ty_substs = self.get_assoc_ty_substs(self.def_id);
        let supertraits = self.trait_predicates_without_markers(self.def_id)
            .filter(|trait_pred| trait_pred.def_id() != self.def_id)
            .map(|trait_pred| self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs))
            .collect_vec();
        let extends = if supertraits.is_empty() { "".to_owned() } else {
            format!(" extends {}", supertraits.into_iter().join(", "))
        };

        let only_path = format!("traits.\"{}\".only", name);
        let only: Option<HashSet<_>> = self.config.config.lookup(&only_path).map(|only| ::toml_value_as_str_array(only).into_iter().collect());
        let items = self.tcx.trait_items(self.def_id).iter().filter_map(|item| match *item {
            ty::ImplOrTraitItem::TypeTraitItem(_) => None,
            ty::ImplOrTraitItem::MethodTraitItem(ref method) => {
                // FIXME: Do something more clever than ignoring default method overrides
                if self.tcx.provided_trait_methods(self.def_id).iter().any(|m| m.name == method.name) ||
                    only.iter().any(|only| !only.contains(&*method.name.as_str())) {
                    None
                } else {
                    let ty = self.transpile_ty(self.tcx.lookup_item_type(method.def_id).ty);
                    Some(format!("({} : {})", method.name, ty))
                }
            }
            ty::ImplOrTraitItem::ConstTraitItem(_) =>
                panic!("unimplemented: const trait items"),
        }).collect_vec();
        format!("structure {} {}{} {}",
                self.as_generic_ty_def(Some("[class]")),
                self.transpile_associated_types(self.def_id).join(" "),
                extends,
                if items.is_empty() { "".to_owned() }
                else { format!(":= mk () ::\n{}", items.join("\n")) })
    }

    fn transpile_trait_impl(&self) -> String {
        let trait_ref = self.tcx.impl_trait_ref(self.def_id).unwrap();

        let mut assoc_ty_substs = self.get_assoc_ty_substs(self.def_id);
        for item in self.tcx.impl_items.borrow().get(&self.def_id).unwrap() {
            if let ty::ImplOrTraitItem::TypeTraitItem(ref assoc_ty) = self.tcx.impl_or_trait_item(item.def_id()) {
                assoc_ty_substs.insert(self.transpile_associated_type(trait_ref, &assoc_ty.name), self.transpile_ty(assoc_ty.ty.unwrap()));
            }
        }
        let mut trait_params = self.trait_predicates_without_markers(self.def_id).map(|trait_pred| {
                format!(" [{}]", self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs))
        });

        let supertraits = self.trait_predicates_without_markers(trait_ref.def_id).map(|p| p.subst(self.tcx, trait_ref.substs)).filter_map(|trait_pred| {
            if trait_pred.def_id() == trait_ref.def_id {
                return None;
            }
            // explicit dependency edge
            self.infer_trait_impl(trait_pred.trait_ref);
            Some(format!("(_ : {})", self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs)))
        });

        let only_path = format!("traits.\"{}\".only", &self.name_def_id(trait_ref.def_id));
        let only: Option<HashSet<_>> = self.config.config.lookup(&only_path).map(|only| ::toml_value_as_str_array(only).into_iter().collect());
        let items = self.tcx.impl_items.borrow().get(&self.def_id).unwrap().iter().filter_map(|item| match self.tcx.impl_or_trait_item(item.def_id()) {
            ty::ImplOrTraitItem::TypeTraitItem(_) =>
                None,
            ty::ImplOrTraitItem::MethodTraitItem(ref method) => {
                // FIXME: Do something more clever than ignoring default method overrides
                if self.tcx.provided_trait_methods(trait_ref.def_id).iter().any(|m| m.name == method.name) ||
                    only.iter().any(|only| !only.contains(&*method.name.as_str())) {
                    None
                } else {
                    Some(format!("{} := {}", method.name, self.name_def_id(method.def_id)))
                }
            }
            ty::ImplOrTraitItem::ConstTraitItem(_) =>
                panic!("unimplemented: const trait items"),
        }).collect_vec();

        format!("definition {}{} := ⦃\n  {}\n⦄",
                self.as_generic_ty_def(Some("[instance]")),
                trait_params.join(""),
                iter::once(self.transpile_trait_ref(trait_ref, &assoc_ty_substs)).chain(supertraits).chain(items).join(",\n  "))
    }

    fn transpile_fn(&self, name: String, decl: &FnDecl) -> String {
        let param_names = decl.inputs.iter().enumerate().map(|(i, param)| match param.pat.node {
            PatKind::Ident(_, ref ident, _) => krate::mk_lean_name(&ident.node.name.to_string()),
            _ => format!("p{}", i),
        }).collect();
        ::trans::fun::FnTranspiler::new(self, param_names).transpile_fn(name)
    }

    pub fn transpile_def_id(&self) -> Option<String> {
        let name = self.name();
        Some(match self.tcx.map.def_key(self.def_id).disambiguated_data.data {
            DefPathData::Impl(_) => {
                if self.tcx.impl_trait_ref(self.def_id).is_some() &&
                    !self.is_marker_trait(self.tcx.impl_trait_ref(self.def_id).unwrap().def_id) {
                    self.transpile_trait_impl()
                } else { return None }
            }
            DefPathData::Type(_) => {
                // traits are weird
                if let front::map::Node::NodeItem(&hir::Item { node: hir::Item_::ItemTrait(..), .. }) =
                    self.tcx.map.get(self.node_id()) {
                    if !self.is_marker_trait(self.def_id) {
                        self.transpile_trait(&name)
                    } else { return None }
                } else {
                    match self.tcx.lookup_item_type(self.def_id).ty.sty {
                        ty::TypeVariants::TyEnum(ref adt_def, _) => self.transpile_enum(&name, adt_def),
                        ty::TypeVariants::TyStruct(ref adt_def, _) => self.transpile_struct(adt_def.struct_variant()),
                        _ => panic!("unimplemented: transpiling type {:?}", self.def_id),
                    }
                }
            }
            DefPathData::Value(_) => {
                if let Some(fn_like) = front::map::blocks::FnLikeNode::from_node(self.tcx.map.get(self.node_id())) {
                    self.transpile_fn(name, fn_like.decl())
                } else { return None }
            }
            _ => return None,
        })
    }
}
