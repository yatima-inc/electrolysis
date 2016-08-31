use std::collections::{HashMap, HashSet};
use std::iter;
use std::ops::Deref;

use itertools::Itertools;

use syntax::ast::{self, NodeId};
use rustc::hir::{self, FnDecl, PatKind};
use rustc::hir::def_id::DefId;
use rustc::ty::subst::{Subst, Substs};
use rustc::traits::*;
use rustc::ty::{self, Ty};

use joins::*;
use trans::krate::{self, CrateTranspiler};

pub enum TraitImplLookup<'tcx> {
    Static { impl_def_id: DefId, params: Vec<String>, substs: Substs<'tcx> },
    Dynamic { param: String },
}

impl<'tcx> TraitImplLookup<'tcx> {
    pub fn to_string<'a>(self, trans: &ItemTranspiler) -> String {
        match self {
            TraitImplLookup::Static { impl_def_id, params, substs } =>
                format!("({} {})", trans.name_def_id(impl_def_id), substs.types().map(|ty| {
                    trans.transpile_ty(ty)
                }).chain(params).join(" ")),
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
        // the primary way of adding dependencies: if some definition textually relies on another one,
        // it will call `name_def_id` at some point
        self.add_dep(did);
        krate::name_def_id(self.tcx, did)
    }

    fn transpile_trait_ref_args(&self, trait_ref: ty::TraitRef) -> Vec<String> {
        trait_ref.substs.types().map(|ty| {
            self.transpile_ty(ty)
        }).collect()
    }

    fn transpile_associated_type(&self, _trait_ref: ty::TraitRef, name: &ast::Name) -> String {
        // TODO: avoid name clashes without being too verbose
        //let prefix = self.name_def_id(trait_ref.def_id);
        format!("{}", name) //_{}", prefix, name)
    }

    /// `where Item = u32` ~> `{'Item': 'u32'}`
    pub fn get_assoc_ty_substs(&self, def_id: DefId) -> HashMap<String, String> {
        self.tcx.lookup_predicates(def_id).predicates.into_iter().filter_map(|trait_pred| match trait_pred {
            ty::Predicate::Projection(ty::Binder(proj_pred)) => {
                let assoc_ty = self.transpile_associated_type(proj_pred.projection_ty.trait_ref, &proj_pred.projection_ty.item_name);
                Some((assoc_ty, self.transpile_ty(&proj_pred.ty)))
            }
            _ => None,
        }).collect()
    }

    /// `Iterator, {}` ~> `(['Item'], ['Item'])`
    /// `Iterator, {'Item': 'u32'}` ~> `(['u32'], [])`
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

    /// `Add<T, RHS=S>` ~> `'Add T'`
    pub fn transpile_trait_ref_no_assoc_tys(&self, trait_ref: ty::TraitRef) -> String {
        (&self.name_def_id(trait_ref.def_id), self.transpile_trait_ref_args(trait_ref)).join(" ")
    }

    /// `Add<T>` ~> `'Add T RHS'`
    /// `Add<T, RHS=S>` ~> `'Add T S'`
    pub fn transpile_trait_ref(&self, trait_ref: ty::TraitRef<'tcx>, assoc_ty_substs: &HashMap<String, String>) -> String {
        let associated_types = self.transpile_trait_ref_assoc_tys(trait_ref, assoc_ty_substs).0;
        (self.transpile_trait_ref_no_assoc_tys(trait_ref), associated_types).join(" ")
    }

    /// `Fn(&mut T) -> R` ~> `(R × T)'`
    pub fn ret_ty(&self, fun_ty: &ty::BareFnTy) -> String {
        let sig = fun_ty.sig.skip_binder();
        let muts = sig.inputs.iter().filter_map(|i| krate::try_unwrap_mut_ref(i));
        let out_ty = self.transpile_ty(sig.output);
        format!("({})", (out_ty, muts.map(|ty| self.transpile_ty(ty))).join(" × "))
    }

    pub fn transpile_ty(&self, ty: Ty) -> String {
        match ty.sty {
            // may as well go full classical
            ty::TypeVariants::TyBool => "Prop".to_string(),
            ty::TypeVariants::TyUint(ref ty) => ty.to_string(),
            ty::TypeVariants::TyInt(ref ty) => ty.to_string(),
            //ty::TypeVariants::TyFloat(ref ty) => ty.to_string(),
            ty::TypeVariants::TyTuple(ref tys) => match tys[..] {
                [] => "unit".to_string(),
                _ => format!("({})", tys.iter().map(|ty| self.transpile_ty(ty)).join(" × ")),
            },
            // `Fn(&mut T) -> R` ~> `'T -> sem (R × T)'`
            ty::TypeVariants::TyFnDef(_, _, ref data) | ty::TypeVariants::TyFnPtr(ref data) => {
                let sig = data.sig.skip_binder();
                let inputs = sig.inputs.iter().map(|ty| self.transpile_ty(ty));
                inputs.chain(iter::once(format!("sem {}", self.ret_ty(data)))).join(" → ")
            },
            ty::TypeVariants::TyStruct(ref adt_def, ref substs) |
            ty::TypeVariants::TyEnum(ref adt_def, ref substs) => format!(
                "({})",
                (&self.name_def_id(adt_def.did), substs.types().map(|ty| self.transpile_ty(ty))).join(" ")
            ),
            ty::TypeVariants::TyRef(_, ref data) => self.transpile_ty(data.ty),
            ty::TypeVariants::TyParam(ref param) => param.name.to_string(),
            ty::TypeVariants::TyProjection(ref proj) => self.transpile_associated_type(proj.trait_ref, &proj.item_name),
            ty::TypeVariants::TySlice(ref ty) => format!("(slice {})", self.transpile_ty(ty)),
            ty::TypeVariants::TyStr => "string".to_string(),
            ty::TypeVariants::TyTrait(_) => panic!("unimplemented: trait objects"),
            ty::TypeVariants::TyArray(ref ty, _size) =>
                format!("(list {})", self.transpile_ty(ty)),
            ty::TypeVariants::TyNever => "empty".to_string(),
            _ => match ty.ty_to_def_id() {
                Some(did) => self.name_def_id(did),
                None => panic!("unimplemented: ty {:?}", ty),
            }
        }
    }

    fn trait_predicates(&'a self, def_id: DefId) -> impl Iterator<Item=ty::TraitPredicate<'tcx>> {
        let predicates = if let Some(trait_def_id) = self.tcx.trait_of_item(def_id) {
            // for trait items, ignore predicates on trait except for the `Self: Trait` predicate
            let g = self.tcx.lookup_predicates(def_id);
            g.predicates.into_iter().chain(self.tcx.lookup_predicates(trait_def_id).predicates.into_iter().filter(|pred| match *pred {
                ty::Predicate::Trait(ref trait_pred) => trait_pred.def_id() == trait_def_id,
                _ => false,
            })).collect_vec()
        } else {
            ::itertools::Unfold::new(Some(def_id), |opt_def_id| {
                opt_def_id.map(|def_id| {
                    let g = self.tcx.lookup_predicates(def_id);
                    *opt_def_id = g.parent;
                    self.tcx.lookup_predicates(def_id).predicates
                })
            }).flat_map(|ps| ps).collect()
        };
        predicates.into_iter().filter_map(|trait_pred| match trait_pred {
            ty::Predicate::Trait(trait_pred) => Some(trait_pred.0),
            _ => None,
        })
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

    // ugh
    //
    // very incomplete implementation gleaned from the rustc sources (though those never have to
    // construct a full tree of impls)
    pub fn infer_trait_impl<'b, 'c>(&self, trait_ref: ty::TraitRef<'tcx>, infcx: &'b ::rustc::infer::InferCtxt<'b, 'tcx, 'c>) -> TraitImplLookup<'tcx> {
        let span = ::syntax::codemap::DUMMY_SP;
        let pred: ty::PolyTraitPredicate<'tcx> = ty::Binder(trait_ref).to_poly_trait_predicate();

        let mut selcx = SelectionContext::new(infcx);
        let obligation = Obligation::new(ObligationCause::misc(span, ast::DUMMY_NODE_ID), pred);
        let selection = selcx.select(&obligation).unwrap_or_else(|err| {
            panic!("obligation select: {:?} {:?}", obligation, err)
        }).unwrap();

        match selection {
            Vtable::VtableImpl(data) => {
                let nested_traits = data.nested.iter().filter_map(|obl| match obl.predicate {
                    ty::Predicate::Trait(ref trait_pred) if !self.is_marker_trait(trait_pred.skip_binder().def_id()) => {
                        let trait_ref = self.tcx.lift(&trait_pred.skip_binder().trait_ref).unwrap();
                        Some(self.infer_trait_impl(trait_ref, infcx).to_string(self))
                    }
                    _ => None,
                }).collect();

                let mut fulfill_cx = FulfillmentContext::new();
                for obl in data.nested {
                    fulfill_cx.register_predicate_obligation(&infcx, obl);
                }
                let substs = infcx.drain_fulfillment_cx_or_panic(span, &mut fulfill_cx, &data.substs);

                TraitImplLookup::Static {
                    impl_def_id: data.impl_def_id,
                    params: nested_traits,
                    substs: substs.clone()
                }
            },
            Vtable::VtableParam(_) => {
                let param = self.mk_lean_name(self.transpile_trait_ref_no_assoc_tys(trait_ref));
                TraitImplLookup::Dynamic { param: param }
            }
            Vtable::VtableClosure(_) => {
                TraitImplLookup::Dynamic {
                    // global instance in core/pre.lean
                    param: "fn".to_string()
                }
            },
            vtable => panic!("unimplemented: vtable {:?}", vtable),
        }
    }

    // `self.def_id=Iterator, attr=Some('[class]')` ~> `'Iterator [class] (T : Type₁)'`
    fn as_generic_ty_def(&self, attr: Option<&str>) -> String {
        let name = if let Some(attr) = attr { format!("{} {}", self.name(), attr) } else { self.name() };
        // traits are weird
        let generics = self.tcx.lookup_generics(self.def_id);
        (name, generics.types.iter().map(|p| format!("({} : Type₁)", p.name))).join(" ")
    }

    fn transpile_struct(&self, variant: ty::VariantDef<'tcx>) -> String {
        match variant.kind {
            ty::VariantKind::Struct => {
                let mut fields = variant.fields.iter().map(|f| {
                    format!("({} : {})", self.mk_lean_name(&*f.name.as_str()), self.transpile_ty(f.unsubst_ty()))
                });
                format!("structure {} := mk {{}} ::\n{}",
                        self.as_generic_ty_def(None),
                        fields.join("\n"))
            }
            ty::VariantKind::Tuple => {
                let mut fields = variant.fields.iter().map(|f| {
                    self.transpile_ty(f.unsubst_ty())
                });
                let name = self.as_generic_ty_def(None);
                let applied_ty = (name.clone(), self.tcx.lookup_item_type(self.def_id).generics.types.iter().map(|p| p.name.as_str().to_string())).join(" ");
                format!("inductive {} :=\nmk {{}} : {} → {}",
                        name,
                        fields.join(" → "),
                        applied_ty)
            }
            ty::VariantKind::Unit =>
                format!("structure {} := mk {{}} ::",
                        self.as_generic_ty_def(None)),
        }
    }

    fn transpile_enum(&self, name: &str, adt_def: ty::AdtDef<'tcx>) -> String {
        let generics = adt_def.type_scheme(self.tcx).generics;
        let applied_ty = (name, generics.types.iter().map(|p| p.name.as_str().to_string())).join(" ");
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
        // if no variants have data attached, add a function to extrac the discriminant
        let discr = if adt_def.variants.iter().all(|variant| variant.kind == ty::VariantKind::Unit) {
            let discrs = adt_def.variants.iter().map(|variant| {
                format!("| {}.{} := {}", name, variant.name,
                        variant.disr_val.to_u64_unchecked() as i64)
            }).join("\n");
            format!("\n\ndefinition {}.discr {} : isize := match self with\n{}\nend",
                    name,
                    (generics.types.iter().map(|p| format!("{{{} : Type₁}}", p.name)),
                     &format!("(self : {})", applied_ty)).join(" "),
                    discrs)
        } else { "".to_string() };
        format!("inductive {} :=\n{}{}",
                self.as_generic_ty_def(None), variants.join("\n"), discr)
    }

    fn transpile_static(&self) -> String {
        format!("definition {} : {} :=\n{}",
                krate::name_def_id(self.tcx, self.def_id),
                self.transpile_ty(self.tcx.lookup_item_type(self.def_id).ty),
                ::trans::fun::FnTranspiler::new(self, vec![], "ret".to_string()).transpile_mir())
    }

    fn transpile_associated_types(&self, def_id: DefId) -> Vec<String> {
        self.trait_predicates_without_markers(def_id).flat_map(|trait_pred| {
            let trait_def = self.tcx.lookup_trait_def(trait_pred.def_id());
            trait_def.associated_type_names.iter().map(|name| {
                format!("({} : Type₁)", self.transpile_associated_type(trait_pred.trait_ref, &name))
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
            format!("extends {}", supertraits.into_iter().join(", "))
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
                if items.is_empty() { "".to_string() }
                else { format!(":=\n{}", items.join("\n")) })
    }

    fn transpile_trait_impl(&self) -> String {
        let trait_ref = self.tcx.impl_trait_ref(self.def_id).unwrap();
        let mut assoc_ty_substs = self.get_assoc_ty_substs(self.def_id);
        // For `type S = T`, extend `assoc_ty_substs` by `{'S': 'T'}`
        for item in self.tcx.impl_items.borrow().get(&self.def_id).unwrap() {
            if let ty::ImplOrTraitItem::TypeTraitItem(ref assoc_ty) = self.tcx.impl_or_trait_item(item.def_id()) {
                assoc_ty_substs.insert(self.transpile_associated_type(trait_ref, &assoc_ty.name), self.transpile_ty(assoc_ty.ty.unwrap()));
            }
        }

        // `Self : Iterator<Item=T>` ~> `'[Iterator T]'`
        let mut trait_params = self.trait_predicates_without_markers(self.def_id).map(|trait_pred| {
                format!(" [{}]", self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs))
        });

        let supertrait_impls = self.tcx.normalizing_infer_ctxt(Reveal::All).enter(|infcx| {
                self.trait_predicates_without_markers(trait_ref.def_id).map(|p| p.subst(self.tcx, trait_ref.substs))
                    .filter(|trait_pred| trait_pred.def_id() != trait_ref.def_id)
                    .map(|trait_pred| self.infer_trait_impl(trait_pred.trait_ref, &infcx).to_string(self))
                    .collect_vec()
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
                (self.transpile_trait_ref(trait_ref, &assoc_ty_substs), supertrait_impls.into_iter().chain(items)).join(",\n  "))
    }

    fn transpile_fn(&self, name: String, decl: &FnDecl) -> String {
        let param_names = decl.inputs.iter().enumerate().map(|(i, param)| match param.pat.node {
            PatKind::Binding(hir::BindingMode::BindByValue(_), ref name, None) => self.mk_lean_name(&*name.node.as_str()),
            _ => format!("p{}", i),
        }).collect_vec();
        let return_expr = {
            let sig = self.tcx.lookup_item_type(self.def_id).ty.fn_sig().skip_binder();
            let muts = sig.inputs.iter().zip(param_names.iter()).filter_map(|(ty, name)| {
                krate::try_unwrap_mut_ref(ty).map(|_| name.clone())
            });
            format!("return ({})\n", ("ret", muts).join(", "))
        };

        ::trans::fun::FnTranspiler::new(self, param_names, return_expr).transpile_fn(name)
    }

    pub fn transpile_def_id(&self) -> Option<String> {
        use rustc::hir::map::Node;
        use rustc::hir::Item_;
        let name = self.name();

        let node = self.tcx.map.get(self.node_id());
        if let Some(fn_like) = hir::map::blocks::FnLikeNode::from_node(node) {
            return if let Node::NodeExpr(_) = node {
                // closure
                None
            } else {
                Some(self.transpile_fn(name, fn_like.decl()))
            }
        }

        match node {
            Node::NodeItem(item) => Some(match item.node {
                Item_::ItemExternCrate(_) | Item_::ItemUse(_) | Item_::ItemMod(_)
                | Item_::ItemForeignMod(_) => return None,
                Item_::ItemStatic(_, hir::Mutability::MutMutable, _) =>
                    panic!("unimplemented: mutable static {:?}", name),
                Item_::ItemStatic(_, hir::Mutability::MutImmutable, _) | Item_::ItemConst(..) =>
                    self.transpile_static(),
                Item_::ItemEnum(..) | Item_::ItemStruct(..) =>
                    match self.tcx.lookup_item_type(self.def_id).ty.sty {
                        ty::TypeVariants::TyEnum(ref adt_def, _) =>
                            self.transpile_enum(&name, adt_def),
                        ty::TypeVariants::TyStruct(ref adt_def, _) =>
                            self.transpile_struct(adt_def.struct_variant()),
                        _ => unreachable!(),
                    },
                Item_::ItemTrait(..) => {
                    if self.is_marker_trait(self.def_id) {
                        return None
                    }
                    self.transpile_trait(&name)
                }
                Item_::ItemDefaultImpl(..) => return None,
                Item_::ItemImpl(..) => {
                    if let Some(trait_ref) = self.tcx.impl_trait_ref(self.def_id) {
                        if !self.is_marker_trait(trait_ref.def_id) {
                            return Some(self.transpile_trait_impl())
                        }
                    }
                    return None
                }
                Item_::ItemTy(..) =>
                    format!("definition {} := {}",
                            self.as_generic_ty_def(None),
                            self.transpile_ty(self.tcx.lookup_item_type(self.def_id).ty)),
                _ => panic!("unimplemented: {:?}", item),
            }),
            Node::NodeTraitItem(_) | Node::NodeVariant(_) | Node::NodeStructCtor(_) => None,
            _ => panic!("unimplemented: {:?}", node),
        }
    }
}
