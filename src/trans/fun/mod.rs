mod component;

use std::collections::HashMap;
use std::iter;
use std::ops::Deref;

use itertools::Itertools;

use rustc_front::hir;
use rustc::mir::repr::*;
use rustc::middle::const_eval::ConstVal;
use rustc::middle::subst::Subst;
use rustc::middle::ty::{self, Ty};

use self::component::Component;
use trans::item;
use trans::krate::{self, mk_lean_name};

fn get_tuple_elem<S : AsRef<str>>(value: S, idx: usize, len: usize) -> String {
    let fsts = iter::repeat(".1").take(len - idx - 1);
    let snd = if idx == 0 { None } else { Some(".2") };
    iter::once(value.as_ref()).chain(fsts).chain(snd).join("")
}

fn detuplize(val: &str, pat: &[String], cont: &str) -> String {
    match pat {
        [ref x] => format!("let {} ← {};\n{}", x, val, cont),
        _ => format!("match {} with ({}) :=\n{}end\n", val, pat.into_iter().join(", "), cont),
    }
}

fn unwrap_refs<'tcx>(ty: Ty<'tcx>) -> Ty<'tcx> {
    match ty.sty {
        ty::TypeVariants::TyRef(_, ty::TypeAndMut { ty, .. }) => unwrap_refs(ty),
        _ => ty
    }
}

/// value that indicates whether evaluating it can panic
struct MaybeValue {
    val: String,
    total: bool,
}

impl MaybeValue {
    fn total<T: Into<String>>(val: T) -> MaybeValue { MaybeValue { val: val.into(), total: true } }
    fn partial<T: Into<String>>(val: T) -> MaybeValue { MaybeValue { val: val.into(), total: false } }
}

pub struct FnTranspiler<'a, 'tcx: 'a> {
    sup: &'a item::ItemTranspiler<'a, 'tcx>,
    param_names: Vec<String>,
    return_expr: String,
    prelude: Vec<String>,
    refs: HashMap<usize, &'a Lvalue<'tcx>>,
}

impl<'a, 'tcx> Deref for FnTranspiler<'a, 'tcx> {
    type Target = item::ItemTranspiler<'a, 'tcx>;

    fn deref(&self) -> &item::ItemTranspiler<'a, 'tcx> {
        self.sup
    }
}

impl<'a, 'tcx> FnTranspiler<'a, 'tcx> {
    pub fn new(sup: &'a item::ItemTranspiler<'a, 'tcx>, param_names: Vec<String>, return_expr: String) -> FnTranspiler<'a, 'tcx> {
        FnTranspiler {
            sup: sup,
            param_names: param_names,
            return_expr: return_expr,
            prelude: Default::default(),
            refs: Default::default(),
        }
    }

    fn mir(&self) -> &'a Mir<'tcx> {
        &self.mir_map.map[&self.node_id()]
    }

    fn local_name(&self, lv: &Lvalue) -> String {
        match *lv {
            Lvalue::Var(idx) => mk_lean_name(&*self.mir().var_decls[idx as usize].name.as_str()),
            Lvalue::Temp(idx) => format!("t{}", idx),
            Lvalue::Arg(idx) => self.param_names[idx as usize].clone(),
            Lvalue::ReturnPointer => "ret".to_string(),
            _ => panic!("not a local: {:?}", lv),
        }
    }

    fn deref_mut(&self, lv: &Lvalue) -> Option<&Lvalue<'tcx>> {
        if let Some(lv_idx) = self.lvalue_idx(lv) {
            if let Some(lv) = self.refs.get(&lv_idx) {
                return Some(lv)
            }
        }
        None
    }

    fn lvalue_name(&self, lv: &Lvalue) -> Option<String> {
        if let Some(lv) = self.deref_mut(lv) {
            return self.lvalue_name(lv)
        }

        Some(match *lv {
            Lvalue::Var(..) | Lvalue::Temp(..) | Lvalue::Arg(..) | Lvalue::ReturnPointer => self.local_name(lv),
            Lvalue::Static(did) => self.name_def_id(did),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                return self.lvalue_name(base),
            Lvalue::Projection(_) => return None,
        })
    }

    fn num_locals(&self) -> usize {
        self.mir().var_decls.len() + self.mir().temp_decls.len() + 1
    }

    fn locals(&self) -> Vec<String> {
        self.mir().var_decls.iter().enumerate().map(|(idx, _)| Lvalue::Var(idx as u32))
            .chain(self.mir().temp_decls.iter().enumerate().map(|(idx, _)| Lvalue::Temp(idx as u32)))
            .chain(iter::once(Lvalue::ReturnPointer))
            .map(|lv| self.local_name(&lv))
            .collect()
    }

    fn get_lvalue(&self, lv: &Lvalue<'tcx>) -> String {
        if let Some(lv) = self.deref_mut(lv) {
            return self.get_lvalue(lv)
        }
        if let Some(name) = self.lvalue_name(lv) {
            return name
        }

        match *lv {
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.get_lvalue(base),
            Lvalue::Projection(box Projection {
                elem: ProjectionElem::Field(ref field, _),
                base: Lvalue::Projection(box Projection {
                    ref base,
                    elem: ProjectionElem::Downcast(..),
                }),
            }) =>
                format!("{}_{}", self.get_lvalue(base), field.index()),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(ref field, _) }) =>
                match unwrap_refs(self.lvalue_ty(base)).sty {
                    ty::TypeVariants::TyTuple(ref tys) =>
                        get_tuple_elem(self.get_lvalue(base), field.index(), tys.len()),
                    ty::TypeVariants::TyStruct(ref adt_def, _) => {
                        if adt_def.struct_variant().is_tuple_struct() {
                            format!("match {} with {} x := x end",
                                    get_tuple_elem(self.get_lvalue(base), field.index(), adt_def.struct_variant().fields.len()),
                                    self.name_def_id(adt_def.did))
                        } else {
                            format!("({}.{} {})",
                                    self.name_def_id(adt_def.did),
                                    mk_lean_name(&*adt_def.struct_variant().fields[field.index()].name.as_str()),
                                    self.get_lvalue(base))
                        }
                    }
                    ty::TypeVariants::TyClosure(..) =>
                        self.param_names[field.index()].clone(),
                    ref ty => panic!("unimplemented: accessing field of {:?}", ty),
                },
            _ => panic!("unimplemented: loading {:?}", lv),
        }
    }

    fn lvalue_ty(&self, lv: &Lvalue<'tcx>) -> Ty<'tcx> {
        self.mir().lvalue_ty(self.tcx, lv).to_ty(self.tcx)
    }

    fn lvalue_idx(&self, lv: &Lvalue) -> Option<usize> {
        match *lv {
            Lvalue::Var(idx) => Some(idx as usize),
            Lvalue::Temp(idx) => Some(self.mir().var_decls.len() + idx as usize),
            Lvalue::ReturnPointer => Some(self.num_locals() - 1),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.lvalue_idx(base),
            _ => None,
        }
    }

    fn set_lvalue(&self, lv: &Lvalue<'tcx>, val: &str) -> String {
        if let Some(lv) = self.deref_mut(lv) {
            return self.set_lvalue(lv, val)
        }
        if let Some(name) = self.lvalue_name(lv) {
            return format!("let {} ← {};\n", name, val)
        }
        match *lv {
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.set_lvalue(base, val),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(ref field, _) }) => {
                let base_name = self.lvalue_name(base).ok_or_else(|| format!("ugh, nested fields assignments? {:?}", lv)).unwrap();
                match unwrap_refs(self.lvalue_ty(base)).sty {
                    ty::TypeVariants::TyStruct(ref adt_def, _) => {
                        let field_name = adt_def.struct_variant().fields[field.index()].name;
                        format!("let {} ← ⦃ {}, {} := {}, {} ⦄;\n", base_name, self.name_def_id(adt_def.did), field_name, val, base_name)
                    },
                    ref ty => panic!("unimplemented: setting field of {:?}", ty),
                }
            }
            _ => panic!("unimplemented: setting lvalue {:?}", lv),
        }
    }

    fn set_lvalues_option<'b>(&self, lvs: Vec<&'b Lvalue<'tcx>>, val: &str, cont: &str) -> String {
        let (direct_dests, indirect_dests): (Vec<_>, Vec<_>) = lvs.into_iter().map(|lv| {
            match self.lvalue_name(lv) {
                Some(name) => (name, None),
                None => (self.local_name(lv), Some(self.set_lvalue(self.deref_mut(lv).unwrap(), &self.local_name(lv))))
            }
        }).unzip();
        let indirect_dests = indirect_dests.into_iter().filter_map(|x| x).join("");
        format!("do tmp__ ← {};\n{}", val,
                detuplize("tmp__", &direct_dests[..], &(indirect_dests + cont)))
    }

    fn transpile_constval(&self, val: &ConstVal) -> String {
        match *val {
            ConstVal::Bool(b) => b.to_string(),
            ConstVal::Integral(i) => match i.int_type().unwrap() {
                ::syntax::attr::IntType::SignedInt(_) =>
                    format!("({} : int)", i.to_u64_unchecked() as i64),
                ::syntax::attr::IntType::UnsignedInt(_) =>
                    format!("({} : nat)", i.to_u64_unchecked()),
            },
            ConstVal::Str(ref s) => format!("\"{}\"", s),
            _ => panic!("unimplemented: literal {:?}", val),
        }
    }

    fn transpile_constant(&self, c: &Constant) -> String {
        match c.literal {
            Literal::Value { ref value } => self.transpile_constval(value),
            _ => panic!("unimplemented: constant {:?}", c),
        }
    }

    fn get_operand(&self, op: &Operand<'tcx>) -> String {
        match *op {
            Operand::Consume(ref lv) => self.get_lvalue(lv),
            Operand::Constant(ref c) => self.transpile_constant(c),
        }
    }

    fn get_rvalue(&mut self, rv: &Rvalue<'tcx>) -> MaybeValue {
        MaybeValue::total(match *rv {
            Rvalue::Use(Operand::Consume(Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Index(ref idx) }))) =>
                return MaybeValue::partial(format!("slice._T_.slice_SliceExt.get_unchecked {} {}", self.get_lvalue(base), self.get_operand(idx))),
            Rvalue::Use(ref op) => self.get_operand(op),
            Rvalue::UnaryOp(op, ref operand) =>
                format!("{} {}", match op {
                    UnOp::Not if self.mir().operand_ty(self.tcx, operand).is_bool() => "bool.bnot",
                    UnOp::Not => "NOT",
                    UnOp::Neg => "-",
                }, self.get_operand(operand)),
            Rvalue::BinaryOp(op, ref o1, ref o2) => {
                let (so1, so2) = (self.get_operand(o1), self.get_operand(o2));
                return match op {
                    BinOp::Sub if !self.mir().operand_ty(self.tcx, o1).is_signed() => MaybeValue::partial(format!("{} {} {}", "checked.sub", so1, so2)),
                    BinOp::Div => MaybeValue::partial(format!("{} {} {}", "checked.div", so1, so2)),
                    BinOp::Rem => MaybeValue::partial(format!("{} {} {}", "checked.mod", so1, so2)),
                    BinOp::Shl => MaybeValue::partial(format!("{} {} {}", "checked.shl", so1, so2)),
                    BinOp::Shr => MaybeValue::partial(format!("{} {} {}", "checked.shr", so1, so2)),
                    _ => MaybeValue::total(format!("{} {} {}", so1, match op {
                        BinOp::Add => "+",
                        BinOp::Sub => "-",
                        BinOp::Mul => "*",
                        BinOp::Eq => "=",
                        BinOp::Lt => "<",
                        BinOp::Le => "<=",
                        BinOp::Ne => "≠",
                        BinOp::Ge => ">=",
                        BinOp::Gt => ">",
                        _ => panic!("unimplemented: operator {:?}", op),
                    }, so2))
                }
            }
            Rvalue::Cast(CastKind::Misc, ref op, ref ty) if self.mir().operand_ty(self.tcx, op).is_integral() && ty.is_integral() => {
                format!("({}.of_num {})",
                        if ty.is_signed() { "int" } else { "nat" },
                        self.get_operand(op))
            }
            Rvalue::Ref(_, BorrowKind::Shared, ref lv) =>
                return self.get_rvalue(&Rvalue::Use(Operand::Consume(lv.clone()))),
            Rvalue::Aggregate(AggregateKind::Tuple, ref ops) => {
                let mut ops = ops.iter().map(|op| self.get_operand(op));
                format!("({})", ops.join(", "))
            }
            Rvalue::Aggregate(AggregateKind::Adt(ref adt_def, variant_idx, _), ref ops) => {
                self.add_dep(adt_def.did);

                let variant = &adt_def.variants[variant_idx];
                let mut ops = ops.iter().map(|op| self.get_operand(op));
                format!("{}{} {}",
                        self.name_def_id(variant.did),
                        if adt_def.adt_kind() == ty::AdtKind::Struct && !adt_def.struct_variant().is_tuple_struct() { ".mk" } else { "" },
                        ops.join(" "))
            }
            Rvalue::Aggregate(AggregateKind::Closure(def_id, _), ref ops) => {
                let upvars = ops.iter().map(|op| match *op {
                    Operand::Consume(ref lv) => lv,
                    Operand::Constant(_) => unreachable!(),
                }).collect_vec();
                if upvars.iter().any(|lv| krate::try_unwrap_mut_ref(self.lvalue_ty(lv)).map(|_| lv).is_some()) {
                    panic!("unimplemented: mutable capturing closure")
                }
                let decl = match self.tcx.map.expect_expr(self.tcx.map.as_local_node_id(def_id).unwrap()).node {
                    hir::Expr_::ExprClosure(_, ref decl, _) => decl,
                    _ => unreachable!(),
                };
                let param_names = upvars.iter().map(|lv| self.lvalue_name(lv).unwrap()).chain(
                    decl.inputs.iter().enumerate().map(|(i, param)| match param.pat.node {
                    hir::PatKind::Ident(_, ref ident, _) => krate::mk_lean_name(&ident.node.name.to_string()),
                    _ => format!("p{}", i),
                })).collect();
                let trans = item::ItemTranspiler { sup: self.sup.sup, def_id: def_id };
                let mut trans = FnTranspiler::new(&trans, param_names, "some ret".to_string());
                let mut comp = Component::new(&trans, START_BLOCK, trans.mir().all_basic_blocks(), None);
                let body = trans.transpile_basic_block(START_BLOCK, &mut comp);
                self.prelude.append(&mut trans.prelude);
                format!("λ{}, ({})", trans.param_names.iter().skip(upvars.len()).join(" "), body)
            }
            Rvalue::Len(ref lv) => format!("list.length {}", self.get_lvalue(lv)),
            _ => panic!("unimplemented: rvalue {:?}", rv),
        })
    }

    fn transpile_statement(&mut self, stmt: &'a Statement<'tcx>) -> String {
        match stmt.kind {
            StatementKind::Assign(ref lv, ref rv) => {
                if let Rvalue::Ref(_, BorrowKind::Mut, ref lsource) = *rv {
                    let idx = self.lvalue_idx(lv).unwrap_or_else(|| {
                        panic!("unimplemented: storing {:?}", lv)
                    });
                    self.refs.insert(idx, lsource);
                    return "".to_string()
                }
                if *lv != Lvalue::ReturnPointer && self.lvalue_ty(lv).is_nil() {
                    // optimization/rustc_mir workaround: don't save '()'
                    return "".to_string()
                }

                match self.get_rvalue(rv) {
                    MaybeValue { val, total: true } => self.set_lvalue(lv, &val),
                    MaybeValue { val, total: false } =>
                        format!("do tmp__ ← {};\n{}", &val, self.set_lvalue(lv, "tmp__")),
                }
            }
        }
    }

    fn transpile_basic_block_rec(&mut self, bb: BasicBlock, comp: &Component) -> String {
        if comp.header == Some(bb) {
            format!("some (inl {})\n", comp.state_val)
        } else if !comp.blocks.contains(&bb) {
            // leaving a loop
            format!("do tmp__ ← {};\nsome (inr tmp__)", self.transpile_basic_block(bb, &comp.outer.unwrap()))
        } else {
            self.transpile_basic_block(bb, comp)
        }
    }

    fn call_return_dests<'b>(&self, call: &'b Terminator<'tcx>) -> Vec<&'b Lvalue<'tcx>> {
        match call {
            &Terminator::Call { ref args, destination: Some((ref lv, _)), .. } => {
                let muts = args.iter().filter_map(|op| match *op {
                    Operand::Consume(ref lv) => krate::try_unwrap_mut_ref(self.lvalue_ty(lv)).map(|_| lv),
                    Operand::Constant(_) => None,
                });
                iter::once(lv).chain(muts).collect()
            }
            _ => vec![],
        }
    }

    fn transpile_basic_block(&mut self, bb: BasicBlock, comp: &Component) -> String {
        macro_rules! rec { ($bb:expr) => { self.transpile_basic_block_rec($bb, comp) } }

        if let Some(l) = comp.loops.clone().into_iter().find(|l| l.contains(&bb)) {
            let mut l_comp = Component::new(self, bb, l, Some(&comp));
            let (defs, _) = Component::defs_uses(comp.blocks.iter().filter(|bb| !l_comp.blocks.contains(bb)), self);
            let (l_defs, l_uses) = Component::defs_uses(l_comp.blocks.iter(), self);
            let nonlocal_uses = self.locals().into_iter().filter(|v| defs.contains(v) && l_uses.contains(v) && !l_defs.contains(v));
            let state_vars = self.locals().into_iter().filter(|v| defs.contains(v) && l_defs.contains(v)).collect_vec();
            l_comp.state_val = format!("({})", state_vars.iter().join(", "));
            let name = format!("{}.loop_{}", self.name(), bb.index());
            let app = iter::once(name).chain(nonlocal_uses).join(" ");
            let body = self.transpile_basic_block(bb, &l_comp);
            self.prelude.push(format!("definition {} state__ :=\n{}", app,
                                      detuplize("state__", &state_vars, &body)));
            return format!("loop' ({}) {}", app, l_comp.state_val);
        }

        let data = self.mir().basic_block_data(bb);
        let stmts = data.statements.iter().map(|s| self.transpile_statement(s)).collect_vec();
        let terminator = match data.terminator {
            Some(ref terminator) => Some(match *terminator {
                Terminator::Goto { target } =>
                    rec!(target),
                Terminator::If { ref cond, targets: (bb_if, bb_else) } =>
                    format!("if {} then\n{} else\n{}", self.get_operand(cond),
                    rec!(bb_if),
                    rec!(bb_else)),
                Terminator::Return => self.return_expr.clone(),
                Terminator::Call { ref func, ref args, destination: Some((_, target)), ..  } => {
                    let call = match *func {
                        Operand::Constant(Constant { literal: Literal::Item { def_id, substs, .. }, .. }) => {
                            let substs = substs.clone();
                            let (def_id, substs) = match self.tcx.trait_of_item(def_id) {
                                Some(trait_def_id) => {
                                    // from trans::meth::trans_method_callee
                                    let trait_ref = substs.to_trait_ref(self.tcx, trait_def_id);

                                    match self.infer_trait_impl(trait_ref) {
                                        item::TraitImplLookup::Static { impl_def_id, substs: impl_substs, .. }  => {
                                            let method = self.tcx.impl_or_trait_item(def_id).as_opt_method().unwrap();
                                            let trait_def = self.tcx.lookup_trait_def(method.container.id());
                                            let method = trait_def.ancestors(impl_def_id).fn_defs(&self.tcx, method.name).next().unwrap().item;
                                            let impl_substs = impl_substs.with_method_from(&substs);
                                            (method.def_id, if method.container.id() == impl_def_id { impl_substs } else { substs })
                                        }
                                        item::TraitImplLookup::Dynamic { .. } =>
                                            (def_id, substs)
                                    }
                                }
                                _ => (def_id, substs)
                            };

                            // analogous to transpile_fn

                            // TODO: should probably substitute and make explicit
                            let ty_params = self.tcx.lookup_item_type(def_id).generics.types.iter().map(|_| "_".to_string()).collect_vec();
                            let assoc_ty_substs = self.get_assoc_ty_substs(def_id);
                            let trait_params = self.trait_predicates_without_markers(def_id).flat_map(|trait_pred| {
                                let free_assoc_tys = self.transpile_trait_ref_assoc_tys(trait_pred.trait_ref, &assoc_ty_substs).1;
                                let free_assoc_tys = free_assoc_tys.into_iter().map(|_| "_".to_string());
                                let trait_param = self.infer_trait_impl(trait_pred.trait_ref.subst(self.tcx, &substs)).to_string(self);
                                free_assoc_tys.chain(iter::once(trait_param))
                            });
                            iter::once(format!("@{}", self.name_def_id(def_id))).chain(ty_params).chain(trait_params).join(" ")
                        },
                        Operand::Constant(_) => unreachable!(),
                        Operand::Consume(ref lv) => self.get_lvalue(lv),
                    };
                    let call = iter::once(call).chain(args.iter().map(|op| self.get_operand(op))).join(" ");
                    let rec = rec!(target);
                    self.set_lvalues_option(self.call_return_dests(&terminator), &call, &rec)
                }
                Terminator::Call { destination: None, .. } =>
                    "none\n".to_string(),
                Terminator::Switch { ref discr, ref adt_def, ref targets } => {
                    let value = self.get_lvalue(discr);
                    let mut arms = adt_def.variants.iter().zip(targets).map(|(var, &target)| {
                        let vars = (0..var.fields.len()).into_iter().map(|i| format!("{}_{}", value, i));
                        format!("| {} :=\n{}", iter::once(self.name_def_id(var.did)).chain(vars).join(" "), rec!(target))
                    });
                    format!("match {} with\n{}end\n", value, arms.join(" "))
                },
                Terminator::SwitchInt { ref discr, switch_ty: _, ref values, ref targets } => {
                    let arms = values.iter().zip(targets).map(|(val, &target)| {
                        format!("| {} :=\n{}", self.transpile_constval(val), rec!(target))
                    }).collect_vec();
                    let fallback = format!("| _ :=\n{}", rec!(*targets.last().unwrap()));
                    format!("match {} with\n{}\nend\n", self.get_lvalue(discr),
                            arms.into_iter().chain(iter::once(fallback)).join(""))
                },
                Terminator::Drop { target, .. } => rec!(target),
                Terminator::Resume => String::new(),
            }),
            None => None,
        };
        stmts.into_iter().chain(terminator.into_iter()).join("")
    }

    pub fn transpile_fn(&mut self, name: String) -> String {
        // FIXME... or not
        if name.starts_with("tuple._A__B__C__D") {
            return "".to_string()
        }

        let params = self.param_names.iter().zip(self.mir().arg_decls.iter()).map(|(name, arg)| {
            format!("({} : {})", name, self.transpile_ty(&arg.ty))
        }).collect_vec();

        let mut comp = Component::new(self, START_BLOCK, self.mir().all_basic_blocks(), None);
        let body = self.transpile_basic_block(START_BLOCK, &mut comp);

        let ty_params = self.tcx.lookup_item_type(self.def_id).generics.types.iter().map(|p| format!("{{{} : Type}}", p.name)).collect_vec();
        let assoc_ty_substs = self.get_assoc_ty_substs(self.def_id);
        let trait_params = self.trait_predicates_without_markers(self.def_id).flat_map(|trait_pred| {
            let free_assoc_tys = self.transpile_trait_ref_assoc_tys(trait_pred.trait_ref, &assoc_ty_substs).1;
            let free_assoc_tys = free_assoc_tys.into_iter().map(|ty| format!("({} : Type)", ty));
            let trait_param = format!("[{} : {}]",
                                      mk_lean_name(self.transpile_trait_ref_no_assoc_tys(trait_pred.trait_ref)).replace('.', "_"),
                                      self.transpile_trait_ref(trait_pred.trait_ref, &assoc_ty_substs));
            free_assoc_tys.chain(iter::once(trait_param))
        }).collect_vec();

        let is_rec = self.is_recursive(self.def_id);
        let body = if is_rec {
            format!("fix_opt (λ{}, {})", name, body)
        } else { body };
        let prelude = self.prelude.drain(..).collect_vec();
        if prelude.is_empty() {
            let def = format!("definition {} :=\n{}",
                              iter::once(name).chain(ty_params).chain(trait_params).chain(params).join(" "),
                              body);
            prelude.into_iter().chain(iter::once(def)).join("\n\n")
        } else {
            format!("section
{}

{}

definition {} :=\n{}
end",
                    vec![ty_params, trait_params, params].into_iter().map(|p| {
                        format!("parameters {}", p.into_iter().join(" "))
                    }).join("\n"),
                    prelude.into_iter().join("\n\n"),
                    iter::once(name).join(" "), body)
        }
    }
}
