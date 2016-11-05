mod component;

use std::collections::HashMap;
use std::iter;
use std::ops::Deref;

use itertools::Itertools;

use rustc::hir;
use rustc::hir::def::CtorKind;
use rustc::hir::def_id::DefId;
use rustc::mir::repr::*;
use rustc::middle::const_val::ConstVal;
use rustc::traits;
use rustc::ty::{self, Ty};
use rustc::ty::subst::{Subst, Substs};
use rustc_data_structures::indexed_vec::Idx;
use syntax::ast;

use self::component::Component;
use joins::*;
use trans::item;
use trans::krate;
use trans::TransResult;

/// `mk_tuple("x", "y")` ~> `"(x, y)"`
fn mk_tuple<It: Iterator<Item=String>>(it: It) -> String {
    match it.collect_vec()[..] {
        [] => "⋆".to_string(),
        [ref x] => x.clone(),
        ref xs => format!("({})", xs.into_iter().join(", "))
    }
}

/// `get_tuple_elem('x', 1, 3)` ~> `'x.1.2'`
fn get_tuple_elem<S : AsRef<str>>(value: S, idx: usize, len: usize) -> String {
    let fsts = iter::repeat(".1").take(len - idx - 1);
    let snd = if idx == 0 { None } else { Some(".2") };
    iter::once(value.as_ref()).chain(fsts).chain(snd).join("")
}

// TODO: instead implement pattern let in Lean
fn detuplize(val: &str, pat: &[String], cont: &str) -> String {
    match *pat {
        [ref x] => format!("let' {} ← {};\n{}", x, val, cont),
        _ => format!("match {} with ({}) :=\n{}end\n", val, pat.into_iter().join(", "), cont),
    }
}

/// `&&T` ~> `T`
fn unwrap_refs<'tcx>(ty: Ty<'tcx>) -> Ty<'tcx> {
    match ty.sty {
        ty::TypeVariants::TyRef(_, ty::TypeAndMut { ty, mutbl: hir::Mutability::MutImmutable }) => unwrap_refs(ty),
        _ => ty
    }
}

fn lvalue_of_operand<'a, 'tcx>(op: &'a Operand<'tcx>) -> &'a Lvalue<'tcx> {
    match *op {
        Operand::Consume(ref lv) => lv,
        Operand::Constant(_) => panic!("not an lvalue: {:?}", op),
    }
}

trait AsLocal {
    fn as_local(&self) -> Option<Local>;
}

impl<'tcx> AsLocal for Lvalue<'tcx> {
    fn as_local(&self) -> Option<Local> {
        match *self {
            Lvalue::Local(local) => Some(local),
            _ => None,
        }
    }
}

/// Value that indicates whether evaluating it can panic
struct MaybeValue {
    val: String,
    total: bool,
}

impl MaybeValue {
    fn total<T: ToString>(val: T) -> MaybeValue { MaybeValue { val: val.to_string(), total: true } }
    fn partial<T: ToString>(val: T) -> MaybeValue { MaybeValue { val: val.to_string(), total: false } }

    fn to_partial(self) -> String {
        if self.total {
            format!("return ({})", self.val)
        } else { self.val }
    }
    fn to_total(self) -> String {
        if !self.total {
            panic!("MaybeValue::to_total called on partial value {}", self.val)
        }
        self.val
    }

    fn and_then<F: FnOnce(String) -> MaybeValue>(self, depth: u32, f: F) -> MaybeValue {
        if self.total {
            f(self.val)
        } else {
            let tmp = format!("«$tmp{}»", depth);
            let new = f(tmp.clone());
            MaybeValue::partial(format!(
                "do {} ← {};\n{}", tmp, self.val, new.to_partial()))
        }
    }
    fn map<F: FnOnce(String) -> String>(self, depth: u32, f: F) -> String {
        self.and_then(depth, |var| MaybeValue::partial(f(var))).val
    }

    fn and_then_multi<It, F>(depth: u32, vals: It, f: F) -> MaybeValue
        where It: Iterator<Item=MaybeValue>,
              F: FnOnce(Vec<String>) -> MaybeValue,
    {
        fn rec<It, F>(depth: u32, mut vals: It, mut vars: Vec<String>, f: F) -> MaybeValue
            where It: Iterator<Item=MaybeValue>,
            F: FnOnce(Vec<String>) -> MaybeValue,
        {
            match vals.next() {
                None => f(vars),
                Some(val) => val.and_then(depth, |var| {
                    vars.push(var);
                    rec(depth + 1, vals, vars, f)
                })
            }
        }
        rec(depth, vals, Vec::new(), f)
    }
    fn map_multi<It, F>(depth: u32, vals: It, f: F) -> String
        where It: Iterator<Item=MaybeValue>,
              F: FnOnce(Vec<String>) -> String,
    {
        MaybeValue::and_then_multi(depth, vals, |vars| MaybeValue::partial(f(vars))).val
    }
}

#[derive(Clone)]
pub struct FnTranspiler<'a, 'tcx: 'a> {
    sup: &'a item::ItemTranspiler<'a, 'tcx>,
    mir: &'a Mir<'tcx>,
    // helper definitions to be prepended to the translation
    prelude: Vec<String>,
    refs: HashMap<Local, Lvalue<'tcx>>,
}

impl<'a, 'tcx> Deref for FnTranspiler<'a, 'tcx> {
    type Target = item::ItemTranspiler<'a, 'tcx>;

    fn deref(&self) -> &item::ItemTranspiler<'a, 'tcx> {
        self.sup
    }
}

impl<'a, 'tcx> FnTranspiler<'a, 'tcx> {
    pub fn new(sup: &'a item::ItemTranspiler<'a, 'tcx>) -> FnTranspiler<'a, 'tcx> {
        FnTranspiler {
            sup: sup,
            mir: &sup.mir_map.map[&sup.def_id],
            prelude: Default::default(),
            refs: Default::default(),
        }
    }

    fn local_name(&self, local: Local) -> String {
        let opt_name = self.mir.local_decls[local].name;
        match self.mir.local_kind(local) {
            LocalKind::Var => self.mk_lean_name(&*opt_name.unwrap().as_str()),
            LocalKind::Temp => format!("t{}", local.index()),
            LocalKind::Arg => match opt_name {
                Some(name) => format!("{}ₐ", name),
                None => format!("a{}", local.index()),
            },
            LocalKind::ReturnPointer => "ret".to_string(),
        }
    }

    fn param_names(&self) -> ::std::vec::IntoIter<String> {
        self.mir.args_iter().map(|l| self.local_name(l)).collect_vec().into_iter()
    }

    fn lvalue_name(&self, lv: &Lvalue) -> Option<String> {
        match *lv {
            Lvalue::Local(local) => Some(self.local_name(local)),
            Lvalue::Static(did) => Some(self.name_def_id(did)),
            Lvalue::Projection(_) => None,
        }
    }

    fn deref_mut(&self, lv: &Lvalue<'tcx>) -> Option<Lvalue<'tcx>> {
        lv.as_local().and_then(|local| self.refs.get(&local).cloned())
    }

    fn get_lvalue(&self, lv: &Lvalue<'tcx>) -> MaybeValue {
        if let Some(name) = self.lvalue_name(lv) {
            return MaybeValue::total(name)
        }

        match *lv {
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) => {
                if let Some(ref src) = self.deref_mut(base) {
                    // read through a &mut
                    self.get_lvalue(base).and_then(0, |base| self.get_lvalue(src).and_then(1, |src| {
                        MaybeValue::partial(format!("lens.get {} {}", base, src))
                    }))
                } else {
                    self.get_lvalue(base)
                }
            }
            // glorious HACK: downcasting to an enum item should only happen directly after
            // a `match`, so just use the variable introduced in the `match`
            Lvalue::Projection(box Projection {
                elem: ProjectionElem::Field(ref field, _),
                base: Lvalue::Projection(box Projection {
                    base: Lvalue::Local(base),
                    elem: ProjectionElem::Downcast(..),
                }),
            }) =>
                MaybeValue::total(format!("{}_{}", self.local_name(base), field.index())),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Index(ref idx) }) =>
                self.get_lvalue(base).and_then(0, |base| self.get_operand(idx).and_then(1, |idx| {
                    MaybeValue::partial(format!("core.«[T] as core.slice.SliceExt».get_unchecked {} {}", base, idx))
                })),
            // `x.0`, `x.f`
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Field(ref field, _) }) =>
                self.get_lvalue(base).and_then(0, |sbase| MaybeValue::total(match unwrap_refs(self.lvalue_ty(base)).sty {
                    ty::TypeVariants::TyTuple(ref tys) =>
                        get_tuple_elem(sbase, field.index(), tys.len()),
                    ty::TypeVariants::TyAdt(ref adt_def, _) => {
                        if adt_def.struct_variant().ctor_kind == CtorKind::Fn { // tuple struct
                            format!("match {} with {}.mk {} := x{} end",
                                    sbase,
                                    self.name_def_id(adt_def.did),
                                    (0..adt_def.struct_variant().fields.len()).map(|i| format!("x{}", i)).join(" "),
                                    field.index())
                        } else {
                            format!("({}.{} {})",
                                    self.name_def_id(adt_def.did),
                                    self.mk_lean_name(&*adt_def.struct_variant().fields[field.index()].name.as_str()),
                                    sbase)
                        }
                    }
                    ty::TypeVariants::TyClosure(_, ref substs) =>
                        // captured variables become a tuple parameter
                        get_tuple_elem(sbase, field.index(), substs.upvar_tys.len()),
                    ref ty => panic!("unimplemented: accessing field of {:?}", ty),
                })),
            _ => panic!("unimplemented: loading {:?}", lv),
        }
    }

    fn lvalue_ty(&self, lv: &Lvalue<'tcx>) -> Ty<'tcx> {
        lv.ty(self.mir, self.tcx).to_ty(self.tcx)
    }

    fn update_struct(&self, adt_def: &ty::AdtDef<'tcx>, field: Field, base: &str, val: &str) -> String {
        let field_name = adt_def.struct_variant().fields[field.index()].name;
        let rest = if adt_def.struct_variant().fields.len() > 1 {
            format!(", {}", base)
        } else { "".to_string() };
        format!("⦃ {}, {} := {}{} ⦄",
                self.name_def_id(adt_def.did),
                field_name, val,
                rest)
    }

    fn set_lvalue(&self, lv: &Lvalue<'tcx>, val: &str) -> String {
        if let Some(name) = self.lvalue_name(lv) {
            if name == val { // no-op
                return "".to_string()
            } else {
                return format!("let' {} ← {};\n", name, val)
            }
        }
        match *lv {
            Lvalue::Projection(box Projection { ref base, ref elem }) =>
                self.get_lvalue(base).map(0, |sbase| match *elem {
                    ProjectionElem::Deref => {
                        if let Some(ref src) = self.deref_mut(base) {
                            self.get_lvalue(src).map(1, |src| {
                                // writing through a &mut
                                format!("do {src} ← lens.set {lens} {src} {val};\n",
                                        src=src, lens=sbase, val=val)
                            })
                        } else {
                            self.set_lvalue(base, val)
                        }
                    }
                    ProjectionElem::Field(field, _) => {
                        match unwrap_refs(self.lvalue_ty(base)).sty {
                            ty::TypeVariants::TyAdt(ref adt_def, _) =>
                                self.set_lvalue(base, &self.update_struct(adt_def, field, &sbase, val)),
                            ref ty => panic!("unimplemented: setting field of {:?}", ty),
                        }
                    }
                    ProjectionElem::Index(ref index) => {
                        self.get_operand(index).map(1, |index| {
                            MaybeValue::partial(format!("sem.lift_opt (list.update {} {} {})", sbase, index, val)).map(2, |new| {
                                self.set_lvalue(base, &new)
                            })
                        })
                    }
                    _ => panic!("unimplemented: setting lvalue {:?}", lv),
                }),
            _ => panic!("unimplemented: setting lvalue {:?}", lv),
        }
    }

    fn transpile_constval(&self, val: &ConstVal) -> String {
        match *val {
            ConstVal::Bool(b) => (if b {"tt"} else {"ff"}).to_string(),
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

    fn get_constant(&self, c: &Constant) -> MaybeValue {
        match c.literal {
            Literal::Value { ref value } => MaybeValue::total(self.transpile_constval(value)),
            Literal::Promoted { index }  => MaybeValue::total(format!("promoted_{}", index.index())),
            Literal::Item { def_id, .. } => {
                use rustc::hir::*;
                if let hir::map::Node::NodeItem(item) = self.tcx.map.get_if_local(def_id).unwrap() {
                    match item.node {
                        Item_::ItemStatic(..) | Item_::ItemConst(..) =>
                            return MaybeValue::partial(self.name_def_id(def_id)),
                        _ => {}
                    }
                }
                MaybeValue::total(self.name_def_id(def_id))
            }
        }
    }

    fn get_operand(&self, op: &Operand<'tcx>) -> MaybeValue {
        match *op {
            Operand::Consume(ref lv) => {
                if self.deref_mut(lv).is_some() {
                    panic!("unimplemented: arbitrary move of &mut {:?}", lv)
                }
                self.get_lvalue(lv)
            }
            Operand::Constant(ref c) => self.get_constant(c),
        }
    }

    fn get_rvalue(&mut self, rv: &Rvalue<'tcx>) -> MaybeValue {
        match *rv {
            Rvalue::Use(ref op) => self.get_operand(op),
            Rvalue::UnaryOp(op, ref operand) => {
                let toperand = operand.ty(self.mir, self.tcx);
                self.get_operand(operand).and_then(0, |soperand| MaybeValue::total(format!("{} {}", match op {
                    UnOp::Not if toperand.is_bool() => "bool.bnot",
                    UnOp::Not if !toperand.is_signed() => "bitnot",
                    UnOp::Not => panic!("unimplemented: signed bitwise negation"),
                    UnOp::Neg =>
                        return MaybeValue::partial(format!("checked.neg {}.bits {}",
                                                           self.transpile_ty(toperand),
                                                           soperand)),
                    }
                , soperand)))
            }
            Rvalue::BinaryOp(op, ref o1, ref o2) => {
                self.get_operand(o1).and_then(0, |so1| self.get_operand(o2).and_then(1, |so2| {
                    let to1 = o1.ty(self.mir, self.tcx);
                    let to2 = o2.ty(self.mir, self.tcx);
                    let checked_homogenous_binop = |name: &'static str| {
                        assert!(to1 == to2);
                        let name = if to1.is_signed() { format!("s{}", name) } else { name.to_string() };
                        MaybeValue::partial(format!("checked.{} {}.bits {} {}", name, self.transpile_ty(to1), so1, so2))
                    };
                    let checked_shift = |name: &'static str| {
                        let name = if to1.is_signed() { format!("s{}", name) } else { name.to_string() };
                        let name = if to2.is_signed() { name + "s" } else { name.to_string() };
                        MaybeValue::partial(format!("checked.{} {}.bits {} {}", name, self.transpile_ty(to1), so1, so2))
                    };
                    let bitop = |name, bool_name| {
                        assert!(to1 == to2);
                        if to1.is_signed() {
                            panic!("unimplemented: signed bitwise operator")
                        }
                        if to1.is_bool() {
                            MaybeValue::total(format!("{} {} {}", bool_name, so1, so2))
                        } else {
                            MaybeValue::total(format!("{} {}.bits {} {}", name, self.transpile_ty(to1), so1, so2))
                        }
                    };
                    let infix_binop = |name| MaybeValue::total(format!("{} {} {}", so1, name, so2));
                    match op {
                        BinOp::Add => checked_homogenous_binop("add"),
                        BinOp::Sub => checked_homogenous_binop("sub"),
                        BinOp::Mul => checked_homogenous_binop("mul"),
                        BinOp::Div => checked_homogenous_binop("div"),
                        BinOp::Rem => checked_homogenous_binop("rem"),
                        BinOp::Shl => checked_shift("shl"),
                        BinOp::Shr => checked_shift("shr"),
                        BinOp::BitOr => bitop("bitor", "bor"),
                        BinOp::BitAnd => bitop("bitand", "band"),
                        BinOp::BitXor => bitop("bitxor", "bxor"),
                        BinOp::Eq => infix_binop("=ᵇ"),
                        BinOp::Lt => infix_binop("<ᵇ"),
                        BinOp::Le => infix_binop("≤ᵇ"),
                        BinOp::Ne => infix_binop("≠ᵇ"),
                        BinOp::Ge => infix_binop("≥ᵇ"),
                        BinOp::Gt => infix_binop(">ᵇ"),
                    }
                }))
            }
            // checked operators used in `Assert`... but we've already checked
            Rvalue::CheckedBinaryOp(op, ref o1, ref o2) => {
                let MaybeValue { val, total } = self.get_rvalue(&Rvalue::BinaryOp(op, o1.clone(), o2.clone()));
                if total {
                    MaybeValue::total(format!("({}, tt)", val))
                } else {
                    MaybeValue::partial(format!("sem.map (λx, (x, tt)) ({})", val))
                }
            }
            Rvalue::Cast(CastKind::Misc, ref op, ref dest_ty) => {
                let op_ty = op.ty(self.mir, self.tcx);
                self.get_operand(op).and_then(0, |operand| MaybeValue::partial(
                    if op_ty.is_integral() || op_ty.is_bool() {
                        format!("({}_to_{} {})",
                                self.transpile_ty(op_ty),
                                self.transpile_ty(dest_ty),
                                operand)
                    } else if let ty::TypeVariants::TyAdt(..) = op_ty.sty {
                        format!("(isize_to_{} ({}.discr {}))",
                                self.transpile_ty(dest_ty),
                                self.name_def_id(op_ty.ty_to_def_id().unwrap()),
                                operand)
                    } else {
                        panic!("unimplemented: cast from {:?} to {:?}", op_ty, dest_ty)
                    }))
            }
            Rvalue::Cast(CastKind::Unsize, ref op, _) => self.get_operand(op),
            //Rvalue::Cast(CastKind::ReifyFnPointer, ref op, _) => self.get_operand(op),
            Rvalue::Ref(_, BorrowKind::Shared, ref lv) =>
                self.get_lvalue(lv),
            Rvalue::Aggregate(AggregateKind::Tuple, ref ops) => {
                if ops.len() == 0 {
                    MaybeValue::total("⋆")
                } else {
                    MaybeValue::and_then_multi(0, ops.iter().map(|op| self.get_operand(op)), |ops| {
                        MaybeValue::total(format!("({})", ops.join(", ")))
                    })
                }
            }
            Rvalue::Aggregate(AggregateKind::Array, ref ops) => {
                MaybeValue::and_then_multi(0, ops.iter().map(|op| self.get_operand(op)), |ops| {
                    MaybeValue::total(format!("[{}]", ops.join(", ")))
                })
            }
            Rvalue::Aggregate(AggregateKind::Adt(ref adt_def, variant_idx, _, _), ref ops) => {
                self.add_dep(adt_def.did);

                let variant = &adt_def.variants[variant_idx];
                MaybeValue::and_then_multi(0, ops.iter().map(|op| self.get_operand(op)), |ops| {
                    let mut val = self.name_def_id(variant.did);
                    if variant.ctor_kind == CtorKind::Fictive {
                        match adt_def.adt_kind() {
                            ty::AdtKind::Struct => val += ".mk",
                            ty::AdtKind::Enum =>
                                return MaybeValue::total(
                                    format!("{val} ({val}.struct.mk {})",
                                            ops.join(" "), val=val)),
                            ty::AdtKind::Union => unreachable!(),
                        }
                    }
                    MaybeValue::total((val, ops).join(" "))
                })
            }
            Rvalue::Aggregate(AggregateKind::Closure(def_id, _), ref ops) => {
                // start small with immutable closures: compile to Lean closure using
                // recursive FnTranspiler
                let upvars = ops.iter().map(lvalue_of_operand).collect_vec();
                if upvars.iter().any(|lv| krate::try_unwrap_mut_ref(self.lvalue_ty(lv)).map(|_| lv).is_some()) {
                    panic!("unimplemented: mutable capturing closure")
                }
                let trans = item::ItemTranspiler { sup: self.sup.sup, def_id: def_id };
                let mut trans = FnTranspiler::new(&trans);
                let body = trans.transpile_mir();
                self.prelude.append(&mut trans.prelude);
                MaybeValue::and_then_multi(0, upvars.iter().map(|lv| self.get_lvalue(lv)), |upvars| {
                    MaybeValue::total(format!(
                        "(λ {}, {}) {}",
                        trans.param_names().join(" "),
                        body,
                        mk_tuple(upvars.into_iter())))
                })
            }
            Rvalue::Len(ref lv) => self.get_lvalue(lv).and_then(0, |lv| {
                MaybeValue::total(format!("list.length {}", lv))
            }),
            Rvalue::Repeat(ref op, ref times) => self.get_operand(op).and_then(0, |op| {
                use rustc_const_math::ConstUsize::*;
                let times = match times.value {
                    Us16(t) => t as u64,
                    Us32(t) => t as u64,
                    Us64(t) => t,
                };
                // multiplying `op` is okay because it's known to implement `Copy`
                MaybeValue::total(format!("list.replicate {} {}", times, op))
            }),
            _ => panic!("unimplemented: rvalue {:?}", rv),
        }
    }

    /// Makes path of lenses and return eventual target
    fn mk_lenses(&self, lv: &'a Lvalue<'tcx>, lenses: &mut Vec<String>) -> &'a Lvalue<'tcx> {
        if lv.as_local().is_some() {
            return lv
        }

        match *lv {
            Lvalue::Projection(box Projection { ref base, ref elem }) => {
                match *elem {
                    ProjectionElem::Deref =>
                        if self.deref_mut(base).is_some() {
                            return base
                        },
                    ProjectionElem::Field(field, _) => {
                        let ty = unwrap_refs(self.lvalue_ty(base));
                        match ty.sty {
                            ty::TypeVariants::TyAdt(ref adt_def, _) => {
                                let field_name = adt_def.struct_variant().fields[field.index()].name;
                                lenses.push(format!("lens.mk (return ∘ {ty}.{field}) (λ (o : {ty}) i, return {setter})",
                                                    ty=self.name_def_id(adt_def.did), field=field_name,
                                                    setter=self.update_struct(adt_def, field, "o", "i")))
                            },
                            ref ty => panic!("unimplemented: lens on field of {:?}", ty),
                        }
                    }
                    ProjectionElem::Index(ref index) =>
                        lenses.push(format!("lens.index _ {}", self.get_operand(index).to_total())),
                    _ => panic!("unimplemented: lens on lvalue {:?}", lv),
                }
                self.mk_lenses(base, lenses)
            }
            _ => panic!("unimplemented: lens on lvalue {:?}", lv),
        }
    }

    /// Set dest to the combined lens on `&mut source` in val
    fn set_mut_ref(&mut self, dest: &Lvalue<'tcx>, mut lenses: Vec<String>, source: &Lvalue<'tcx>) -> String {
        let dest_local = dest.as_local().unwrap_or_else(|| {
            panic!("unimplemented: storing &mut in {:?}", dest)
        });
        let source = match self.deref_mut(source) {
            Some(ult_source) => {
                // reborrow ~> combine lenses
                lenses.push(self.get_lvalue(source).to_total());
                ult_source.clone()
            }
            _ => source.clone()
        };
        if *dest == Lvalue::Local(RETURN_POINTER) &&
            krate::try_unwrap_mut_ref(self.mir.return_ty).is_some() &&
            source != Lvalue::Local(Local::new(1)) {
            panic!("unimplemented: returning mutable reference to argument other than the first")
        }
        self.refs.insert(dest_local, source);
        let val = if lenses.is_empty() {
            format!("@lens.id {}", self.transpile_ty(krate::try_unwrap_mut_ref(self.lvalue_ty(dest)).unwrap()))
        }
        else { format!("({})", lenses.into_iter().join(" ∘ₗ ")) };
        self.set_lvalue(dest, &val)
    }

    fn transpile_statement(&mut self, kind: &StatementKind<'tcx>) -> String {
        match *kind {
            StatementKind::Assign(ref lv, ref rv) => {
                match *rv {
                    Rvalue::Ref(_, BorrowKind::Mut, ref source) => {
                        let mut lenses = vec![];
                        let source = self.mk_lenses(source, &mut lenses);
                        self.set_mut_ref(lv, lenses, source)
                    }
                    // move &mut
                    Rvalue::Use(Operand::Consume(Lvalue::Local(source)))
                        if krate::try_unwrap_mut_ref(self.mir.local_decls[source].ty).is_some() =>
                        self.set_mut_ref(lv, vec![], &Lvalue::Local(source)),
                    _ => self.get_rvalue(rv).map(0, |rv| self.set_lvalue(lv, &rv)),
                }
            }
            StatementKind::SetDiscriminant { .. } =>
                panic!("unimplemented: statement kind {:?}", kind),
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop =>
                "".to_string(),
        }
    }

    fn transpile_basic_block_rec(&mut self, bb: BasicBlock, comp: &Component) -> String {
        if comp.header == Some(bb) {
            // pass state to next iteration
            format!("return (sum.inl {})\n", comp.state_val)
        } else if !comp.blocks.contains(&bb) {
            // leaving a loop
            format!("do tmp__ ← {};\nreturn (sum.inr tmp__)", self.transpile_basic_block(bb, &comp.outer.unwrap()))
        } else {
            self.transpile_basic_block(bb, comp)
        }
    }

    /// return value + mutable input references
    fn call_return_dests<'b>(&self, call: &'b TerminatorKind<'tcx>) -> Vec<&'b Lvalue<'tcx>> {
        match call {
            &TerminatorKind::Call { ref args, destination: Some((ref lv, _)), .. } => {
                let muts = args.iter().filter_map(|op| match *op {
                    Operand::Consume(ref lv) => krate::try_unwrap_mut_ref(self.lvalue_ty(lv)).map(|_| lv),
                    Operand::Constant(_) => None,
                });
                iter::once(lv).chain(muts).collect()
            }
            _ => unreachable!(),
        }
    }

    /// Locates the applicable definition of a method, given its name.
    // from trans::meth
    fn get_impl_method<'t>(
        tcx: ty::TyCtxt<'a, 't, 't>,
        substs: &Substs<'t>,
        impl_def_id: DefId,
        impl_substs: &Substs<'t>,
        name: ast::Name,
    ) -> (DefId, Substs<'t>) {
        let trait_def_id = tcx.trait_id_of_impl(impl_def_id).unwrap();
        let trait_def = tcx.lookup_trait_def(trait_def_id);

        match trait_def.ancestors(impl_def_id).fn_defs(tcx, name).next() {
            Some(node_item) => {
                let substs = tcx.infer_ctxt(None, None, traits::Reveal::All).enter(|infcx| {
                    let substs = substs.rebase_onto(tcx, trait_def_id, impl_substs);
                    let substs = traits::translate_substs(&infcx, impl_def_id,
                                                        substs, node_item.node);
                    tcx.lift(&substs).unwrap_or_else(|| {
                        bug!("trans::meth::get_impl_method: translate_substs \
                            returned {:?} which contains inference types/regions",
                            substs);
                    })
                });
                (node_item.item.def_id, substs.clone())
            }
            None => {
                bug!("method {:?} not found in {:?}", name, impl_def_id)
            }
        }
    }

    // All type generics including from parent items
    fn full_generics(&self, def_id: DefId) -> Vec<&'tcx ty::TypeParameterDef<'tcx>> {
        ::itertools::Unfold::new(Some(def_id), |opt_def_id| {
            opt_def_id.map(|def_id| {
                let g = self.tcx.lookup_generics(def_id);
                *opt_def_id = g.parent;
                g.types.iter()
            })
        }).flat_map(|t| t).collect()
    }

    /// Desparately tries to figure out a call target, including implicit (type) parameters
    fn get_call_target(&self, func: &Operand<'tcx>) -> String {
        match *func {
            Operand::Constant(Constant { literal: Literal::Item { def_id, substs, .. }, .. }) => {
                let substs = substs.clone();
                self.tcx.infer_ctxt(None, Some(ty::ParameterEnvironment::for_item(self.tcx, self.node_id())), ::rustc::traits::Reveal::All).enter(|infcx| -> TransResult {
                    let (def_id, substs): (_, ty::subst::Substs<'tcx>) = match self.tcx.trait_of_item(def_id) {
                        Some(trait_def_id) => {
                            // from trans::meth::trans_method_callee
                            let trait_ref = ty::TraitRef::from_method(self.tcx, trait_def_id, &substs);

                            match self.infer_trait_impl(trait_ref, &infcx)? {
                                item::TraitImplLookup::Static { impl_def_id, substs: impl_substs, .. }  => {
                                    let method = self.tcx.impl_or_trait_item(def_id).as_opt_method().unwrap();
                                    FnTranspiler::get_impl_method(self.tcx, &substs, impl_def_id, &impl_substs, method.name)
                                }
                                item::TraitImplLookup::Dynamic { .. } =>
                                    (def_id, substs)
                            }
                        }
                        _ => (def_id, substs)
                    };

                    // TODO: should probably substitute and make explicit
                    let ty_params = self.full_generics(def_id).iter().map(|_| "_".to_string()).collect_vec();
                    // analogous to `ItemTranspiler::transpile_trait_params` - see there for examples
                    let assoc_ty_substs = self.get_assoc_ty_substs(def_id);
                    let trait_params = try_iter!(self.trait_predicates_without_markers(def_id).map(|trait_pred| -> TransResult<_> {
                        let free_assoc_tys = self.transpile_trait_ref_assoc_tys(trait_pred.trait_ref, &assoc_ty_substs).1;
                        let free_assoc_tys = free_assoc_tys.into_iter().map(|_| "_".to_string());
                        let trait_ref: ty::TraitRef<'tcx> = trait_pred.trait_ref;
                        let trait_param = self.infer_trait_impl(trait_ref.subst(self.tcx, &substs), &infcx)?.to_string(self);
                        Ok(free_assoc_tys.chain(iter::once(trait_param)))
                    })).flat_map(|x| x);
                    Ok((format!("@{}", self.name_def_id(def_id)), ty_params.into_iter().chain(trait_params)).join(" "))
                }).unwrap()
            }
            Operand::Constant(_) => unreachable!(),
            Operand::Consume(ref lv) => self.get_lvalue(lv).to_total(),
        }
    }

    fn return_expr(&self) -> String {
        let mut_args = self.mir.args_iter().filter_map(|arg| {
            krate::try_unwrap_mut_ref(self.mir.local_decls[arg].ty).map(|_| self.local_name(arg))
        });
        format!("return ({})\n", ("ret", mut_args).join(", "))
    }

    fn transpile_basic_block(&mut self, bb: BasicBlock, comp: &Component) -> String {
        macro_rules! rec { ($bb:expr) => { self.transpile_basic_block_rec($bb, comp) } }
        use rustc::mir::repr::TerminatorKind::*;

        if let Some(l) = comp.loops.iter().find(|l| l.contains(&bb)) {
            // entering a loop
            let mut l_comp = Component::new(self, bb, l, Some(&comp));
            let (defs, _) = Component::defs_uses(comp.blocks.iter().filter(|bb| !l_comp.blocks.contains(bb)), self);
            let (l_defs, l_uses) = Component::defs_uses(l_comp.blocks.iter(), self);
            // vars that are used by l, but not (re)defined ~> parameters
            let nonlocal_uses = self.mir.local_decls.indices().map(|v| self.local_name(v))
                .filter(|v| l_uses.contains(v) && !l_defs.contains(v)).collect_vec();
            // vars that are redefined by l ~> loop state
            let (state_var_tys, state_vars): (Vec<_>, Vec<_>) = self.mir.local_decls.indices().filter_map(|v| {
                let name = self.local_name(v);
                if defs.contains(&name) && l_defs.contains(&name) {
                    let ty = self.transpile_ty(self.lvalue_ty(&Lvalue::Local(v)));
                    Some((ty, name))
                } else { None }
            }).unzip();
            let state_ty = state_var_tys.join(" × ");
            l_comp.state_val = format!("({})", state_vars.iter().join(", "));
            let name = format!("{}.loop_{}", self.name(), bb.index());
            let app = (name, nonlocal_uses).join(" ");
            let ret_ty = format!("sem (sum ({}) {})", state_ty, self.ret_ty());
            let body = self.transpile_basic_block(bb, &l_comp);
            self.prelude.push(format!("definition {} (state__ : {}) : {} :=\n{}", app,
                                      state_ty, ret_ty, detuplize("state__", &state_vars, &body)));
            return format!("loop ({}) {}", app, l_comp.state_val);
        }

        let data = &self.mir[bb];
        let stmts = data.statements.iter().map(|s| self.transpile_statement(&s.kind)).collect_vec();
        let terminator = match data.terminator {
            Some(ref terminator) => Some(match terminator.kind {
                Goto { target } =>
                    rec!(target),
                If { ref cond, targets: (bb_if, bb_else) } =>
                    // TODO: this duplicates all code after the if
                    self.get_operand(cond).map(0, |cond| format!(
                        "if {} = bool.tt then\n{}else\n{}", cond,
                        rec!(bb_if),
                        rec!(bb_else))),
                Return => self.return_expr(),
                Call { ref func, ref args, destination: Some((_, target)), ..  } => {
                    MaybeValue::map_multi(0, args.iter().map(|op| {
                        if let Operand::Consume(ref lv) = *op {
                            if krate::try_unwrap_mut_ref(self.lvalue_ty(lv)).is_some() {
                                // dereference &mut arguments
                                return self.get_lvalue(&lv.clone().deref())
                            }
                        }
                        self.get_operand(op)
                    }).collect_vec().into_iter(), |sargs| {
                        let call_target = self.get_call_target(func);
                        let call = (call_target, sargs).join(" ");

                        let (direct_dests, indirect_dests): (Vec<_>, Vec<_>) = self.call_return_dests(&terminator.kind).into_iter().enumerate().map(|(i, lv)| {
                            let tmp = format!("«{}$»", self.local_name(lv.as_local().unwrap()));
                            if krate::try_unwrap_mut_ref(self.lvalue_ty(lv)).is_some() {
                                if i == 0 {
                                    let source = lvalue_of_operand(&args[0]);
                                    // reborrow source into lv, using lens tmp
                                    (tmp.clone(), Some(self.set_mut_ref(lv, vec![tmp], source.deref())))
                                } else {
                                    // write back through &mut
                                    (tmp.clone(), Some(self.set_lvalue(&lv.clone().deref(), &tmp)))
                                }
                            } else {
                                if let Some(name) = self.lvalue_name(lv) {
                                    (name, None)
                                } else {
                                    (tmp.clone(), Some(self.set_lvalue(lv, &tmp)))
                                }
                            }
                        }).unzip();
                        let indirect_dests = indirect_dests.into_iter().filter_map(|x| x).rev().join("");
                        let rec = rec!(target);
                        format!("dostep «$tmp» ← {};\n{}", call,
                                detuplize("«$tmp»", &direct_dests[..], &(indirect_dests + &rec)))
                    })
                }
                // diverging call
                Call { destination: None, .. } | Unreachable =>
                    "mzero\n".to_string(),
                Switch { ref discr, ref adt_def, ref targets } => {
                    let value = self.local_name(discr.as_local().unwrap());
                    let mut arms = adt_def.variants.iter().zip(targets).map(|(var, &target)| {
                        // binding names used by `get_lvalue`
                        let vars = (0..var.fields.len()).into_iter().map(|i| format!("{}_{}", value, i));
                        format!("| {} :=\n{}", (self.name_def_id(var.did), vars).join(" "), rec!(target))
                    });
                    format!("match {} with\n{}end\n", value, arms.join(" "))
                },
                SwitchInt { ref discr, switch_ty: _, ref values, ref targets } => {
                    self.get_lvalue(discr).map(0, |discr| {
                        let arms = values.iter().zip(targets).map(|(val, &target)| {
                            let val = match *val {
                                ConstVal::Integral(i) => match i.int_type().unwrap() {
                                    ::syntax::attr::IntType::SignedInt(_) =>
                                        format!("{}", i.to_u64_unchecked() as i64),
                                    ::syntax::attr::IntType::UnsignedInt(_) =>
                                        format!("{}", i.to_u64_unchecked()),
                                },
                                _ => unreachable!(),
                            };
                            format!("| {} :=\n{}", val, rec!(target))
                        }).collect_vec();
                        let fallback = format!("| _ :=\n{}", rec!(*targets.last().unwrap()));
                        format!("match {} with\n{}\nend\n", discr,
                                arms.into_iter().chain(iter::once(fallback)).join(""))
                    })
                },
                // out-of-bounds/overflow checks - already part of core/pre.lean
                Assert { target, /*ref cond, expected,*/ .. } => rec!(target), /*self.get_operand(cond).map(0, |cond| {
                    format!("cond {} mzero ({})", if expected {cond} else {
                        format!("(bnot {})", cond)
                    }, rec!(target))
                }),*/
                Drop { target, .. } => rec!(target),
                DropAndReplace { ref location, ref value, target, .. } => {
                    self.transpile_statement(&StatementKind::Assign(location.clone(), Rvalue::Use(value.clone()))) +
                    &rec!(target)
                }
                Resume => String::new(),
            }),
            None => None,
        };
        stmts.into_iter().chain(terminator).join("")
    }

    pub fn transpile_mir(&mut self) -> String {
        let blocks = self.mir.basic_blocks().indices().collect_vec();
        let mut comp = Component::new(&self, START_BLOCK, &blocks[..], None);
        self.transpile_basic_block(START_BLOCK, &mut comp)
    }

    fn ret_ty(&self) -> String {
        match self.normalize_ty(self.tcx.lookup_item_type(self.def_id).ty).sty {
            ty::TypeVariants::TyFnDef(_, _, ref data) | ty::TypeVariants::TyFnPtr(ref data) =>
                self.sup.ret_ty(data),
            _ => unreachable!(),
        }
    }

    pub fn transpile_fn(mut self, name: String) -> String {
        // FIXME... or not
        if name.starts_with("tuple._A__B__C__D") {
            return "".to_string()
        }

        let params = self.mir.args_iter().map(|arg| {
            format!("({} : {})", self.local_name(arg), self.transpile_ty(krate::unwrap_mut_ref(&self.mir.local_decls[arg].ty)))
        }).collect_vec();

        let promoted = self.mir.promoted.iter_enumerated().map(|(idx, mir)| {
            let body = FnTranspiler { mir: mir, ..self.clone() }.transpile_mir();
            format!("do promoted_{} ←\n{};", idx.index(), body)
        }).collect_vec();

        let body = (promoted, self.transpile_mir()).join("\n");

        let ty_params = self.full_generics(self.def_id).iter().map(|p| format!("{{{} : Type₁}}", p.name)).collect_vec();
        let trait_params = self.transpile_trait_params(self.def_id, None);

        let is_rec = self.is_recursive(self.def_id);
        let body = if is_rec {
            // FIXME: not actually implemented yet
            format!("fix_opt (λ{}, {})", name, body)
        } else { body };
        if self.prelude.is_empty() {
            let def = format!("definition {} : sem {} :=\n{}",
                              (name, ty_params.into_iter().chain(trait_params).chain(params)).join(" "),
                              self.ret_ty(),
                              body);
            self.prelude.into_iter().chain(iter::once(def)).join("\n\n")
        } else {
            format!("section
{}

{}

definition {} : sem {} :=\n{}
end",
                    vec![ty_params, trait_params, params].into_iter().map(|p| {
                        format!("parameters {}", p.into_iter().join(" "))
                    }).join("\n"),
                    self.prelude.iter().join("\n\n"),
                    name, self.ret_ty(), body)
        }
    }
}
