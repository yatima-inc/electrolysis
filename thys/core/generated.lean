import core.pre
import data.nat data.list

noncomputable theory

open classical
open int
open nat
open prod.ops
open sum
open core


namespace core
section
  variables {m : Type₁ → Type} [monad_sem m]

inductive result.Result (T : Type₁) (E : Type₁) :=
| Ok {} : T → result.Result T E
| Err {} : E → result.Result T E

inductive cmp.Ordering :=
| Less {} : cmp.Ordering
| Equal {} : cmp.Ordering
| Greater {} : cmp.Ordering

structure ops.RangeTo (Idx : Type₁) := mk {} ::
(end_ : Idx)

structure ops.Range (Idx : Type₁) := mk {} ::
(start : Idx)
(end_ : Idx)

/-
/// Implements slicing with syntax `&self[begin .. end]`.
///
/// Returns a slice of self for the index range [`begin`..`end`).
///
/// This operation is `O(1)`.
///
/// # Panics
///
/// Requires that `begin <= end` and `end <= self.len()`,
/// otherwise slicing will panic.
-/
definition slice._T_.ops_Index_ops_Range_usize__.index {T : Type₁} (self : slice T) (index : ops.Range usize) : m (slice T) :=
if ops.Range.start index ≤ ops.Range.end_ index ∧ ops.Range.end_ index ≤ list.length self
then return (list.firstn (ops.Range.end_ index - ops.Range.start index) (list.dropn (ops.Range.start index) self))
else mzero

definition slice._T_.ops_Index_ops_RangeTo_usize__.index {T : Type₁} (self : (slice T)) (index : (ops.RangeTo usize)) : m (slice T) :=
let self ← self;
let index ← index;
let t1 ← self;
let t4 ← (0 : nat);
let t6 ← (ops.RangeTo.end_ index);
let t5 ← t6;
let t3 ← ops.Range.mk t4 t5;
do tmp__ ← @slice._T_.ops_Index_ops_Range_usize__.index _ _ _ t1 t3;
let t0 ← tmp__;
let ret ← t0;
return (ret)


structure ops.RangeFrom (Idx : Type₁) := mk {} ::
(start : Idx)

definition slice._T_.ops_Index_ops_RangeFrom_usize__.index {T : Type₁} (self : (slice T)) (index : (ops.RangeFrom usize)) : m (slice T) :=
let self ← self;
let index ← index;
let t1 ← self;
let t5 ← (ops.RangeFrom.start index);
let t4 ← t5;
let t7 ← self;
do tmp__ ← @slice._T_.slice_SliceExt.len _ _ _ t7;
let t6 ← tmp__;
let t3 ← ops.Range.mk t4 t6;
do tmp__ ← @slice._T_.ops_Index_ops_Range_usize__.index _ _ _ t1 t3;
let t0 ← tmp__;
let ret ← t0;
return (ret)


definition slice._T_.slice_SliceExt.split_at {T : Type₁} (self : (slice T)) (mid : usize) : m ((slice T) × (slice T)) :=
let self ← self;
let mid ← mid;
let t3 ← self;
let t7 ← mid;
let t6 ← t7;
let t5 ← ops.RangeTo.mk t6;
do tmp__ ← @slice._T_.ops_Index_ops_RangeTo_usize__.index _ _ _ t3 t5;
let t2 ← tmp__;
let t1 ← t2;
let t0 ← t1;
let t11 ← self;
let t14 ← mid;
let t13 ← t14;
let t12 ← ops.RangeFrom.mk t13;
do tmp__ ← @slice._T_.ops_Index_ops_RangeFrom_usize__.index _ _ _ t11 t12;
let t10 ← tmp__;
let t9 ← t10;
let t8 ← t9;
let ret ← (t0, t8);
return (ret)


structure slice.SliceExt [class] (Self : Type₁) (Item : Type₁) :=
(len : Self → m (usize))

definition slice._T_.slice_SliceExt [instance] (T : Type₁) := ⦃
  slice.SliceExt (slice T) T,
  len := slice._T_.slice_SliceExt.len
⦄

definition slice.SliceExt.is_empty {Self : Type₁} (Item : Type₁) [slice_SliceExt_Self : slice.SliceExt Self Item] (self : Self) : m Prop :=
let self ← self;
let t1 ← self;
do tmp__ ← @slice.SliceExt.len _ _ _ _ slice_SliceExt_Self t1;
let t0 ← tmp__;
let ret ← t0 = (0 : nat);
return (ret)


section
parameters {T : Type₁} {F : Type₁}
parameters [ops_FnMut__T__F : ops.FnMut (T) F (cmp.Ordering )]
parameters (self : (slice T)) (f : F)

definition slice._T_.slice_SliceExt.binary_search_by.loop_4 state__ :=
match state__ with (f, base, s) :=
let t3 ← s;
let t6 ← s;
do tmp__ ← @slice._T_.slice_SliceExt.len _ _ _ t6;
let t5 ← tmp__;
do tmp__ ← checked.shr t5 (1 : int);
let t4 ← tmp__;
do tmp__ ← @slice._T_.slice_SliceExt.split_at _ _ _ t3 t4;
let t2 ← tmp__;
let head ← t2.1;
let tail ← t2.2;
let t9 ← tail;
do tmp__ ← @slice.SliceExt.is_empty _ _ _ _ (slice._T_.slice_SliceExt T) t9;
let t8 ← tmp__;
if t8 then
do tmp__ ← let t10 ← base;
let ret ← result.Result.Err t10;
return (ret)
;
return (inr tmp__) else
let t16 ← list.length tail;
let t17 ← (0 : nat) < t16;
if t17 then
do tmp__ ← slice._T_.slice_SliceExt.get_unchecked tail (0 : nat);
let t15 ← tmp__;
let t14 ← t15;
let t13 ← (t14);
do tmp__ ← @ops.FnMut.call_mut _ _ _ _ _ ops_FnMut__T__F f t13;
match tmp__ with (t11, f) :=
match t11 with
| cmp.Ordering.Less :=
let t23 ← head;
do tmp__ ← @slice._T_.slice_SliceExt.len _ _ _ t23;
let t22 ← tmp__;
let t21 ← t22 + (1 : nat);
let base ← base + t21;
let t28 ← tail;
let t30 ← (1 : nat);
let t29 ← ops.RangeFrom.mk t30;
do tmp__ ← @slice._T_.ops_Index_ops_RangeFrom_usize__.index _ _ _ t28 t29;
let t27 ← tmp__;
let t26 ← t27;
let t25 ← t26;
let s ← t25;
return (inl (f, base, s))
 | cmp.Ordering.Equal :=
do tmp__ ← let t33 ← base;
let t35 ← head;
do tmp__ ← @slice._T_.slice_SliceExt.len _ _ _ t35;
let t34 ← tmp__;
let t32 ← t33 + t34;
let ret ← result.Result.Ok t32;
return (ret)
;
return (inr tmp__) | cmp.Ordering.Greater :=
let t31 ← head;
let s ← t31;
return (inl (f, base, s))
end
end
 else
do tmp__ ← let t18 ← ("rust/src/libcore/slice.rs", (307 : nat));
let t19 ← t18;
mzero
;
return (inr tmp__)end


definition slice._T_.slice_SliceExt.binary_search_by : m (result.Result usize usize) :=
let self ← self;
let f ← f;
let base ← (0 : nat);
let t1 ← self;
let s ← t1;
loop' (slice._T_.slice_SliceExt.binary_search_by.loop_4) (f, base, s)
end

structure cmp.PartialEq [class] (Rhs : Type₁) (Self : Type₁)  :=
(eq : Self → Rhs → m (Prop))

structure cmp.Eq [class] (Self : Type₁) extends cmp.PartialEq Self Self 

inductive option.Option (T : Type₁) :=
| None {} : option.Option T
| Some {} : T → option.Option T

structure cmp.PartialOrd [class] (Rhs : Type₁) (Self : Type₁) extends cmp.PartialEq Rhs Self :=
(partial_cmp : Self → Rhs → m ((option.Option (cmp.Ordering ))))

structure cmp.Ord [class] (Self : Type₁) extends cmp.Eq Self, cmp.PartialOrd Self Self :=
(cmp : Self → Self → m ((cmp.Ordering )))

definition slice._T_.slice_SliceExt.binary_search {T : Type₁} [cmp_Ord_T : cmp.Ord T] (self : (slice T)) (x : T) : m (result.Result usize usize) :=
let self ← self;
let x ← x;
let t0 ← self;
let t3 ← x;
let t2 ← (λp, let p ← p;
let t0 ← p;
let t2 ← t3;
do tmp__ ← @cmp.Ord.cmp _ _ _ cmp_Ord_T t0 t2;
let ret ← tmp__;
return ret);
do tmp__ ← @slice._T_.slice_SliceExt.binary_search_by _ _ _ _ fn t0 t2;
let ret ← tmp__;
return (ret)


end
end core
