import core.pre
import data.nat data.list

noncomputable theory

open classical
open int
open nat
open option
open prod.ops
open sum

namespace core
open core

inductive cmp.Ordering :=
| Less {} : cmp.Ordering
| Equal {} : cmp.Ordering
| Greater {} : cmp.Ordering

structure ops.RangeTo (Idx : Type) := mk {} ::
(end_ : Idx)

structure ops.Range (Idx : Type) := mk {} ::
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
definition slice._T_.ops_Index_ops_Range_usize__.index {T : Type} (self : slice T) (index : ops.Range usize) :=
if ops.Range.start index ≤ ops.Range.end_ index ∧ ops.Range.end_ index ≤ list.length self
then some (list.firstn (ops.Range.end_ index - ops.Range.start index) (list.dropn (ops.Range.start index) self))
else none

definition slice._T_.ops_Index_ops_RangeTo_usize__.index {T : Type} (self : (slice T)) (index : (ops.RangeTo usize)) :=
let self ← self;
let index ← index;
let t1 ← self;
let t3 ← (0 : nat);
let t5 ← (ops.RangeTo.end_ index);
let t4 ← t5;
let t2 ← ops.Range.mk t3 t4;
do tmp__ ← @slice._T_.ops_Index_ops_Range_usize__.index _ t1 t2;
let t0 ← tmp__;
let ret ← t0;
some (ret)


structure ops.RangeFrom (Idx : Type) := mk {} ::
(start : Idx)

definition slice._T_.ops_Index_ops_RangeFrom_usize__.index {T : Type} (self : (slice T)) (index : (ops.RangeFrom usize)) :=
let self ← self;
let index ← index;
let t1 ← self;
let t4 ← (ops.RangeFrom.start index);
let t3 ← t4;
let t6 ← self;
do tmp__ ← @slice._T_.slice_SliceExt.len _ t6;
let t5 ← tmp__;
let t2 ← ops.Range.mk t3 t5;
do tmp__ ← @slice._T_.ops_Index_ops_Range_usize__.index _ t1 t2;
let t0 ← tmp__;
let ret ← t0;
some (ret)


definition slice._T_.slice_SliceExt.split_at {T : Type} (self : (slice T)) (mid : usize) :=
let self ← self;
let mid ← mid;
let t3 ← self;
let t6 ← mid;
let t5 ← t6;
let t4 ← ops.RangeTo.mk t5;
do tmp__ ← @slice._T_.ops_Index_ops_RangeTo_usize__.index _ t3 t4;
let t2 ← tmp__;
let t1 ← t2;
let t0 ← t1;
let t10 ← self;
let t13 ← mid;
let t12 ← t13;
let t11 ← ops.RangeFrom.mk t12;
do tmp__ ← @slice._T_.ops_Index_ops_RangeFrom_usize__.index _ t10 t11;
let t9 ← tmp__;
let t8 ← t9;
let t7 ← t8;
let ret ← (t0, t7);
some (ret)


structure slice.SliceExt [class] (Self : Type) (Item : Type) :=
(len : Self → option (usize))

definition slice._T_.slice_SliceExt [instance] (T : Type) := ⦃
  slice.SliceExt (slice T) T,
  len := slice._T_.slice_SliceExt.len
⦄

definition slice.SliceExt.is_empty {Self : Type} (Item : Type) [slice_SliceExt_Self : slice.SliceExt Self Item] (self : Self) :=
let self ← self;
let t1 ← self;
do tmp__ ← @slice.SliceExt.len _ _ slice_SliceExt_Self t1;
let t0 ← tmp__;
let ret ← t0 = (0 : nat);
some (ret)


inductive result.Result (T : Type) (E : Type) :=
| Ok {} : T → result.Result T E
| Err {} : E → result.Result T E

section
parameters {T : Type} {F : Type}
parameters [ops_FnMut__T__F : ops.FnMut (T) F (cmp.Ordering )]
parameters (self : (slice T)) (f : F)

definition slice._T_.slice_SliceExt.binary_search_by.loop_4 state__ :=
match state__ with (f, base, s) :=
let t3 ← s;
let t6 ← s;
do tmp__ ← @slice._T_.slice_SliceExt.len _ t6;
let t5 ← tmp__;
do tmp__ ← option.map (λx, (x, true)) (checked.shr t5 (1 : int));
let t7 ← tmp__;
let t4 ← t7.1;
do tmp__ ← @slice._T_.slice_SliceExt.split_at _ t3 t4;
let t2 ← tmp__;
let head ← t2.1;
let tail ← t2.2;
let t10 ← tail;
do tmp__ ← @slice.SliceExt.is_empty _ _ (slice._T_.slice_SliceExt T) t10;
let t9 ← tmp__;
if t9 then
do tmp__ ← let t11 ← base;
let ret ← result.Result.Err t11;
some (ret)
;
some (inr tmp__) else
let t17 ← list.length tail;
let t18 ← (0 : nat) < t17;
do tmp__ ← slice._T_.slice_SliceExt.get_unchecked tail (0 : nat);
let t16 ← tmp__;
let t15 ← t16;
let t14 ← (t15);
do tmp__ ← @ops.FnMut.call_mut _ _ _ ops_FnMut__T__F f t14;
match tmp__ with (t12, f) :=
match t12 with
| cmp.Ordering.Less :=
let t21 ← head;
do tmp__ ← @slice._T_.slice_SliceExt.len _ t21;
let t20 ← tmp__;
let t22 ← (t20 + (1 : nat), true);
let t19 ← t22.1;
let t23 ← (base + t19, true);
let base ← t23.1;
let t26 ← tail;
let t28 ← (1 : nat);
let t27 ← ops.RangeFrom.mk t28;
do tmp__ ← @slice._T_.ops_Index_ops_RangeFrom_usize__.index _ t26 t27;
let t25 ← tmp__;
let t24 ← t25;
let s ← t24;
some (inl (f, base, s))
 | cmp.Ordering.Equal :=
do tmp__ ← let t30 ← base;
let t32 ← head;
do tmp__ ← @slice._T_.slice_SliceExt.len _ t32;
let t31 ← tmp__;
let t33 ← (t30 + t31, true);
let t29 ← t33.1;
let ret ← result.Result.Ok t29;
some (ret)
;
some (inr tmp__) | cmp.Ordering.Greater :=
let s ← head;
some (inl (f, base, s))
end
end
end


definition slice._T_.slice_SliceExt.binary_search_by :=
let self ← self;
let f ← f;
let base ← (0 : nat);
let t1 ← self;
let s ← t1;
loop' (slice._T_.slice_SliceExt.binary_search_by.loop_4) (f, base, s)
end

structure cmp.PartialEq [class] (Rhs : Type) (Self : Type)  :=
(eq : Self → Rhs → option (Prop))

structure cmp.Eq [class] (Self : Type) extends cmp.PartialEq Self Self 

inductive option.Option (T : Type) :=
| None {} : option.Option T
| Some {} : T → option.Option T

structure cmp.PartialOrd [class] (Rhs : Type) (Self : Type) extends cmp.PartialEq Rhs Self :=
(partial_cmp : Self → Rhs → option ((option.Option (cmp.Ordering ))))

structure cmp.Ord [class] (Self : Type) extends cmp.Eq Self, cmp.PartialOrd Self Self :=
(cmp : Self → Self → option ((cmp.Ordering )))

definition slice._T_.slice_SliceExt.binary_search {T : Type} [cmp_Ord_T : cmp.Ord T] (self : (slice T)) (x : T) :=
let self ← self;
let x ← x;
let t0 ← self;
let t2 ← x;
let t1 ← (λp, let p ← p;
let t0 ← p;
let t1 ← t2;
do tmp__ ← @cmp.Ord.cmp _ cmp_Ord_T t0 t1;
let ret ← tmp__;
some ret);
do tmp__ ← @slice._T_.slice_SliceExt.binary_search_by _ _ fn t0 t1;
let ret ← tmp__;
some (ret)


end core