import core.pre

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit
open core

namespace core

inductive cmp.Ordering :=
| Less {} : cmp.Ordering
| Equal {} : cmp.Ordering
| Greater {} : cmp.Ordering

structure ops.RangeFrom (Idx : Type₁) := mk {} ::
(start : Idx)

inductive result.Result (T : Type₁) (E : Type₁) :=
| Ok {} : T → result.Result T E
| Err {} : E → result.Result T E

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
definition slice._T_.as.ops_Index_ops_Range_usize__.index {T : Type₁} (self : slice T) (index : ops.Range usize) : sem (slice T) :=
if ops.Range.start index ≤ ops.Range.end_ index ∧ ops.Range.end_ index ≤ list.length self
then return (list.firstn (ops.Range.end_ index - ops.Range.start index) (list.dropn (ops.Range.start index) self))
else mzero

definition slice._T_.as.ops_Index_ops_RangeTo_usize__.index {T : Type₁} (self : (slice T)) (index : (ops.RangeTo usize)) : sem ((slice T)) :=
let' t1 ← self;
let' t3 ← (0 : nat);
let' t5 ← (ops.RangeTo.end_ index);
let' t4 ← t5;
let' t2 ← ops.Range.mk t3 t4;
dostep tmp__ ← @slice._T_.as.ops_Index_ops_Range_usize__.index _ t1 t2;
let' t0 ← tmp__;
let' ret ← t0;
return (ret)


definition slice._T_.as.ops_Index_ops_RangeFrom_usize__.index {T : Type₁} (self : (slice T)) (index : (ops.RangeFrom usize)) : sem ((slice T)) :=
let' t1 ← self;
let' t4 ← (ops.RangeFrom.start index);
let' t3 ← t4;
let' t6 ← self;
dostep tmp__ ← @slice._T_.as.slice_SliceExt.len _ t6;
let' t5 ← tmp__;
let' t2 ← ops.Range.mk t3 t5;
dostep tmp__ ← @slice._T_.as.ops_Index_ops_Range_usize__.index _ t1 t2;
let' t0 ← tmp__;
let' ret ← t0;
return (ret)


definition slice._T_.as.slice_SliceExt.split_at {T : Type₁} (self : (slice T)) (mid : usize) : sem (((slice T) × (slice T))) :=
let' t3 ← self;
let' t6 ← mid;
let' t5 ← t6;
let' t4 ← ops.RangeTo.mk t5;
dostep tmp__ ← @slice._T_.as.ops_Index_ops_RangeTo_usize__.index _ t3 t4;
let' t2 ← tmp__;
let' t1 ← t2;
let' t0 ← t1;
let' t10 ← self;
let' t13 ← mid;
let' t12 ← t13;
let' t11 ← ops.RangeFrom.mk t12;
dostep tmp__ ← @slice._T_.as.ops_Index_ops_RangeFrom_usize__.index _ t10 t11;
let' t9 ← tmp__;
let' t8 ← t9;
let' t7 ← t8;
let' ret ← (t0, t7);
return (ret)


structure slice.SliceExt [class] (Self : Type₁) (Item : Type₁) :=
(len : Self → sem (usize))

definition slice._T_.as.slice_SliceExt [instance] (T : Type₁) := ⦃
  slice.SliceExt (slice T) T,
  len := slice._T_.as.slice_SliceExt.len
⦄

definition slice.SliceExt.is_empty {Self : Type₁} (Item : Type₁) [slice_SliceExt_Self : slice.SliceExt Self Item] (self : Self) : sem (Prop) :=
let' t1 ← self;
dostep tmp__ ← @slice.SliceExt.len _ _ slice_SliceExt_Self t1;
let' t0 ← tmp__;
let' ret ← t0 = (0 : nat);
return (ret)


section
parameters {T : Type₁} {F : Type₁}
parameters [ops_FnMut__T__F : ops.FnMut (T) F (cmp.Ordering)]
parameters (self : (slice T)) (f : F)

definition slice._T_.as.slice_SliceExt.binary_search_by.loop_4 (state__ : F × usize × (slice T)) : sem (sum (F × usize × (slice T)) ((result.Result usize usize))) :=
match state__ with (f, base, s) :=
let' t3 ← s;
let' t6 ← s;
dostep tmp__ ← @slice._T_.as.slice_SliceExt.len _ t6;
let' t5 ← tmp__;
do tmp__ ← sem.map (λx, (x, true)) (checked.shr t5 (1 : int));
let' t7 ← tmp__;
let' t4 ← t7.1;
dostep tmp__ ← @slice._T_.as.slice_SliceExt.split_at _ t3 t4;
let' t2 ← tmp__;
let' head ← t2.1;
let' tail ← t2.2;
let' t10 ← tail;
dostep tmp__ ← @slice.SliceExt.is_empty _ _ (slice._T_.as.slice_SliceExt T) t10;
let' t9 ← tmp__;
if t9 then
do tmp__ ← let' t11 ← base;
let' ret ← result.Result.Err t11;
return (ret)
;
return (sum.inr tmp__) else
let' t17 ← list.length tail;
let' t18 ← (0 : nat) < t17;
do tmp__ ← slice._T_.as.slice_SliceExt.get_unchecked tail (0 : nat);
let' t16 ← tmp__;
let' t15 ← t16;
let' t14 ← (t15);
dostep tmp__ ← @ops.FnMut.call_mut _ _ _ ops_FnMut__T__F f t14;
match tmp__ with (t12, f) :=
match t12 with
| cmp.Ordering.Less :=
let' t21 ← head;
dostep tmp__ ← @slice._T_.as.slice_SliceExt.len _ t21;
let' t20 ← tmp__;
let' t22 ← (t20 + (1 : nat), true);
let' t19 ← t22.1;
let' t23 ← (base + t19, true);
let' base ← t23.1;
let' t26 ← tail;
let' t28 ← (1 : nat);
let' t27 ← ops.RangeFrom.mk t28;
dostep tmp__ ← @slice._T_.as.ops_Index_ops_RangeFrom_usize__.index _ t26 t27;
let' t25 ← tmp__;
let' t24 ← t25;
let' s ← t24;
return (sum.inl (f, base, s))
 | cmp.Ordering.Equal :=
do tmp__ ← let' t30 ← base;
let' t32 ← head;
dostep tmp__ ← @slice._T_.as.slice_SliceExt.len _ t32;
let' t31 ← tmp__;
let' t33 ← (t30 + t31, true);
let' t29 ← t33.1;
let' ret ← result.Result.Ok t29;
return (ret)
;
return (sum.inr tmp__) | cmp.Ordering.Greater :=
let' s ← head;
return (sum.inl (f, base, s))
end
end
end


definition slice._T_.as.slice_SliceExt.binary_search_by : sem ((result.Result usize usize)) :=
let' base ← (0 : nat);
let' t1 ← self;
let' s ← t1;
loop (slice._T_.as.slice_SliceExt.binary_search_by.loop_4) (f, base, s)
end

structure cmp.PartialEq [class] (Rhs : Type₁) (Self : Type₁)  :=
(eq : Self → Rhs → sem (Prop))

structure cmp.Eq [class] (Self : Type₁) extends cmp.PartialEq Self Self 

inductive option.Option (T : Type₁) :=
| None {} : option.Option T
| Some {} : T → option.Option T

structure cmp.PartialOrd [class] (Rhs : Type₁) (Self : Type₁) extends cmp.PartialEq Rhs Self :=
(partial_cmp : Self → Rhs → sem ((option.Option (cmp.Ordering))))

structure cmp.Ord [class] (Self : Type₁) extends cmp.Eq Self, cmp.PartialOrd Self Self :=
(cmp : Self → Self → sem ((cmp.Ordering)))

definition slice._T_.as.slice_SliceExt.binary_search {T : Type₁} [cmp_Ord_T : cmp.Ord T] (self : (slice T)) (x : T) : sem ((result.Result usize usize)) :=
let' t0 ← self;
let' t2 ← x;
let' t1 ← (λp, let' t0 ← p;
let' t1 ← t2;
dostep tmp__ ← @cmp.Ord.cmp _ cmp_Ord_T t0 t1;
let' ret ← tmp__;
return ret);
dostep tmp__ ← @slice._T_.as.slice_SliceExt.binary_search_by _ _ fn t0 t1;
let' ret ← tmp__;
return (ret)


end core