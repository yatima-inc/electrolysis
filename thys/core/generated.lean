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

structure default.Default [class] (Self : Type₁)  :=
(default : sem (Self))

definition «i32 as core.default.Default».default : sem (i32) :=
let' ret ← (0 : int);
return (ret)


definition «i32 as core.default.Default» [instance] := ⦃
  default.Default i32,
  default := «i32 as core.default.Default».default
⦄

inductive cmp.Ordering :=
| Less {} : cmp.Ordering
| Equal {} : cmp.Ordering
| Greater {} : cmp.Ordering

structure ops.RangeFrom (Idx : Type₁) := «{{constructor}}» {} ::
(start : Idx)

inductive result.Result (T : Type₁) (E : Type₁) :=
| Ok {} : T → result.Result T E
| Err {} : E → result.Result T E

structure ops.RangeTo (Idx : Type₁) := «{{constructor}}» {} ::
(«end» : Idx)

structure ops.Range (Idx : Type₁) := «{{constructor}}» {} ::
(start : Idx)
(«end» : Idx)

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
definition «[T] as core.ops.Index<core.ops.Range<usize>>».index {T : Type₁} (self : slice T) (index : ops.Range usize) : sem (slice T) :=
if ops.Range.start index ≤ ops.Range.«end» index ∧ ops.Range.«end» index ≤ list.length self
then return (list.firstn (ops.Range.«end» index - ops.Range.start index) (list.dropn (ops.Range.start index) self))
else mzero

definition «[T] as core.ops.Index<core.ops.RangeTo<usize>>».index {T : Type₁} (self : (slice T)) (index : (ops.RangeTo usize)) : sem ((slice T)) :=
let' t1 ← self;
let' t3 ← (0 : nat);
let' t5 ← (ops.RangeTo.«end» index);
let' t4 ← t5;
let' t2 ← ops.Range.«{{constructor}}» t3 t4;
dostep tmp__ ← @«[T] as core.ops.Index<core.ops.Range<usize>>».index _ t1 t2;
let' t0 ← tmp__;
let' ret ← t0;
return (ret)


definition «[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index {T : Type₁} (self : (slice T)) (index : (ops.RangeFrom usize)) : sem ((slice T)) :=
let' t1 ← self;
let' t4 ← (ops.RangeFrom.start index);
let' t3 ← t4;
let' t6 ← self;
dostep tmp__ ← @«[T] as core.slice.SliceExt».len _ t6;
let' t5 ← tmp__;
let' t2 ← ops.Range.«{{constructor}}» t3 t5;
dostep tmp__ ← @«[T] as core.ops.Index<core.ops.Range<usize>>».index _ t1 t2;
let' t0 ← tmp__;
let' ret ← t0;
return (ret)


definition «[T] as core.slice.SliceExt».split_at {T : Type₁} (self : (slice T)) (mid : usize) : sem (((slice T) × (slice T))) :=
let' t3 ← self;
let' t6 ← mid;
let' t5 ← t6;
let' t4 ← ops.RangeTo.«{{constructor}}» t5;
dostep tmp__ ← @«[T] as core.ops.Index<core.ops.RangeTo<usize>>».index _ t3 t4;
let' t2 ← tmp__;
let' t1 ← t2;
let' t0 ← t1;
let' t10 ← self;
let' t13 ← mid;
let' t12 ← t13;
let' t11 ← ops.RangeFrom.«{{constructor}}» t12;
dostep tmp__ ← @«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index _ t10 t11;
let' t9 ← tmp__;
let' t8 ← t9;
let' t7 ← t8;
let' ret ← (t0, t7);
return (ret)


structure slice.SliceExt [class] (Self : Type₁) (Item : Type₁) :=
(len : Self → sem (usize))

definition «[T] as core.slice.SliceExt» [instance] (T : Type₁) := ⦃
  slice.SliceExt (slice T) T,
  len := «[T] as core.slice.SliceExt».len
⦄

definition slice.SliceExt.is_empty {Self : Type₁} (Item : Type₁) [«slice.SliceExt Self» : slice.SliceExt Self Item] (self : Self) : sem (Prop) :=
let' t1 ← self;
dostep tmp__ ← @slice.SliceExt.len _ _ «slice.SliceExt Self» t1;
let' t0 ← tmp__;
let' ret ← t0 = (0 : nat);
return (ret)


section
parameters {F : Type₁} {T : Type₁}
parameters [«ops.FnMut F (T)» : ops.FnMut F (T) (cmp.Ordering)]
parameters (self : (slice T)) (f : F)

definition «[T] as core.slice.SliceExt».binary_search_by.loop_4 (state__ : F × usize × (slice T)) : sem (sum (F × usize × (slice T)) ((result.Result usize usize))) :=
match state__ with (f, base, s) :=
let' t4 ← s;
let' t7 ← s;
dostep tmp__ ← @«[T] as core.slice.SliceExt».len _ t7;
let' t6 ← tmp__;
do tmp__ ← sem.map (λx, (x, true)) (checked.shr t6 (1 : int));
let' t8 ← tmp__;
let' t5 ← t8.1;
dostep tmp__ ← @«[T] as core.slice.SliceExt».split_at _ t4 t5;
let' t3 ← tmp__;
let' head ← t3.1;
let' tail ← t3.2;
let' t11 ← tail;
dostep tmp__ ← @slice.SliceExt.is_empty _ _ («[T] as core.slice.SliceExt» T) t11;
let' t10 ← tmp__;
if t10 then
do tmp__ ← let' t13 ← base;
let' ret ← result.Result.Err t13;
return (ret)
;
return (sum.inr tmp__)else
let' t19 ← list.length tail;
let' t20 ← (0 : nat) < t19;
do tmp__ ← «[T] as core.slice.SliceExt».get_unchecked tail (0 : nat);
let' t18 ← tmp__;
let' t17 ← t18;
let' t16 ← (t17);
dostep tmp__ ← @ops.FnMut.call_mut _ _ _ «ops.FnMut F (T)» f t16;
match tmp__ with (t14, f) :=
match t14 with
| cmp.Ordering.Less :=
let' t23 ← head;
dostep tmp__ ← @«[T] as core.slice.SliceExt».len _ t23;
let' t22 ← tmp__;
let' t24 ← (t22 + (1 : nat), true);
let' t21 ← t24.1;
let' t25 ← (base + t21, true);
let' base ← t25.1;
let' t28 ← tail;
let' t30 ← (1 : nat);
let' t29 ← ops.RangeFrom.«{{constructor}}» t30;
dostep tmp__ ← @«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index _ t28 t29;
let' t27 ← tmp__;
let' t26 ← t27;
let' s ← t26;
return (sum.inl (f, base, s))
 | cmp.Ordering.Equal :=
do tmp__ ← let' t33 ← base;
let' t35 ← head;
dostep tmp__ ← @«[T] as core.slice.SliceExt».len _ t35;
let' t34 ← tmp__;
let' t36 ← (t33 + t34, true);
let' t32 ← t36.1;
let' ret ← result.Result.Ok t32;
return (ret)
;
return (sum.inr tmp__) | cmp.Ordering.Greater :=
let' s ← head;
return (sum.inl (f, base, s))
end
end
end


definition «[T] as core.slice.SliceExt».binary_search_by : sem ((result.Result usize usize)) :=
let' base ← (0 : nat);
let' t1 ← self;
let' s ← t1;
loop («[T] as core.slice.SliceExt».binary_search_by.loop_4) (f, base, s)
end

structure cmp.PartialEq [class] (Self : Type₁) (Rhs : Type₁)  :=
(eq : Self → Rhs → sem (Prop))

structure cmp.Eq [class] (Self : Type₁) extends cmp.PartialEq Self Self 

inductive option.Option (T : Type₁) :=
| None {} : option.Option T
| Some {} : T → option.Option T

structure cmp.PartialOrd [class] (Self : Type₁) (Rhs : Type₁) extends cmp.PartialEq Self Rhs :=
(partial_cmp : Self → Rhs → sem ((option.Option (cmp.Ordering))))

structure cmp.Ord [class] (Self : Type₁) extends cmp.Eq Self, cmp.PartialOrd Self Self :=
(cmp : Self → Self → sem ((cmp.Ordering)))

definition «[T] as core.slice.SliceExt».binary_search {T : Type₁} [«cmp.Ord T» : cmp.Ord T] (self : (slice T)) (x : T) : sem ((result.Result usize usize)) :=
let' t0 ← self;
let' t2 ← x;
let' t1 ← (λp, let' t0 ← p;
let' t1 ← t2;
dostep tmp__ ← @cmp.Ord.cmp _ «cmp.Ord T» t0 t1;
let' ret ← tmp__;
return ret);
dostep tmp__ ← @«[T] as core.slice.SliceExt».binary_search_by _ _ fn t0 t1;
let' ret ← tmp__;
return (ret)


end core