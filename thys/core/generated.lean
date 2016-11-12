import core.pre

noncomputable theory

open bool
open [class] classical
open [notation] function
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit
open core

structure core.clone.Clone [class] (Self : Type₁)  :=
(clone : Self → sem (Self))

structure core.marker.Copy [class] (Self : Type₁)  extends core.clone.Clone Self 

structure core.marker.PhantomData (T : Type₁) := mk {} ::

structure core.ops.BitAnd [class] (Self : Type₁) (RHS : Type₁) (Output : Type₁) :=
(bitand : Self → RHS → sem (Output))

definition core.«u32 as core.ops.BitAnd».bitand (selfₐ : u32) (rhsₐ : u32) : sem (u32) :=
let' self ← selfₐ;
let' rhs ← rhsₐ;
let' t5 ← self;
let' t6 ← rhs;
let' ret ← bitand u32.bits t5 t6;
return (ret)


definition core.«&'a u32 as core.ops.BitAnd<u32>».bitand (selfₐ : u32) (otherₐ : u32) : sem (u32) :=
let' self ← selfₐ;
let' other ← otherₐ;
let' t5 ← self;
let' t6 ← other;
dostep «$tmp» ← @core.«u32 as core.ops.BitAnd».bitand t5 t6;
let' ret ← «$tmp»;
return (ret)


definition core.«&'a u32 as core.ops.BitAnd<u32>» [instance] := ⦃
  core.ops.BitAnd u32 u32 u32,
  bitand := core.«&'a u32 as core.ops.BitAnd<u32>».bitand
⦄

structure core.ops.RangeFull := mk {} ::

structure core.ops.Range (Idx : Type₁) := mk {} ::
(start : Idx)
(«end» : Idx)

structure core.ops.RangeFrom (Idx : Type₁) := mk {} ::
(start : Idx)

structure core.ops.RangeTo (Idx : Type₁) := mk {} ::
(«end» : Idx)

structure core.ops.RangeInclusive.Empty.struct (Idx : Type₁) := mk {} ::
(«at» : Idx)



structure core.ops.RangeInclusive.NonEmpty.struct (Idx : Type₁) := mk {} ::
(start : Idx)
(«end» : Idx)

inductive core.ops.RangeInclusive (Idx : Type₁) :=
| Empty {} : core.ops.RangeInclusive.Empty.struct Idx → core.ops.RangeInclusive Idx
| NonEmpty {} : core.ops.RangeInclusive.NonEmpty.struct Idx → core.ops.RangeInclusive Idx

structure core.ops.RangeToInclusive (Idx : Type₁) := mk {} ::
(«end» : Idx)

definition core.«u32 as core.clone.Clone».clone (selfₐ : u32) : sem (u32) :=
let' self ← selfₐ;
let' t3 ← self;
let' ret ← t3;
return (ret)


definition core.«u32 as core.clone.Clone» [instance] := ⦃
  core.clone.Clone u32,
  clone := core.«u32 as core.clone.Clone».clone
⦄

structure core.default.Default [class] (Self : Type₁)  :=
(default : sem (Self))

definition core.«i32 as core.default.Default».default : sem (i32) :=
let' ret ← (0 : int);
return (ret)


definition core.«i32 as core.default.Default» [instance] := ⦃
  core.default.Default i32,
  default := core.«i32 as core.default.Default».default
⦄

inductive core.option.Option (T : Type₁) :=
| None {} : core.option.Option T
| Some {} : T → core.option.Option T

structure core.iter.iterator.Iterator [class] (Self : Type₁) (Item : Type₁) :=
(next : Self → sem ((core.option.Option Item) × Self))

definition core.«[T] as core.slice.SliceExt».get {T : Type₁} (selfₐ : (slice T)) (indexₐ : usize) : sem ((core.option.Option T)) :=
let' self ← selfₐ;
let' index ← indexₐ;
let' t6 ← index;
let' t8 ← self;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len _ t8;
let' t7 ← «$tmp»;
let' t5 ← t6 <ᵇ t7;
if t5 = bool.tt then
let' t11 ← index;
let' t12 ← list.length self;
let' t13 ← t11 <ᵇ t12;
do «$tmp0» ← core.«[T] as core.slice.SliceExt».get_unchecked self t11;
let' t10 ← «$tmp0»;
let' t9 ← t10;
let' ret ← core.option.Option.Some t9;
return (ret)
else
let' ret ← core.option.Option.None;
return (ret)


structure core.cmp.PartialEq [class] (Self : Type₁) (Rhs : Type₁)  :=
(eq : Self → Rhs → sem (bool))

structure core.cmp.Eq [class] (Self : Type₁)  extends core.cmp.PartialEq Self Self 

inductive core.cmp.Ordering :=
| Less {} : core.cmp.Ordering
| Equal {} : core.cmp.Ordering
| Greater {} : core.cmp.Ordering

definition core.cmp.Ordering.discr (self : core.cmp.Ordering) : isize := match self with
| core.cmp.Ordering.Less := -1
| core.cmp.Ordering.Equal := 0
| core.cmp.Ordering.Greater := 1
end

structure core.cmp.PartialOrd [class] (Self : Type₁) (Rhs : Type₁)  extends core.cmp.PartialEq Self Rhs :=
(partial_cmp : Self → Rhs → sem ((core.option.Option (core.cmp.Ordering))))

structure core.cmp.Ord [class] (Self : Type₁)  extends core.cmp.Eq Self, core.cmp.PartialOrd Self Self :=
(cmp : Self → Self → sem ((core.cmp.Ordering)))

structure core.«[T] as core.slice.SliceExt».binary_search.closure_5594 (T : Type₁) := (val : T)

section
parameters {T : Type₁}
parameters [«core.cmp.Ord T» : core.cmp.Ord T]
section
parameters (a1 : (core.«[T] as core.slice.SliceExt».binary_search.closure_5594 T)) (pₐ : T)



definition core.«[T] as core.slice.SliceExt».binary_search.closure_5594.fn : sem ((core.cmp.Ordering) × (core.«[T] as core.slice.SliceExt».binary_search.closure_5594 T)) :=
let' p ← pₐ;
let' t4 ← p;
let' t5 ← (core.«[T] as core.slice.SliceExt».binary_search.closure_5594.val a1);
dostep «$tmp» ← @core.cmp.Ord.cmp _ «core.cmp.Ord T» t4 t5;
let' ret ← «$tmp»;
return (ret, a1)

end
definition core.«[T] as core.slice.SliceExt».binary_search.closure_5594.inst [instance] : core.ops.FnMut (core.«[T] as core.slice.SliceExt».binary_search.closure_5594 T) T (core.cmp.Ordering) :=
core.ops.FnMut.mk core.«[T] as core.slice.SliceExt».binary_search.closure_5594.fn

end

inductive core.result.Result (T : Type₁) (E : Type₁) :=
| Ok {} : T → core.result.Result T E
| Err {} : E → core.result.Result T E

section
open core.ops

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
definition core.«[T] as core.ops.Index<core.ops.Range<usize>>».index {T : Type₁} (self : slice T) (index : Range usize) : sem (slice T) :=
if Range.start index ≤ Range.«end» index ∧ Range.«end» index ≤ list.length self
then return (list.firstn (Range.«end» index - Range.start index) (list.dropn (Range.start index) self))
else mzero

end

definition core.«[T] as core.ops.Index<core.ops.RangeTo<usize>>».index {T : Type₁} (selfₐ : (slice T)) (indexₐ : (core.ops.RangeTo usize)) : sem ((slice T)) :=
let' self ← selfₐ;
let' index ← indexₐ;
let' t6 ← self;
let' t8 ← (0 : nat);
let' t10 ← (core.ops.RangeTo.«end» index);
let' t9 ← t10;
let' t7 ← core.ops.Range.mk t8 t9;
dostep «$tmp» ← @core.«[T] as core.ops.Index<core.ops.Range<usize>>».index _ t6 t7;
let' t5 ← «$tmp»;
let' ret ← t5;
return (ret)


definition core.«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index {T : Type₁} (selfₐ : (slice T)) (indexₐ : (core.ops.RangeFrom usize)) : sem ((slice T)) :=
let' self ← selfₐ;
let' index ← indexₐ;
let' t6 ← self;
let' t9 ← (core.ops.RangeFrom.start index);
let' t8 ← t9;
let' t11 ← self;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len _ t11;
let' t10 ← «$tmp»;
let' t7 ← core.ops.Range.mk t8 t10;
dostep «$tmp» ← @core.«[T] as core.ops.Index<core.ops.Range<usize>>».index _ t6 t7;
let' t5 ← «$tmp»;
let' ret ← t5;
return (ret)


definition core.«[T] as core.slice.SliceExt».split_at {T : Type₁} (selfₐ : (slice T)) (midₐ : usize) : sem (((slice T) × (slice T))) :=
let' self ← selfₐ;
let' mid ← midₐ;
let' t8 ← self;
let' t11 ← mid;
let' t10 ← t11;
let' t9 ← core.ops.RangeTo.mk t10;
dostep «$tmp» ← @core.«[T] as core.ops.Index<core.ops.RangeTo<usize>>».index _ t8 t9;
let' t7 ← «$tmp»;
let' t6 ← t7;
let' t5 ← t6;
let' t15 ← self;
let' t18 ← mid;
let' t17 ← t18;
let' t16 ← core.ops.RangeFrom.mk t17;
dostep «$tmp» ← @core.«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index _ t15 t16;
let' t14 ← «$tmp»;
let' t13 ← t14;
let' t12 ← t13;
let' ret ← (t5, t12);
return (ret)


structure core.slice.SliceExt [class] (Self : Type₁) (Item : Type₁) :=
(len : Self → sem (usize))

definition core.«[T] as core.slice.SliceExt» [instance] (T : Type₁) := ⦃
  core.slice.SliceExt (slice T) T,
  len := core.«[T] as core.slice.SliceExt».len
⦄

definition core.slice.SliceExt.is_empty {Self : Type₁} (Item : Type₁) [«core.slice.SliceExt Self» : core.slice.SliceExt Self Item] (selfₐ : Self) : sem (bool) :=
let' self ← selfₐ;
let' t4 ← self;
dostep «$tmp» ← @core.slice.SliceExt.len _ _ «core.slice.SliceExt Self» t4;
let' t3 ← «$tmp»;
let' ret ← t3 =ᵇ (0 : nat);
return (ret)


section
parameters {F : Type₁} {T : Type₁}
parameters [«core.ops.FnMut F (T)» : core.ops.FnMut F (T) (core.cmp.Ordering)]
section
parameters (selfₐ : (slice T)) (fₐ : F)

definition core.«[T] as core.slice.SliceExt».binary_search_by.loop_4 (state__ : F × usize × (slice T)) : sem (sum (F × usize × (slice T)) ((core.result.Result usize usize))) :=
match state__ with (f, base, s) :=
let' t13 ← s;
let' t16 ← s;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len _ t16;
let' t15 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shrs usize.bits t15 (1 : int));
let' t17 ← «$tmp0»;
let' t14 ← t17.1;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».split_at _ t13 t14;
let' t12 ← «$tmp»;
let' head ← t12.1;
let' tail ← t12.2;
let' t20 ← tail;
dostep «$tmp» ← @core.slice.SliceExt.is_empty _ _ (core.«[T] as core.slice.SliceExt» T) t20;
let' t19 ← «$tmp»;
if t19 = bool.tt then
do tmp__ ← let' t22 ← base;
let' ret ← core.result.Result.Err t22;
return (ret)
;
return (sum.inr tmp__)else
let' t18 ← ⋆;
let' t24 ← @lens.id F;
let' t28 ← list.length tail;
let' t29 ← (0 : nat) <ᵇ t28;
do «$tmp0» ← core.«[T] as core.slice.SliceExt».get_unchecked tail (0 : nat);
let' t27 ← «$tmp0»;
let' t26 ← t27;
let' t25 ← (t26);
do «$tmp0» ← lens.get t24 f;
dostep «$tmp» ← @core.ops.FnMut.call_mut _ _ _ «core.ops.FnMut F (T)» «$tmp0» t25;
match «$tmp» with (t23, «t24$») :=
do f ← lens.set t24 f «t24$»;
match t23 with
| core.cmp.Ordering.Less :=
let' t32 ← head;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len _ t32;
let' t31 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits t31 (1 : nat));
let' t33 ← «$tmp0»;
let' t30 ← t33.1;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits base t30);
let' t34 ← «$tmp0»;
let' base ← t34.1;
let' t37 ← tail;
let' t39 ← (1 : nat);
let' t38 ← core.ops.RangeFrom.mk t39;
dostep «$tmp» ← @core.«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index _ t37 t38;
let' t36 ← «$tmp»;
let' t35 ← t36;
let' s ← t35;
let' t6 ← ⋆;
return (sum.inl (f, base, s))
 | core.cmp.Ordering.Equal :=
do tmp__ ← let' t42 ← base;
let' t44 ← head;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».len _ t44;
let' t43 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits t42 t43);
let' t45 ← «$tmp0»;
let' t41 ← t45.1;
let' ret ← core.result.Result.Ok t41;
return (ret)
;
return (sum.inr tmp__) | core.cmp.Ordering.Greater :=
let' s ← head;
return (sum.inl (f, base, s))
end
end
end


definition core.«[T] as core.slice.SliceExt».binary_search_by : sem ((core.result.Result usize usize)) :=
let' self ← selfₐ;
let' f ← fₐ;
let' base ← (0 : nat);
let' t8 ← self;
let' s ← t8;
loop (core.«[T] as core.slice.SliceExt».binary_search_by.loop_4) (f, base, s)
end
end

definition core.«[T] as core.slice.SliceExt».binary_search {T : Type₁} [«core.cmp.Ord T» : core.cmp.Ord T] (selfₐ : (slice T)) (xₐ : T) : sem ((core.result.Result usize usize)) :=
let' self ← selfₐ;
let' x ← xₐ;
let' t5 ← self;
let' t7 ← x;
let' t6 ← core.«[T] as core.slice.SliceExt».binary_search.closure_5594.mk t7;
dostep «$tmp» ← @core.«[T] as core.slice.SliceExt».binary_search_by _ _ _ t5 t6;
let' ret ← «$tmp»;
return (ret)


