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

namespace core

structure clone.Clone [class] (Self : Type₁)  :=
(clone : Self → sem (Self))

structure marker.Copy [class] (Self : Type₁)  extends clone.Clone Self 

structure marker.PhantomData (T : Type₁) := mk {} ::

structure ops.BitAnd [class] (Self : Type₁) (RHS : Type₁) (Output : Type₁) :=
(bitand : Self → RHS → sem (Output))

definition «u32 as core.ops.BitAnd».bitand (selfₐ : u32) (rhsₐ : u32) : sem (u32) :=
let' self ← (selfₐ);
let' rhs ← (rhsₐ);
let' t0 ← (self);
let' t1 ← (rhs);
let' ret ← ((t0) && (t1));
return (ret)


definition «&'a u32 as core.ops.BitAnd<u32>».bitand (selfₐ : u32) (otherₐ : u32) : sem (u32) :=
let' self ← (selfₐ);
let' other ← (otherₐ);
let' t0 ← (self);
let' t1 ← (other);
dostep «$tmp» ← @«u32 as core.ops.BitAnd».bitand (t0) (t1);
let' ret ← «$tmp»;
return (ret)


definition «&'a u32 as core.ops.BitAnd<u32>» [instance] := ⦃
  ops.BitAnd u32 u32 u32,
  bitand := «&'a u32 as core.ops.BitAnd<u32>».bitand
⦄

definition «u32 as core.clone.Clone».clone (selfₐ : u32) : sem (u32) :=
let' self ← (selfₐ);
let' t0 ← (self);
let' ret ← (t0);
return (ret)


definition «u32 as core.clone.Clone» [instance] := ⦃
  clone.Clone u32,
  clone := «u32 as core.clone.Clone».clone
⦄

structure default.Default [class] (Self : Type₁)  :=
(default : sem (Self))

definition «i32 as core.default.Default».default : sem (i32) :=
let' ret ← ((0 : int));
return (ret)


definition «i32 as core.default.Default» [instance] := ⦃
  default.Default i32,
  default := «i32 as core.default.Default».default
⦄

inductive option.Option (T : Type₁) :=
| None {} : option.Option T
| Some {} : T → option.Option T

structure iter.iterator.Iterator [class] (Self : Type₁) (Item : Type₁) :=
(next : Self → sem ((option.Option Item) × Self))

definition «[T] as core.slice.SliceExt».get {T : Type₁} (selfₐ : (slice T)) (indexₐ : usize) : sem ((option.Option T)) :=
let' self ← (selfₐ);
let' index ← (indexₐ);
let' t1 ← (index);
let' t3 ← (self);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».len _ (t3);
let' t2 ← «$tmp»;
let' t0 ← ((t1) <ᵇ (t2));
if (t0) = bool.tt then
let' t6 ← (index);
let' t7 ← (list.length (self));
let' t8 ← ((t6) <ᵇ (t7));
do «$tmp0» ← «[T] as core.slice.SliceExt».get_unchecked (self) (t6);
let' t5 ← «$tmp0»;
let' t4 ← (t5);
let' ret ← (option.Option.Some (t4));
return (ret)
else
let' ret ← (option.Option.None);
return (ret)


inductive cmp.Ordering :=
| Less {} : cmp.Ordering
| Equal {} : cmp.Ordering
| Greater {} : cmp.Ordering

definition cmp.Ordering.discr (self : cmp.Ordering) : isize := match self with
| cmp.Ordering.Less := -1
| cmp.Ordering.Equal := 0
| cmp.Ordering.Greater := 1
end

structure ops.RangeFrom (Idx : Type₁) := mk {} ::
(start : Idx)

inductive result.Result (T : Type₁) (E : Type₁) :=
| Ok {} : T → result.Result T E
| Err {} : E → result.Result T E

structure ops.RangeTo (Idx : Type₁) := mk {} ::
(«end» : Idx)

structure ops.Range (Idx : Type₁) := mk {} ::
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

definition «[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index {T : Type₁} (selfₐ : (slice T)) (indexₐ : (ops.RangeFrom usize)) : sem ((slice T)) :=
let' self ← (selfₐ);
let' index ← (indexₐ);
let' t1 ← (self);
let' t4 ← ((ops.RangeFrom.start (index)));
let' t3 ← (t4);
let' t6 ← (self);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».len _ (t6);
let' t5 ← «$tmp»;
let' t2 ← (ops.Range.mk (t3) (t5));
dostep «$tmp» ← @«[T] as core.ops.Index<core.ops.Range<usize>>».index _ (t1) (t2);
let' t0 ← «$tmp»;
let' ret ← (t0);
return (ret)


definition «[T] as core.ops.Index<core.ops.RangeTo<usize>>».index {T : Type₁} (selfₐ : (slice T)) (indexₐ : (ops.RangeTo usize)) : sem ((slice T)) :=
let' self ← (selfₐ);
let' index ← (indexₐ);
let' t1 ← (self);
let' t3 ← ((0 : nat));
let' t5 ← ((ops.RangeTo.«end» (index)));
let' t4 ← (t5);
let' t2 ← (ops.Range.mk (t3) (t4));
dostep «$tmp» ← @«[T] as core.ops.Index<core.ops.Range<usize>>».index _ (t1) (t2);
let' t0 ← «$tmp»;
let' ret ← (t0);
return (ret)


definition «[T] as core.slice.SliceExt».split_at {T : Type₁} (selfₐ : (slice T)) (midₐ : usize) : sem (((slice T) × (slice T))) :=
let' self ← (selfₐ);
let' mid ← (midₐ);
let' t3 ← (self);
let' t6 ← (mid);
let' t5 ← (t6);
let' t4 ← (ops.RangeTo.mk (t5));
dostep «$tmp» ← @«[T] as core.ops.Index<core.ops.RangeTo<usize>>».index _ (t3) (t4);
let' t2 ← «$tmp»;
let' t1 ← (t2);
let' t0 ← (t1);
let' t10 ← (self);
let' t13 ← (mid);
let' t12 ← (t13);
let' t11 ← (ops.RangeFrom.mk (t12));
dostep «$tmp» ← @«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index _ (t10) (t11);
let' t9 ← «$tmp»;
let' t8 ← (t9);
let' t7 ← (t8);
let' ret ← (((t0), (t7)));
return (ret)


structure slice.SliceExt [class] (Self : Type₁) (Item : Type₁) :=
(len : Self → sem (usize))

definition «[T] as core.slice.SliceExt» [instance] (T : Type₁) := ⦃
  slice.SliceExt (slice T) T,
  len := «[T] as core.slice.SliceExt».len
⦄

definition slice.SliceExt.is_empty {Self : Type₁} (Item : Type₁) [«slice.SliceExt Self» : slice.SliceExt Self Item] (selfₐ : Self) : sem (bool) :=
let' self ← (selfₐ);
let' t1 ← (self);
dostep «$tmp» ← @slice.SliceExt.len _ _ «slice.SliceExt Self» (t1);
let' t0 ← «$tmp»;
let' ret ← ((t0) =ᵇ ((0 : nat)));
return (ret)


section
parameters {F : Type₁} {T : Type₁}
parameters [«ops.FnMut F (T)» : ops.FnMut F (T) (cmp.Ordering)]
parameters (selfₐ : (slice T)) (fₐ : F)

definition «[T] as core.slice.SliceExt».binary_search_by.loop_4 (state__ : F × usize × (slice T)) : sem (sum (F × usize × (slice T)) ((result.Result usize usize))) :=
match state__ with (f, base, s) :=
let' t4 ← (s);
let' t7 ← (s);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».len _ (t7);
let' t6 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shr (t6) ((1 : int)));
let' t8 ← «$tmp0»;
let' t5 ← ((t8).1);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».split_at _ (t4) (t5);
let' t3 ← «$tmp»;
let' head ← ((t3).1);
let' tail ← ((t3).2);
let' t11 ← (tail);
dostep «$tmp» ← @slice.SliceExt.is_empty _ _ («[T] as core.slice.SliceExt» T) (t11);
let' t10 ← «$tmp»;
if (t10) = bool.tt then
do tmp__ ← let' t13 ← (base);
let' ret ← (result.Result.Err (t13));
return (ret)
;
return (sum.inr tmp__)else
let' t9 ← (⋆);
let' t15 ← lens.id;
let' t19 ← (list.length (tail));
let' t20 ← (((0 : nat)) <ᵇ (t19));
do «$tmp0» ← «[T] as core.slice.SliceExt».get_unchecked (tail) ((0 : nat));
let' t18 ← «$tmp0»;
let' t17 ← (t18);
let' t16 ← (((t17)));
do «$tmp0» ← lens.get (t15) f;
dostep «$tmp» ← @ops.FnMut.call_mut _ _ _ «ops.FnMut F (T)» «$tmp0» (t16);
match «$tmp» with (t14, «t15$») :=
do f ← lens.set t15 f «t15$»;
match t14 with
| cmp.Ordering.Less :=
let' t23 ← (head);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».len _ (t23);
let' t22 ← «$tmp»;
let' t24 ← (((t22) + ((1 : nat)), true));
let' t21 ← ((t24).1);
let' t25 ← (((base) + (t21), true));
let' base ← ((t25).1);
let' t28 ← (tail);
let' t30 ← ((1 : nat));
let' t29 ← (ops.RangeFrom.mk (t30));
dostep «$tmp» ← @«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index _ (t28) (t29);
let' t27 ← «$tmp»;
let' t26 ← (t27);
let' s ← (t26);
let' t0 ← (⋆);
return (sum.inl (f, base, s))
 | cmp.Ordering.Equal :=
do tmp__ ← let' t33 ← (base);
let' t35 ← (head);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».len _ (t35);
let' t34 ← «$tmp»;
let' t36 ← (((t33) + (t34), true));
let' t32 ← ((t36).1);
let' ret ← (result.Result.Ok (t32));
return (ret)
;
return (sum.inr tmp__) | cmp.Ordering.Greater :=
let' s ← (head);
return (sum.inl (f, base, s))
end
end
end


definition «[T] as core.slice.SliceExt».binary_search_by : sem ((result.Result usize usize)) :=
let' self ← (selfₐ);
let' f ← (fₐ);
let' base ← ((0 : nat));
let' t1 ← (self);
let' s ← (t1);
loop («[T] as core.slice.SliceExt».binary_search_by.loop_4) (f, base, s)
end

structure cmp.PartialEq [class] (Self : Type₁) (Rhs : Type₁)  :=
(eq : Self → Rhs → sem (bool))

structure cmp.PartialOrd [class] (Self : Type₁) (Rhs : Type₁)  extends cmp.PartialEq Self Rhs :=
(partial_cmp : Self → Rhs → sem ((option.Option (cmp.Ordering))))

structure cmp.Eq [class] (Self : Type₁)  extends cmp.PartialEq Self Self 

structure cmp.Ord [class] (Self : Type₁)  extends cmp.Eq Self, cmp.PartialOrd Self Self :=
(cmp : Self → Self → sem ((cmp.Ordering)))

definition «[T] as core.slice.SliceExt».binary_search {T : Type₁} [«cmp.Ord T» : cmp.Ord T] (selfₐ : (slice T)) (xₐ : T) : sem ((result.Result usize usize)) :=
let' self ← (selfₐ);
let' x ← (xₐ);
let' t0 ← (self);
let' t2 ← (x);
let' t1 ← ((λ upvarsₐ pₐ, let' p ← (pₐ);
let' t0 ← (p);
let' t1 ← ((upvarsₐ));
dostep «$tmp» ← @cmp.Ord.cmp _ «cmp.Ord T» (t0) (t1);
let' ret ← «$tmp»;
return ret) (t2));
dostep «$tmp» ← @«[T] as core.slice.SliceExt».binary_search_by _ _ fn (t0) (t1);
let' ret ← «$tmp»;
return (ret)


end core