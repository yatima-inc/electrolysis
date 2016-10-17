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
let' t5 ← (self);
let' t6 ← (rhs);
let' ret ← (bitand u32.bits (t5) (t6));
return (ret)


definition «&'a u32 as core.ops.BitAnd<u32>».bitand (selfₐ : u32) (otherₐ : u32) : sem (u32) :=
let' self ← (selfₐ);
let' other ← (otherₐ);
let' t5 ← (self);
let' t6 ← (other);
dostep «$tmp» ← @«u32 as core.ops.BitAnd».bitand (t5) (t6);
let' ret ← «$tmp»;
return (ret)


definition «&'a u32 as core.ops.BitAnd<u32>» [instance] := ⦃
  ops.BitAnd u32 u32 u32,
  bitand := «&'a u32 as core.ops.BitAnd<u32>».bitand
⦄

definition «u32 as core.clone.Clone».clone (selfₐ : u32) : sem (u32) :=
let' self ← (selfₐ);
let' t3 ← (self);
let' ret ← (t3);
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
let' t6 ← (index);
let' t8 ← (self);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».len _ (t8);
let' t7 ← «$tmp»;
let' t5 ← ((t6) <ᵇ (t7));
if (t5) = bool.tt then
let' t11 ← (index);
let' t12 ← (list.length (self));
let' t13 ← ((t11) <ᵇ (t12));
do «$tmp0» ← «[T] as core.slice.SliceExt».get_unchecked (self) (t11);
let' t10 ← «$tmp0»;
let' t9 ← (t10);
let' ret ← (option.Option.Some (t9));
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

inductive result.Result (T : Type₁) (E : Type₁) :=
| Ok {} : T → result.Result T E
| Err {} : E → result.Result T E

structure ops.RangeFrom (Idx : Type₁) := mk {} ::
(start : Idx)

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

definition «[T] as core.ops.Index<core.ops.RangeTo<usize>>».index {T : Type₁} (selfₐ : (slice T)) (indexₐ : (ops.RangeTo usize)) : sem ((slice T)) :=
let' self ← (selfₐ);
let' index ← (indexₐ);
let' t6 ← (self);
let' t8 ← ((0 : nat));
let' t10 ← ((ops.RangeTo.«end» (index)));
let' t9 ← (t10);
let' t7 ← (ops.Range.mk (t8) (t9));
dostep «$tmp» ← @«[T] as core.ops.Index<core.ops.Range<usize>>».index _ (t6) (t7);
let' t5 ← «$tmp»;
let' ret ← (t5);
return (ret)


definition «[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index {T : Type₁} (selfₐ : (slice T)) (indexₐ : (ops.RangeFrom usize)) : sem ((slice T)) :=
let' self ← (selfₐ);
let' index ← (indexₐ);
let' t6 ← (self);
let' t9 ← ((ops.RangeFrom.start (index)));
let' t8 ← (t9);
let' t11 ← (self);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».len _ (t11);
let' t10 ← «$tmp»;
let' t7 ← (ops.Range.mk (t8) (t10));
dostep «$tmp» ← @«[T] as core.ops.Index<core.ops.Range<usize>>».index _ (t6) (t7);
let' t5 ← «$tmp»;
let' ret ← (t5);
return (ret)


definition «[T] as core.slice.SliceExt».split_at {T : Type₁} (selfₐ : (slice T)) (midₐ : usize) : sem (((slice T) × (slice T))) :=
let' self ← (selfₐ);
let' mid ← (midₐ);
let' t8 ← (self);
let' t11 ← (mid);
let' t10 ← (t11);
let' t9 ← (ops.RangeTo.mk (t10));
dostep «$tmp» ← @«[T] as core.ops.Index<core.ops.RangeTo<usize>>».index _ (t8) (t9);
let' t7 ← «$tmp»;
let' t6 ← (t7);
let' t5 ← (t6);
let' t15 ← (self);
let' t18 ← (mid);
let' t17 ← (t18);
let' t16 ← (ops.RangeFrom.mk (t17));
dostep «$tmp» ← @«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index _ (t15) (t16);
let' t14 ← «$tmp»;
let' t13 ← (t14);
let' t12 ← (t13);
let' ret ← (((t5), (t12)));
return (ret)


structure slice.SliceExt [class] (Self : Type₁) (Item : Type₁) :=
(len : Self → sem (usize))

definition «[T] as core.slice.SliceExt» [instance] (T : Type₁) := ⦃
  slice.SliceExt (slice T) T,
  len := «[T] as core.slice.SliceExt».len
⦄

definition slice.SliceExt.is_empty {Self : Type₁} (Item : Type₁) [«slice.SliceExt Self» : slice.SliceExt Self Item] (selfₐ : Self) : sem (bool) :=
let' self ← (selfₐ);
let' t4 ← (self);
dostep «$tmp» ← @slice.SliceExt.len _ _ «slice.SliceExt Self» (t4);
let' t3 ← «$tmp»;
let' ret ← ((t3) =ᵇ ((0 : nat)));
return (ret)


section
parameters {F : Type₁} {T : Type₁}
parameters [«ops.FnMut F (T)» : ops.FnMut F (T) (cmp.Ordering)]
parameters (selfₐ : (slice T)) (fₐ : F)

definition «[T] as core.slice.SliceExt».binary_search_by.loop_4 (state__ : F × usize × (slice T)) : sem (sum (F × usize × (slice T)) ((result.Result usize usize))) :=
match state__ with (f, base, s) :=
let' t13 ← (s);
let' t16 ← (s);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».len _ (t16);
let' t15 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shrs usize.bits (t15) ((1 : int)));
let' t17 ← «$tmp0»;
let' t14 ← ((t17).1);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».split_at _ (t13) (t14);
let' t12 ← «$tmp»;
let' head ← ((t12).1);
let' tail ← ((t12).2);
let' t20 ← (tail);
dostep «$tmp» ← @slice.SliceExt.is_empty _ _ («[T] as core.slice.SliceExt» T) (t20);
let' t19 ← «$tmp»;
if (t19) = bool.tt then
do tmp__ ← let' t22 ← (base);
let' ret ← (result.Result.Err (t22));
return (ret)
;
return (sum.inr tmp__)else
let' t18 ← (⋆);
let' t24 ← lens.id;
let' t28 ← (list.length (tail));
let' t29 ← (((0 : nat)) <ᵇ (t28));
do «$tmp0» ← «[T] as core.slice.SliceExt».get_unchecked (tail) ((0 : nat));
let' t27 ← «$tmp0»;
let' t26 ← (t27);
let' t25 ← (((t26)));
do «$tmp0» ← lens.get (t24) (f);
dostep «$tmp» ← @ops.FnMut.call_mut _ _ _ «ops.FnMut F (T)» «$tmp0» (t25);
match «$tmp» with (t23, «t24$») :=
do (f) ← lens.set (t24) (f) «t24$»;
match t23 with
| cmp.Ordering.Less :=
let' t32 ← (head);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».len _ (t32);
let' t31 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits (t31) ((1 : nat)));
let' t33 ← «$tmp0»;
let' t30 ← ((t33).1);
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits (base) (t30));
let' t34 ← «$tmp0»;
let' base ← ((t34).1);
let' t37 ← (tail);
let' t39 ← ((1 : nat));
let' t38 ← (ops.RangeFrom.mk (t39));
dostep «$tmp» ← @«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index _ (t37) (t38);
let' t36 ← «$tmp»;
let' t35 ← (t36);
let' s ← (t35);
let' t6 ← (⋆);
return (sum.inl (f, base, s))
 | cmp.Ordering.Equal :=
do tmp__ ← let' t42 ← (base);
let' t44 ← (head);
dostep «$tmp» ← @«[T] as core.slice.SliceExt».len _ (t44);
let' t43 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits (t42) (t43));
let' t45 ← «$tmp0»;
let' t41 ← ((t45).1);
let' ret ← (result.Result.Ok (t41));
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
let' t8 ← (self);
let' s ← (t8);
loop («[T] as core.slice.SliceExt».binary_search_by.loop_4) (f, base, s)
end

structure cmp.PartialEq [class] (Self : Type₁) (Rhs : Type₁)  :=
(eq : Self → Rhs → sem (bool))

structure cmp.Eq [class] (Self : Type₁)  extends cmp.PartialEq Self Self 

structure cmp.PartialOrd [class] (Self : Type₁) (Rhs : Type₁)  extends cmp.PartialEq Self Rhs :=
(partial_cmp : Self → Rhs → sem ((option.Option (cmp.Ordering))))

structure cmp.Ord [class] (Self : Type₁)  extends cmp.Eq Self, cmp.PartialOrd Self Self :=
(cmp : Self → Self → sem ((cmp.Ordering)))

definition «[T] as core.slice.SliceExt».binary_search {T : Type₁} [«cmp.Ord T» : cmp.Ord T] (selfₐ : (slice T)) (xₐ : T) : sem ((result.Result usize usize)) :=
let' self ← (selfₐ);
let' x ← (xₐ);
let' t5 ← (self);
let' t7 ← (x);
let' t6 ← ((λ a1 pₐ, let' p ← (pₐ);
let' t4 ← (p);
let' t5 ← ((a1));
dostep «$tmp» ← @cmp.Ord.cmp _ «cmp.Ord T» (t4) (t5);
let' ret ← «$tmp»;
return (ret, a1)
) (t7));
dostep «$tmp» ← @«[T] as core.slice.SliceExt».binary_search_by _ _ _ (t5) (t6);
let' ret ← «$tmp»;
return (ret)


end core