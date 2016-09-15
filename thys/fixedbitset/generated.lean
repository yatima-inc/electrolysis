import collections.generated
import core.generated

noncomputable theory

open bool
open [class] classical
open [notation] function
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace fixedbitset

definition BITS : usize :=
let' ret ← ((32 : nat));
ret

definition div_rem (xₐ : usize) (dₐ : usize) : sem ((usize × usize)) :=
let' x ← (xₐ);
let' d ← (dₐ);
let' t1 ← (x);
let' t2 ← (d);
let' t3 ← ((t2) =ᵈ ((0 : nat)));
do «$tmp0» ← checked.div (t1) (t2);
let' t0 ← «$tmp0»;
let' t5 ← (x);
let' t6 ← (d);
let' t7 ← ((t6) =ᵈ ((0 : nat)));
do «$tmp0» ← checked.mod (t5) (t6);
let' t4 ← «$tmp0»;
let' ret ← (((t0), (t4)));
return (ret)


structure FixedBitSet := mk {} ::
(data : (collections.vec.Vec u32))
(length : usize)

definition FixedBitSet.with_capacity (bitsₐ : usize) : sem ((FixedBitSet)) :=
let' bits ← (bitsₐ);
let' t1 ← (bits);
dostep «$tmp» ← @div_rem (t1) (BITS);
let' t0 ← «$tmp»;
let' blocks ← ((t0).1);
let' rem ← ((t0).2);
let' t4 ← (rem);
let' t3 ← ((t4) >ᵈ ((0 : nat)));
do «$tmp0» ← (bool_to_usize (t3));
let' t2 ← «$tmp0»;
let' t5 ← (((blocks) + (t2), true));
let' blocks ← ((t5).1);
let' t7 ← (blocks);
dostep «$tmp» ← @collections.vec.from_elem _ (core.«u32 as core.clone.Clone» ) ((0 : nat)) (t7);
let' t6 ← «$tmp»;
let' t9 ← (bits);
let' ret ← (FixedBitSet.mk (t6) (t9));
return (ret)


definition FixedBitSet.contains (selfₐ : (FixedBitSet)) (bitₐ : usize) : sem (bool) :=
let' self ← (selfₐ);
let' bit ← (bitₐ);
let' t1 ← (bit);
dostep «$tmp» ← @div_rem (t1) (BITS);
let' t0 ← «$tmp»;
let' block ← ((t0).1);
let' i ← ((t0).2);
let' t5 ← ((FixedBitSet.data (self)));
dostep «$tmp» ← @collections.«collections.vec.Vec<T> as core.ops.Deref».deref _ (t5);
let' t4 ← «$tmp»;
let' t3 ← (t4);
let' t6 ← (block);
dostep «$tmp» ← @collections.«[T]».get _ (t3) (t6);
let' t2 ← «$tmp»;
match t2 with
| core.option.Option.None :=
let' ret ← (ff);
return (ret)
 | core.option.Option.Some t2_0 :=
let' b ← (t2_0);
let' t8 ← (b);
let' t10 ← (i);
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shl ((1 : nat)) (int.of_nat (t10)));
let' t11 ← «$tmp0»;
let' t9 ← ((t11).1);
dostep «$tmp» ← @core.«&'a u32 as core.ops.BitAnd<u32>».bitand (t8) (t9);
let' t7 ← «$tmp»;
let' ret ← ((t7) ≠ᵈ ((0 : nat)));
return (ret)
end


definition FixedBitSet.insert.FILE_LINE : (string × u32) :=
let' ret ← ((("thys/fixedbitset/src/src/lib.rs"), ((87 : nat))));
ret

definition FixedBitSet.insert (selfₐ : (FixedBitSet)) (bitₐ : usize) : sem (unit × (FixedBitSet)) :=
let' self ← lens.id;
let' bit ← (bitₐ);
let' t3 ← (bit);
do «$tmp0» ← do «$tmp0» ← lens.get (self) selfₐ;
return ((FixedBitSet.length «$tmp0»));
let' t4 ← «$tmp0»;
let' t2 ← ((t3) <ᵈ (t4));
let' t1 ← (bool.bnot (t2));
ifb (t1) then
let' t7 ← (FixedBitSet.insert.FILE_LINE);
let' t6 ← (t7);
mzero
else
let' t0 ← (⋆);
let' t9 ← (bit);
dostep «$tmp» ← @div_rem (t9) (BITS);
let' t8 ← «$tmp»;
let' block ← ((t8).1);
let' i ← ((t8).2);
let' t11 ← (i);
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shl ((1 : nat)) (int.of_nat (t11)));
let' t12 ← «$tmp0»;
let' t10 ← ((t12).1);
let' t16 ← (self ∘ₗ lens.mk (return ∘ FixedBitSet.data) (λ (o : FixedBitSet) i, return ⦃ FixedBitSet, data := i, o ⦄));
do «$tmp0» ← lens.get (t16) selfₐ;
dostep «$tmp» ← @collections.«collections.vec.Vec<T> as core.ops.DerefMut».deref_mut _ «$tmp0»;
match «$tmp» with («t15$», «t16$») :=
do selfₐ ← lens.set t16 selfₐ «t16$»;
let' t15 ← (t16 ∘ₗ «t15$»);
let' t14 ← (t15);
let' t17 ← (block);
do «$tmp0» ← lens.get (t14) selfₐ;
dostep «$tmp» ← @collections.«[T]».get_unchecked_mut _ «$tmp0» (t17);
match «$tmp» with («t13$», «t14$») :=
do selfₐ ← lens.set t14 selfₐ «t14$»;
let' t13 ← (t14 ∘ₗ «t13$»);
do «$tmp0» ← do «$tmp0» ← lens.get (t13) selfₐ;
return («$tmp0» || (t10));
do selfₐ ← lens.set t13 selfₐ «$tmp0»;
let' ret ← (⋆);
return (ret, selfₐ)
end
end


end fixedbitset