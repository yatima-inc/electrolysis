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

definition BITS : sem usize :=
let' ret ← ((32 : nat));
return (ret)


definition div_rem (xₐ : usize) (dₐ : usize) : sem ((usize × usize)) :=
let' x ← (xₐ);
let' d ← (dₐ);
let' t6 ← (x);
let' t7 ← (d);
let' t8 ← ((t7) =ᵇ ((0 : nat)));
do «$tmp0» ← checked.div usize.bits (t6) (t7);
let' t5 ← «$tmp0»;
let' t10 ← (x);
let' t11 ← (d);
let' t12 ← ((t11) =ᵇ ((0 : nat)));
do «$tmp0» ← checked.rem usize.bits (t10) (t11);
let' t9 ← «$tmp0»;
let' ret ← (((t5), (t9)));
return (ret)


structure FixedBitSet := mk {} ::
(data : (collections.vec.Vec u32))
(length : usize)

definition FixedBitSet.with_capacity (bitsₐ : usize) : sem ((FixedBitSet)) :=
let' bits ← (bitsₐ);
let' t6 ← (bits);
do «$tmp1» ← BITS;
dostep «$tmp» ← @div_rem (t6) «$tmp1»;
let' t5 ← «$tmp»;
let' blocks ← ((t5).1);
let' rem ← ((t5).2);
let' t9 ← (rem);
let' t8 ← ((t9) >ᵇ ((0 : nat)));
do «$tmp0» ← (bool_to_usize (t8));
let' t7 ← «$tmp0»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.add usize.bits (blocks) (t7));
let' t10 ← «$tmp0»;
let' blocks ← ((t10).1);
let' t12 ← (blocks);
dostep «$tmp» ← @collections.vec.from_elem _ (core.«u32 as core.clone.Clone» ) ((0 : nat)) (t12);
let' t11 ← «$tmp»;
let' t14 ← (bits);
let' ret ← (FixedBitSet.mk (t11) (t14));
return (ret)


definition FixedBitSet.contains (selfₐ : (FixedBitSet)) (bitₐ : usize) : sem (bool) :=
let' self ← (selfₐ);
let' bit ← (bitₐ);
let' t8 ← (bit);
do «$tmp1» ← BITS;
dostep «$tmp» ← @div_rem (t8) «$tmp1»;
let' t7 ← «$tmp»;
let' block ← ((t7).1);
let' i ← ((t7).2);
let' t12 ← ((FixedBitSet.data (self)));
dostep «$tmp» ← @collections.«collections.vec.Vec<T> as core.ops.Deref».deref _ (t12);
let' t11 ← «$tmp»;
let' t10 ← (t11);
let' t13 ← (block);
dostep «$tmp» ← @collections.«[T]».get _ (t10) (t13);
let' t9 ← «$tmp»;
match t9 with
| core.option.Option.None :=
let' ret ← (ff);
return (ret)
 | core.option.Option.Some t9_0 :=
let' b ← (t9_0);
let' t16 ← (b);
let' t18 ← (i);
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shl u32.bits ((1 : nat)) (t18));
let' t19 ← «$tmp0»;
let' t17 ← ((t19).1);
dostep «$tmp» ← @core.«&'a u32 as core.ops.BitAnd<u32>».bitand (t16) (t17);
let' t15 ← «$tmp»;
let' ret ← ((t15) ≠ᵇ ((0 : nat)));
return (ret)
end


definition FixedBitSet.insert.FILE_LINE : sem (string × u32) :=
let' ret ← ((("thys/fixedbitset/src/src/lib.rs"), ((87 : nat))));
return (ret)


definition FixedBitSet.insert (selfₐ : (FixedBitSet)) (bitₐ : usize) : sem (unit × (FixedBitSet)) :=
let' self ← lens.id;
let' bit ← (bitₐ);
let' t8 ← (bit);
do «$tmp0» ← do «$tmp0» ← lens.get (self) (selfₐ);
return ((FixedBitSet.length «$tmp0»));
let' t9 ← «$tmp0»;
let' t7 ← ((t8) <ᵇ (t9));
let' t6 ← (bool.bnot (t7));
if (t6) = bool.tt then
let' t12 ← (FixedBitSet.insert.FILE_LINE);
let' t11 ← (t12);
mzero
else
let' t5 ← (⋆);
let' t16 ← (bit);
do «$tmp1» ← BITS;
dostep «$tmp» ← @div_rem (t16) «$tmp1»;
let' t15 ← «$tmp»;
let' block ← ((t15).1);
let' i ← ((t15).2);
let' t18 ← (i);
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.shl u32.bits ((1 : nat)) (t18));
let' t19 ← «$tmp0»;
let' t17 ← ((t19).1);
let' t23 ← (self ∘ₗ lens.mk (return ∘ FixedBitSet.data) (λ (o : FixedBitSet) i, return ⦃ FixedBitSet, data := i, o ⦄));
do «$tmp0» ← lens.get (t23) (selfₐ);
dostep «$tmp» ← @collections.«collections.vec.Vec<T> as core.ops.DerefMut».deref_mut _ «$tmp0»;
match «$tmp» with («t22$», «t23$») :=
do (selfₐ) ← lens.set (t23) (selfₐ) «t23$»;
let' t22 ← (t23 ∘ₗ «t22$»);
let' t21 ← (t22);
let' t24 ← (block);
do «$tmp0» ← lens.get (t21) (selfₐ);
dostep «$tmp» ← @collections.«[T]».get_unchecked_mut _ «$tmp0» (t24);
match «$tmp» with («t20$», «t21$») :=
do (selfₐ) ← lens.set (t21) (selfₐ) «t21$»;
let' t20 ← (t21 ∘ₗ «t20$»);
do «$tmp0» ← do «$tmp0» ← lens.get (t20) (selfₐ);
return (bitor u32.bits «$tmp0» (t17));
do (selfₐ) ← lens.set (t20) (selfₐ) «$tmp0»;
let' ret ← (⋆);
return (ret, selfₐ)
end
end


end fixedbitset