import collections.thy
import fixedbitset.generated

open eq.ops
open [class] [unfold] nat
open prod.ops
open option
open [notation] set

open core
open collections
open collections.vec
open fixedbitset

namespace fixedbitset.FixedBitSet

eval
  do s ← with_capacity 10;
  do r ← insert s 2;
  contains r.2 2

attribute bool.bnot [unfold 1]

attribute sem [reducible]

structure FixedBitSet' [class] (self : FixedBitSet) : Prop :=
(length_eq : nat.div_ceil (length self) BITS = list.length (Vec.buf (data self)))

lemma div_rem_BITS (n : usize) : div_rem n BITS = some (n / BITS, n % BITS, 0) := rfl

attribute core.u32_as_Copy' [constructor]
attribute core.marker.Copy'._trans_of_to_Copy [unfold 2]

lemma with_capacity_inv (bits : usize) : sem.terminates_with FixedBitSet' (with_capacity bits) :=
obtain v k Hfrom_elem Hv, from
  sem.terminates_with_eq (from_elem_Copy_eq (0 : nat) (nat.div_ceil bits BITS)),
begin
  rewrite [↑nat.div_ceil at Hfrom_elem],
  rewrite [↑with_capacity, div_rem_BITS, ↑bool_to_usize],
  krewrite [if_congr (bool.of_Prop_eq_tt_iff (0 < bits % BITS)) rfl rfl],
  krewrite [Hfrom_elem],
  split,
  rewrite [▸*, Hv, list.length_replicate],
end

lemma contains.term (s : FixedBitSet) [FFF : FixedBitSet' s] (bit : usize) : bit < length s →
  sem.terminates (contains s bit) :=
begin
  intro,
  rewrite [↑contains],
  have BITS ≠ (0 : nat), from !nat.succ_ne_zero,
  rewrite [↑div_rem, ↑checked.div, ↑checked.mod, +if_pos' this, ↑checked.shl],
  rewrite [↑«collections.vec.Vec<T> as core.ops.Deref».deref, ↑«[T]».get,
    ↑«[T] as core.slice.SliceExt».get],
  rewrite [+incr_incr],
  have bit / BITS < nat.div_ceil (length s) BITS,
  begin
    cases decidable_lt 0 (length s % BITS) with Hrem Hnotrem,
    { exact calc bit / BITS ≤ length s / BITS : nat.div_le_div _ (le_of_lt `bit < length s`)
                        ... < nat.div_ceil (length s) BITS : begin
        apply nat.lt_add_of_pos_right,
        rewrite [decidable_eq_inl Hrem !nat.decidable_lt],
        apply nat.zero_lt_succ,
      end
    },
    { have length s % BITS = 0, from nat.eq_zero_of_le_zero (le_of_not_gt Hnotrem),
      have BITS ∣ length s, from nat.dvd_of_mod_eq_zero this,
      apply nat.div_lt_of_lt_mul,
      rewrite [↑nat.div_ceil],
      krewrite [nat.right_distrib, nat.div_mul_cancel this],
      apply nat.le_add_of_le_right `bit < length s` }
  end,
  rewrite [decidable_eq_inl (FixedBitSet'.length_eq s ▸ this) !nat.decidable_lt, ▸*],
  rewrite [↑«[T] as core.slice.SliceExt».get_unchecked],
  cases list.nth_eq_some (FixedBitSet'.length_eq s ▸ this) with b b_eq,
  rewrite [b_eq, ▸*],
  rewrite [↑«&'a u32 as core.ops.BitAnd<u32>».bitand, ↑«u32 as core.ops.BitAnd».bitand],
  contradiction
end

definition to_set (s : FixedBitSet) [FixedBitSet' s] : set usize :=
{bit | @when (bit < length s) !nat.decidable_lt
  (λ H, sem.unwrap (contains.term s bit H) = bool.tt)
}

open [class] classical

lemma insert.sem (s : FixedBitSet) [FFF : FixedBitSet' s] (bit : usize) : bit < length s →
  sem.terminates_with (λ ret,
    let s' := ret.2 in
    when (FixedBitSet' s') (λ H, to_set s' = to_set s ∪ '{bit}))
  (insert s bit) :=
begin
  intro,
  rewrite [↑insert, decidable_eq_inl `bit < length s` !nat.decidable_lt, ▸*],
  have BITS ≠ (0 : nat), from !nat.succ_ne_zero,
  rewrite [↑div_rem, ↑checked.div, ↑checked.mod, +if_pos' this, ↑checked.shl],
  rewrite [↑«collections.vec.Vec<T> as core.ops.DerefMut».deref_mut, ↑«[T]».get_unchecked_mut],
  rewrite [+incr_incr],
  have bit / BITS < nat.div_ceil (length s) BITS,
  begin
    cases decidable_lt 0 (length s % BITS) with Hrem Hnotrem,
    { exact calc bit / BITS ≤ length s / BITS : nat.div_le_div _ (le_of_lt `bit < length s`)
                        ... < nat.div_ceil (length s) BITS : begin
        apply nat.lt_add_of_pos_right,
        rewrite [decidable_eq_inl Hrem !nat.decidable_lt],
        apply nat.zero_lt_succ,
      end
    },
    { have length s % BITS = 0, from nat.eq_zero_of_le_zero (le_of_not_gt Hnotrem),
      have BITS ∣ length s, from nat.dvd_of_mod_eq_zero this,
      apply nat.div_lt_of_lt_mul,
      rewrite [↑nat.div_ceil],
      krewrite [nat.right_distrib, nat.div_mul_cancel this],
      apply nat.le_add_of_le_right `bit < length s` }
  end,
  cases list.nth_eq_some (FixedBitSet'.length_eq s ▸ this) with b b_eq,
  rewrite [b_eq, ▸*],
  cases list.update_eq_some _ (FixedBitSet'.length_eq s ▸ this) with l' l'_eq,
  rewrite [l'_eq, ▸*],
  have FixedBitSet' (FixedBitSet.mk (Vec.mk l') (FixedBitSet.length s)), from sorry,
  rewrite [↑when, dif_pos this, ↑to_set],
  apply set.ext, intro bit',
  rewrite [↑when, ▸*, set.mem_union_eq],
  cases decidable_lt bit' (length s),
  { rewrite [+set.mem_set_of_iff, decidable_eq_inl a_1 !nat.decidable_lt, ▸*] }
end

end fixedbitset.FixedBitSet

