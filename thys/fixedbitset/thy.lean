import collections.thy
import fixedbitset.generated

open eq.ops
open nat
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
(length_eq : nat.div_ceil (length self) 32 = list.length (Vec.buf (data self)))

lemma div_rem_32 (n : usize) : div_rem n 32 = some (n / 32, n % 32, 0) := rfl

attribute core.u32_as_Copy' [constructor]
attribute core.marker.Copy'._trans_of_to_Copy [unfold 2]

lemma with_capacity_inv (bits : usize) [is_usize bits] :
  sem.terminates_with FixedBitSet' (with_capacity bits) :=
obtain v k Hfrom_elem Hv, from
  sem.terminates_with_eq (from_elem_Copy_eq (0 : nat) (nat.div_ceil bits 32)),
begin
  rewrite [↑nat.div_ceil at Hfrom_elem],
  rewrite [↑with_capacity, ↑BITS, div_rem_32, ↑bool_to_unsigned],
  krewrite [if_congr (bool.of_Prop_eq_tt_iff (0 < bits % 32)) rfl rfl],
  have is_usize (bits / 32 + ite (0 < bits % 32) 1 0), from is_bounded_nat_of_le_max $
    have bits / 32 ≤ usize.max - 1, from
      nat.div_le_of_le_mul (le.trans (le_pred_of_lt `is_usize bits`) (calc
        usize.max ≤ usize.max + (usize.max - 1 - 1) : le_add_right
              ... = (usize.max - 1) + (usize.max - 1) : by
                rewrite [-nat.add_sub_assoc (show usize.max - 1 ≥ 1, from
                    nat.le_sub_of_add_le (le.trans dec_trivial usize.max_ge_u16_max)),
                  add.comm, nat.add_sub_assoc usize.max_ge_1]
              ... = (usize.max - 1) * 2    : by rewrite [mul.comm, two_mul]
              ... ≤ (usize.max - 1) * 32 : nat.mul_le_mul !le.refl dec_trivial
    )),
    calc bits / 32 + ite (0 < bits % 32) 1 0
          ≤ usize.max - 1 + 1 : add_le_add this
            (ite_prop (λ h, dec_trivial) (λ h, dec_trivial))
      ... = usize.max : nat.sub_add_cancel usize.max_ge_1,
  rewrite [if_pos this, ▸*],
  krewrite [Hfrom_elem],
  split,
  rewrite [▸*, Hv, list.length_replicate],
end

variables (s : FixedBitSet) (bit : usize)
premises [FixedBitSet' s] (Hbit_lt : bit < length s)
include Hbit_lt

lemma bit_div_32_lt_data_length : bit / 32 < list.length (Vec.buf (data s)) :=
calc bit / 32 < nat.div_ceil (length s) 32 :
begin
  cases decidable_lt 0 (length s % 32) with Hrem Hnotrem,
  { exact calc bit / 32 ≤ length s / 32 : nat.div_le_div _ (le_of_lt Hbit_lt)
                      ... < nat.div_ceil (length s) 32 : begin
      apply nat.lt_add_of_pos_right,
      krewrite [if_pos Hrem],
      apply nat.zero_lt_succ,
    end
  },
  { have length s % 32 = 0, from nat.eq_zero_of_le_zero (le_of_not_gt Hnotrem),
    have 32 ∣ length s, from nat.dvd_of_mod_eq_zero this,
    apply nat.div_lt_of_lt_mul,
    rewrite [↑nat.div_ceil],
    krewrite [nat.right_distrib, nat.div_mul_cancel this],
    apply nat.le_add_of_le_right `bit < length s` }
end
  ... = list.length (Vec.buf (data s)) : FixedBitSet'.length_eq s

lemma contains.spec : sem.terminates_with (λ res,
    option.any (λ b : u32, res = (b &&[32] 2 ^ (bit % 32) ≠ᵇ 0))
      (list.nth (Vec.buf (FixedBitSet.data s)) (bit / 32))
  ) (contains s bit) :=
begin
  intro,
  rewrite [↑contains],
  
  rewrite [↑div_rem, ↑BITS,
    +if_pos (show 32 ≠ (0 : nat), from !nat.succ_ne_zero)],
  rewrite [↑«collections.vec.Vec<T> as core.ops.Deref».deref, ↑«[T]».get,
    ↑«[T] as core.slice.SliceExt».get],
  rewrite [checked.shl_1 (show bit % 32 < u32.bits, from !nat.mod_lt dec_trivial)],
  rewrite [+incr_incr],
  note H := bit_div_32_lt_data_length s bit Hbit_lt,
  krewrite [@if_congr _ _ _ _ !nat.decidable_lt _ _ _ _ (@bool.of_Prop_eq_tt_iff (bit / 32 < list.length (Vec.buf (FixedBitSet.data s))) !nat.decidable_lt) rfl rfl],
  krewrite [if_pos' H],
  rewrite [↑«[T] as core.slice.SliceExt».get_unchecked],
  cases list.nth_eq_some H with b b_eq,
  rewrite [b_eq, ▸*],
  rewrite [▸*, ↑«&'a u32 as core.ops.BitAnd<u32>».bitand, ↑«u32 as core.ops.BitAnd».bitand],
end

section
  omit Hbit_lt
  definition to_set : set usize :=
  {bit | ∃ (h : bit < length s), sem.unwrap (contains.spec s bit h) = bool.tt}
end

lemma insert.spec :
  sem.terminates_with (λ ret,
    let s' := ret.2 in
    ∃ (h : FixedBitSet' s'), to_set s' = to_set s ∪ '{bit})
  (insert s bit) :=
have is_bounded_nat 32 (2^(bit % 32)), from
  strictly_increasing_pow dec_trivial (!mod_lt dec_trivial),
begin
  intro, rewrite [↑insert],
  have bool.bnot (bit <ᵇ FixedBitSet.length s) = bool.tt ↔ ¬(bit < length s),
  by rewrite [!bool.bnot_of_Prop, bool.of_Prop_eq_tt_iff],
  rewrite [if_congr this rfl rfl, if_neg (not_not_intro `bit < length s`), ▸*],
  have 32 ≠ (0 : nat), from !nat.succ_ne_zero,
  rewrite [↑div_rem, ↑BITS, +if_pos' this],
  rewrite [↑«collections.vec.Vec<T> as core.ops.DerefMut».deref_mut, ↑«[T]».get_unchecked_mut],
  rewrite [checked.shl_1 (show bit % 32 < u32.bits, from !nat.mod_lt dec_trivial)],
  note bit_valid := bit_div_32_lt_data_length s bit Hbit_lt,
  cases list.nth_eq_some bit_valid with b b_eq,
  rewrite [b_eq, ▸*],
  cases list.update_eq_some _ bit_valid with l' l'_eq,
  let s' := FixedBitSet.mk (Vec.mk l') (FixedBitSet.length s),
  rewrite [l'_eq, ▸*],
  have FixedBitSet' s', begin
    split,
    rewrite [▸*, FixedBitSet'.length_eq s, list.length_update l'_eq],
  end,
  existsi this,
  rewrite [↑to_set],
  apply set.ext, intro bit',
  rewrite [▸*, set.mem_union_eq],
  cases decidable_lt bit' (length s) with bit'_lt bit'_ge,
  { rewrite [+set.mem_set_of_iff, set.mem_singleton_iff, +exists_true_Prop_iff `bit' < length s`],

    note H := sem.sem_unwrap (contains.spec s' bit' bit'_lt),
    esimp at H,
    note Hbit'_valid := bit_div_32_lt_data_length s bit' bit'_lt,
    cases list.nth_eq_some ((list.length_update l'_eq)⁻¹ ▸ Hbit'_valid) with b' b'_eq,
    rewrite [b'_eq at H{2}, ▸* at H, H],
    clear H,

    note H := sem.sem_unwrap (contains.spec s bit' bit'_lt),
    cases list.nth_eq_some Hbit'_valid with b'' b''_eq,
    rewrite [b''_eq at H{2}, ▸* at H, H],
    clear H,

    note H := list.nth_update (bit' / 32) l'_eq,
    rewrite [b''_eq at H, b'_eq at H],
    clear b'_eq,

    cases (_ : decidable (bit / 32 = bit' / 32)) with same_blk dif_blk,
    { rewrite [if_pos same_blk at H],
      injection H with H,
      have b'' = b, from
        have some b'' = some b, by rewrite [-b_eq, -b''_eq, same_blk],
        option.no_confusion this id,
      rewrite [this, H],
      cases (_ : decidable (bit' = bit)),
      { rewrite [`bit' = bit`, +bool.of_Prop_eq_tt_iff, eq_self_iff_true, or_true,
          iff_true],
        rewrite [bitand_bitor_cancel],
        apply not_imp_not_of_imp eq_zero_of_pow_eq_zero,
        contradiction
      },
      { have bit % 32 ≠ bit' % 32, begin
          revert a, apply not_imp_not_of_imp, intro h,
          rewrite [eq_div_mul_add_mod bit 32, eq_div_mul_add_mod bit' 32, h, same_blk],
        end,
        rewrite [iff_false_intro `bit' ≠ bit`, +bool.of_Prop_eq_tt_iff, bitand_bitor_distrib_right,
          !bitand_disj_pow this, bitor_zero],
        apply iff.symm !or_false
      }
    },
    { rewrite [if_neg dif_blk at H],
      injection H with H,
      rewrite H,
      have bit' ≠ bit, by intro contr; rewrite [contr at dif_blk]; apply dif_blk rfl,
      rewrite [iff_false_intro this, or_false] }
  },
  { rewrite [+set.mem_set_of_iff, set.mem_singleton_iff,
      +iff_false_intro (not_exists_of_not _ bit'_ge), false_iff, false_or],
    show bit' ≠ bit, from take contr, bit'_ge (contr⁻¹ ▸ Hbit_lt) }
end

end fixedbitset.FixedBitSet

