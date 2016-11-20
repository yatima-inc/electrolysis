import core.generated

import algebra.interval
import data.finset
import data.list.sorted

import asymptotic

open bool (tt ff)
open [class] classical
open core
open eq.ops
open list
open list.prefixeq
open [class] [reducible] int
open nat
open interval
open option
open partial
open prod.ops
open set
open topology

open asymptotic

-- doesn't seem to get picked up by class inference
definition inv_image.wf' [trans_instance] {A : Type} {B : Type} {R : B → B → Prop} {f : A → B}
  [well_founded R] : well_founded (inv_image R f) := inv_image.wf f _

attribute sem [reducible]

lemma bitvec.of_is_bounded_nat [instance] (bits : ℕ) (v : bitvec bits) :
  is_bounded_nat bits (bitvec.to ℕ v) :=
!bitvec.to_lt

lemma zero_is_bounded_nat [instance] (bits : ℕ) : is_bounded_nat bits 0 :=
!pow_pos_of_pos dec_trivial

lemma div_is_bounded_nat [instance] (bits x y : ℕ) [h : is_bounded_nat bits x] :
  is_bounded_nat bits (x / y) :=
lt_of_le_of_lt !nat.div_le_self h

lemma mod_is_bounded_nat [instance] (bits x y : ℕ) [h : is_bounded_nat bits x] :
  is_bounded_nat bits (x % y) :=
lt_of_le_of_lt !nat.mod_le h

lemma unsigned.max_is_bounded_nat [instance] (bits : ℕ) : is_bounded_nat bits (unsigned.max bits) :=
begin
  rewrite [↑is_bounded_nat, ↑unsigned.max],
  apply generalize_with_eq (2^bits:ℕ), intro x hx, cases x,
  { exfalso, apply dec_trivial (eq_zero_of_pow_eq_zero hx) },
  { apply lt_succ_self }
end

lemma is_bounded_nat_of_le_max {bits x : ℕ} (h : x ≤ unsigned.max bits) : is_bounded_nat bits x :=
lt_of_le_of_lt h !unsigned.max_is_bounded_nat

lemma usize.max_ge_u16_max : usize.max ≥ u16.max :=
begin
  xrewrite [+sub_one],
  apply pred_le_pred,
  apply nondecreasing_pow (show (2:ℕ) ≥ 1, from dec_trivial) usize.bits_ge_16
end

lemma usize.max_ge_1 : usize.max ≥ 1 := le.trans dec_trivial usize.max_ge_u16_max

lemma length_is_usize_of_is_slice [instance] {T : Type₁} (xs : list T) [is_slice xs] :
  is_usize (length xs) :=
le.trans `is_slice xs` (nondecreasing_pow dec_trivial !sub_le)

section bitwise
open bitvec
open bool
open tuple

lemma bitand_bitor_distrib_right (bits x y z : ℕ) :
  (x ||[bits] y) &&[bits] z = (x &&[bits] z) ||[bits] (y &&[bits] z) :=
by rewrite [↑bitor, ↑bitand, +bitvec.of_to, bitvec.and_or_distrib_right]

lemma bitand_self (bits x : ℕ) [h : is_bounded_nat bits x] : bitand bits x x = x :=
by rewrite [↑bitand, bitvec.and_self, bitvec.to_of h]

lemma bitand.comm (bits x y : ℕ) : bitand bits x y = bitand bits y x :=
by rewrite [↑bitand, bitvec.and.comm]

lemma bitand_bitor_cancel (bits x y : ℕ) [h : is_bounded_nat bits y] :
  bitand bits (bitor bits x y) y = y :=
by rewrite [↑bitor, ↑bitand, +bitvec.of_to, bitvec.and_or_cancel, bitvec.to_of h]

lemma bitand_disj_pow_aux : Π(bits : ℕ) {x y : ℕ}, x < y → bitand bits (2^x) (2^y) = 0
| 0 x y h := rfl
| (succ n) 0 (succ y) h := begin
  krewrite [↑bitand, ↑bitvec.of, ↑bitvec.and, tuple.map₂_snoc],
  rewrite [pow_zero, if_pos (show (1:ℕ) % 2 = 1, from dec_trivial),
    pow_succ, !nat.mul_div_cancel_left (show 2 > 0, from dec_trivial),
    mul_mod_eq_mod_mul_mod, mod_self, zero_mul, if_neg (show (0:ℕ) % 2 ≠ 1, from dec_trivial),
    band_ff, (show (1:ℕ) / 2 = 0, from dec_trivial), ↑bitvec.to],
  krewrite [to_list_append, ▸*],
  rewrite [bitsTo_snoc, ↑cond, bitvec.and.comm, bitvec.of_zero, bitvec.and_zero, ↑bitvec.zero,
    bitsTo_replicate_ff]
end
| (succ n) (succ x) 0 h := false.elim (not_le_of_gt h !zero_le)
| (succ n) (succ x) (succ y) h := begin
  krewrite [↑bitand, ↑bitvec.of, ↑bitvec.and, tuple.map₂_snoc],
  rewrite [+pow_succ, +!nat.mul_div_cancel_left (show 2 > 0, from dec_trivial),
    mul_mod_eq_mod_mul_mod, mul_mod_eq_mod_mul_mod 2, mod_self, +zero_mul,
    if_neg (show (0:ℕ) % 2 ≠ 1, from dec_trivial),
    band_ff, ↑bitvec.to],
  krewrite [to_list_append, ▸*],
  rewrite [bitsTo_snoc, ↑cond], xrewrite [!bitand_disj_pow_aux (lt_of_succ_lt_succ h)]
end

lemma bitand_disj_pow (bits : ℕ) {x y : ℕ} (h : x ≠ y) : bitand bits (2^x) (2^y) = 0 :=
begin
  cases lt_or_gt_of_ne h,
  { apply bitand_disj_pow_aux bits `x < y` },
  { rewrite [bitand.comm, bitand_disj_pow_aux bits `x > y`] }
end

lemma bitor_zero (bits x : ℕ) [h : is_bounded_nat bits x] : bitor bits x 0 = x :=
begin
  rewrite [↑bitor, bitvec.of_zero, bitvec.or_zero, bitvec.to_of h]
end

attribute list.append [unfold 2 3]

lemma checked.shl_1 {bits : ℕ} {y : u32} (h : y < bits) : checked.shl bits 1 y = return (2^y) :=
begin
  cases bits with bits,
  { exfalso, apply !not_lt_zero h },
  { rewrite [if_pos h, ↑shl, of_one, ↑bitvec.to, list.dropn_append
      (show length (replicate bits ff) ≥ y, by rewrite [length_replicate]; apply le_of_lt_succ h),
      list.dropn_replicate, append.assoc, bitsTo_append, append_cons, ↑list.append,
      bitsTo_cons, +bitsTo_replicate_ff,
      length_replicate, min_eq_right (le_of_lt h)],
    simp }
end

end bitwise

namespace core

open clone
open marker

namespace marker
  structure Copy' [class] (T : Type₁) extends Copy T :=
  (perfect : ∀(self : T), sem.terminates_with (λ c, c = self) (Clone.clone self))
end marker

open marker

attribute Copy.to_Clone [unfold 2]
attribute «u32 as core.clone.Clone» [constructor]

definition u32_as_Copy' [instance] : Copy' u32 :=
marker.Copy'.mk Clone.clone begin
  intro self,
  rewrite [▸*, ↑«u32 as core.clone.Clone».clone]
end

namespace cmp
  definition ordering {T : Type} [decidable_linear_order T] (x y : T) : cmp.Ordering :=
  if x < y then Ordering.Less
  else if x = y then Ordering.Equal
  else Ordering.Greater

  structure Ord' [class] (T : Type₁) extends Ord T, decidable_linear_order T :=
  (cmp_eq : ∀x y : T, Σk, cmp x y = some (ordering x y, k))

  namespace Ord'
  section
    parameters {T : Type₁} [Ord' T]

    lemma ord_cmp_eq (x y : T) : Σk, Ord.cmp x y = some (ordering x y, k) := cmp_eq x y -- HACK

    open finset
    open prod

    definition cmp_max_cost (y : T) (xs : list T) := Max x ∈ to_finset xs, sigma.pr1 (cmp_eq x y)

    lemma le_cmp_max_cost {xs : list T} {x y : T} (Hx : x ∈ xs) {ord k} (H : cmp x y = some (ord, k)) :
      k ≤ cmp_max_cost y xs :=
    have sigma.pr1 (cmp_eq x y) ≤ cmp_max_cost y xs, from finset.le_Max _ (mem_to_finset Hx),
    begin
      revert this,
      cases cmp_eq x y with k' Hcmp_eq,
      injection H⁻¹ ⬝ Hcmp_eq with _ Hkk',
      esimp, rewrite -Hkk', apply id
    end
  end
  end Ord'
end cmp

open cmp
open ops
open result

namespace slice

/- The SliceExt trait declares all methods on slices. It has a single implementation
   for [T] -/
open «[T] as core.slice.SliceExt»

section

parameter {T : Type₁}
variable (s : slice T)

lemma is_empty_eq [decidable_eq T] : SliceExt.is_empty T s = some (s =ᵇ [], 1) :=
begin
  apply congr_arg some,
  apply prod.eq,
  { esimp,
    apply bool.of_Prop_eq_of_Prop_of_iff,
    exact iff.intro
      eq_nil_of_length_eq_zero
      (λHeq, Heq⁻¹ ▸ length_nil)
  },
  apply rfl,
end

-- s[start..]
lemma RangeFrom_index_eq (r : RangeFrom usize) (H : RangeFrom.start r ≤ length s) :
  «[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index s r = some (dropn (RangeFrom.start r) s, 2) :=
begin
  let st := RangeFrom.start r,
  have st ≤ length s ∧ length s ≤ length s, from and.intro H (le.refl _),
  rewrite [↑«[T] as core.ops.Index<core.ops.RangeFrom<usize>>».index, ↑«[T] as core.ops.Index<core.ops.Range<usize>>».index,
    return_bind, if_pos' this],
  have firstn (length s - st) (dropn st s) = dropn st s, from
    firstn_all_of_ge (length_dropn st s ▸ le.refl _),
  rewrite this,
end

-- s[..end]
lemma RangeTo_index_eq (r : RangeTo usize) (H : RangeTo.«end» r ≤ length s) :
  «[T] as core.ops.Index<core.ops.RangeTo<usize>>».index s r = some (firstn (RangeTo.«end» r) s, 1) :=
begin
  let e := RangeTo.«end» r,
  have 0 ≤ e ∧ e ≤ length s, by simp,
  rewrite [↑«[T] as core.ops.Index<core.ops.RangeTo<usize>>».index, ↑«[T] as core.ops.Index<core.ops.Range<usize>>».index,
    if_pos' this],
end

/- fn split_at(&self, mid: usize) -> (&[T], &[T])

Divides one slice into two at an index.

The first will contain all indices from [0, mid) (excluding the index mid itself) and the second will contain all indices from [mid, len) (excluding the index len itself).

Panics if mid > len.
-/
lemma split_at_eq {mid : usize} (H : mid ≤ length s) :
  split_at s mid = some ((firstn mid s, dropn mid s), 5) :=
by rewrite [↑split_at, !RangeTo_index_eq H, !RangeFrom_index_eq H]

end

section binary_search
open «[T] as core.slice.SliceExt».binary_search_by
open «[T] as core.slice.SliceExt».binary_search
attribute closure_5594.inst [constructor]

parameter {T : Type₁}
parameter [Ord' T]

-- use separate section for everything but the main theorem
section

parameter self : slice T
parameter needle : T

hypothesis Hsorted : sorted le self
hypothesis His_slice : is_slice self

abbreviation f := closure_5594.mk needle
abbreviation cmp_max_cost := Ord'.cmp_max_cost needle self

/- fn binary_search(&self, x: &T) -> Result<usize, usize> where T: Ord

Binary search a sorted slice for a given element.

If the value is found then Ok is returned, containing the index of the matching element;
if the value is not found then Err is returned, containing the index where a matching element could
be inserted while maintaining sorted order.-/
inductive binary_search_res : Result usize usize → Prop :=
| found     : Πi, nth self i = some needle → binary_search_res (Result.Ok i)
| not_found : Πi, needle ∉ self → sorted le (insert_at self i needle) →
  binary_search_res (Result.Err i)

section loop_4

variable s : slice T
variable base : usize

private abbreviation loop_4.state := closure_5594 T × usize × slice T

include self needle base s -- HACK
structure loop_4_invar : Prop :=
(s_in_self  : s ⊑ₚ (dropn base self))
(insert_pos : sorted.insert_pos self needle ∈ '[base, base + length s])
(needle_mem : needle ∈ self → needle ∈ s)
omit self needle base s

inductive loop_4_step : loop_4.state → Prop :=
mk : Πbase' s', loop_4_invar s' base' → length s' ≤ length s / 2 → length s ≠ 0 →
  loop_4_step (f, base', s')

abbreviation loop_4_res := sum.rec (loop_4_step s) binary_search_res

-- extract some more expensive parts of the proof
section
  variables {x : T} {xs : list T}
  variables (Hinvar : loop_4_invar s base) (Hs : dropn (length s / 2) s = x :: xs)

  include Hs
  lemma aux1 : sorted.insert_pos self needle ≤
    base + (length (firstn (length s / 2) s) + 1) + length (dropn 1 (x::xs)) :=
  let s₁ := firstn (length s / 2) s in
  let s₂ := dropn (length s / 2) s in
  have 1 ≤ length (x :: xs), from succ_le_succ !zero_le,
  calc sorted.insert_pos self needle
    ≤ base + length s : and.right (loop_4_invar.insert_pos Hinvar)
    ... = base + (length s₁ + length s₂) : by rewrite [-length_append, firstn_app_dropn_eq_self]
    ... = base + (length s₁ + (length (dropn 1 (x::xs)) + 1)) : by
      rewrite [Hs, length_dropn, nat.sub_add_cancel this]
    ... = base + (length s₁ + 1) + length (dropn 1 (x::xs)) : by simp
end

include His_slice
private lemma loop_4.spec (Hinvar : loop_4_invar s base) : sem.terminates_with_in
  (loop_4_res s)
  (cmp_max_cost + 15)
  (loop_4 (f, base, s)) :=
have sorted_s : sorted le s, from sorted.sorted_of_prefix_of_sorted
  (loop_4_invar.s_in_self Hinvar)
  (sorted.sorted_dropn_of_sorted Hsorted _),
generalize_with_eq (loop_4 (f, base, s)) (begin
  intro res,
  rewrite [↑loop_4,
    if_pos (show 0 ≤ (1:ℤ), from dec_trivial),
    if_pos (show usize.bits > nat.of_int 1, from lt_of_lt_of_le dec_trivial usize.bits_ge_16)],
  krewrite [pow_one],
  have length s / 2 ≤ length s, from !nat.div_le_self,
  rewrite [▸*, split_at_eq s this, ▸*, is_empty_eq, ▸*],
  let s₁ := firstn (length s / 2) s,
  let s₂ := dropn (length s / 2) s,
  have len_s₁ : length s₁ = length s / 2, by
    rewrite [length_firstn_eq, min_eq_left this],
  eapply generalize_with_eq (dropn (length s / 2) s),
  intro s' Hs, cases s' with x xs,
  { intro H, rewrite -H, clear H,
    have Hs : s = nil, begin
      have 0 = length s - length s / 2, from Hs ▸ !length_dropn,
      apply classical.by_contradiction, intro Hs_not_nil,
      apply lt.irrefl (length s / 2) (calc
        length s / 2 < length s     : div_lt_of_ne_zero (take Hcontr, Hs_not_nil (eq_nil_of_length_eq_zero Hcontr))
                 ... = (length s - length s / 2) + length s / 2 : (nat.sub_add_cancel !nat.div_le_self)⁻¹
                 ... = 0 + length s / 2 : { this⁻¹ }
                 ... = length s / 2 : !zero_add
      )
    end,
    have base = sorted.insert_pos self needle, begin
      note H := loop_4_invar.insert_pos Hinvar,
      rewrite [Hs at H, length_nil at H, add_zero at H, Icc_self at H],
      apply (eq_of_mem_singleton H)⁻¹
    end,
    rewrite this,
    esimp,
    apply sem.terminates_with_in.mk rfl,
    { esimp, right,
      { show needle ∉ self, from
        take Hneedle,
        have needle ∈ s, from loop_4_invar.needle_mem Hinvar Hneedle,
        Hs ▸ this },
      { apply sorted.sorted_insert_at_insert_pos Hsorted }
    },
    { apply le_add_of_le_left, apply dec_trivial }
  },
  { have length s ≠ 0,
    begin
      intro H,
      rewrite (eq_nil_of_length_eq_zero H) at Hs,
      contradiction
    end,
    have Hwf : length xs ≤ length s / 2, from
      calc length xs = length (x :: xs) - 1 : rfl
                 ... ≤ length s / 2         : by
                   rewrite [-Hs, length_dropn]; apply self_sub_half_sub_one_le_half,
    rewrite [▸*, ↑get_unchecked, nth_zero, ↑f],
    --obtain k `k ≤ Ord'.max_cost T` cmp_eq, from Ord'.ord_cmp_eq x needle, -- slow
    cases Ord'.ord_cmp_eq x needle with k cmp_eq,
    rewrite [+incr_incr, ↑closure_5594.fn, cmp_eq, ↑ordering, ▸*],
    have nth_x : nth self (base + length s₁) = some x,
    begin
      have nth s (length s / 2) = some x, by rewrite [nth_eq_first'_dropn, Hs, ▸*, nth_zero],
      rewrite [nth_eq_first'_dropn, add.comm, -dropn_dropn, -nth_eq_first'_dropn, len_s₁],
      apply prefixeq.nth_of_nth_prefixeq this (loop_4_invar.s_in_self Hinvar)
    end,
    have is_usize (base + (length s₁ + 1)), from
      lt_of_le_of_lt (lt_length_of_nth nth_x) (length_is_usize_of_is_slice self),
    rewrite [if_pos (lt_of_le_of_lt !le_add_left this), ▸*, if_pos this, ▸*],
    rewrite [if_pos (show is_usize (base + length s₁), from
      lt_of_le_of_lt (add_le_add_left !le_add_right _) this)],
    have Hle_max_cost : k ≤ cmp_max_cost, from
      Ord'.le_cmp_max_cost (mem_of_nth nth_x) cmp_eq,
    cases (decidable_lt x needle) with Hx_lt_needle Hx_ge_needle,
    { have 1 ≤ length (x :: xs), from succ_le_succ !zero_le,
      rewrite [RangeFrom_index_eq _ (RangeFrom.mk _) this, ▸*],
      intro H, rewrite -H,
      apply sem.terminates_with_in.mk rfl,
      { esimp, split,
        exact ⦃loop_4_invar,
          s_in_self := begin
            rewrite [-Hs, dropn_dropn, len_s₁, add.comm at {1}, {base + _}add.comm, -{dropn _ self}dropn_dropn],
            apply !dropn_prefixeq_dropn_of_prefixeq (loop_4_invar.s_in_self Hinvar),
          end,
          insert_pos := begin
            note H := loop_4_invar.insert_pos Hinvar,
            split,
            { have sorted.insert_pos self needle > base + length s₁, from
                sorted.insert_pos_gt Hsorted Hx_lt_needle nth_x,
              apply succ_le_of_lt this
            },
            exact aux1 s base Hinvar Hs
          end,
          needle_mem := assume Hneedle : needle ∈ self,
            have needle ∈ s₁ ++ s₂, by rewrite [firstn_app_dropn_eq_self]; apply loop_4_invar.needle_mem Hinvar Hneedle,
            or.rec_on (mem_or_mem_of_mem_append this)
              (suppose needle ∈ s₁,
                have x ≥ needle, from
                  obtain i Hi, from nth_of_mem this,
                  show needle ≤ x, from sorted.le_of_nth_le_nth sorted_s
                    (show nth s i = some needle, from prefixeq.nth_of_nth_prefixeq Hi !firstn_prefixeq)
                    (show nth s (length s / 2) = some x, by rewrite [nth_eq_first'_dropn, Hs])
                    (show i ≤ length s / 2, from le_of_lt (len_s₁ ▸ lt_length_of_mem Hi)),
                false.elim (not_le_of_gt Hx_lt_needle this))
              (suppose needle ∈ s₂,
                show needle ∈ xs, from or.rec_on (eq_or_mem_of_mem_cons (Hs ▸ this))
                  (suppose needle = x, false.elim (lt.irrefl _ (this ▸ Hx_lt_needle)))
                  (suppose needle ∈ xs, this))
        ⦄,
        rewrite [length_dropn, length_cons, ▸*, nat.add_sub_cancel],
        exact Hwf, exact `length s ≠ 0` },
      { repeat (rewrite [{k + _ + _}add.assoc] | rewrite [-{_ + (k + _)}add.assoc] |
                rewrite [{_ + k}add.comm]),
        apply add_le_add_right Hle_max_cost }
    },
    { intro H, subst H,
      cases (has_decidable_eq : decidable (x = needle)) with Hfound Hnot_found,
      { apply sem.terminates_with_in.mk rfl,
        { left, apply Hfound ▸ nth_x },
        { repeat (rewrite [{k + _ + _}add.assoc] | rewrite [-{_ + (k + _)}add.assoc] |
                  rewrite [{_ + k}add.comm]),
          apply add_le_add Hle_max_cost dec_trivial }
      },
      { have Hx_gt_needle : x > needle, from lt_of_le_of_ne (le_of_not_gt Hx_ge_needle) (ne.symm Hnot_found),
        apply sem.terminates_with_in.mk rfl,
        { split,
          exact ⦃loop_4_invar,
            s_in_self := prefixeq.trans !firstn_prefixeq (loop_4_invar.s_in_self Hinvar),
            insert_pos := begin
              split,
              { apply and.left (loop_4_invar.insert_pos Hinvar) },
              { apply sorted.insert_pos_le Hsorted Hx_gt_needle nth_x }
            end,
            needle_mem := assume Hneedle : needle ∈ self,
              have needle ∈ s₁ ++ s₂, by rewrite [firstn_app_dropn_eq_self]; apply loop_4_invar.needle_mem Hinvar Hneedle,
              or.rec_on (mem_or_mem_of_mem_append this)
                (suppose needle ∈ s₁, this)
                (suppose needle ∈ s₂,
                  have x ≤ needle, from sorted.first_le
                    (show sorted le (x::xs), from Hs ▸ sorted.sorted_dropn_of_sorted sorted_s _)
                    (show needle ∈ x::xs, from Hs ▸ this),
                  false.elim (not_le_of_gt Hx_gt_needle this))
          ⦄,
          exact !length_firstn_le,
          exact `length s ≠ 0`
        },
        { repeat (rewrite [{k + _ + _}add.assoc] | rewrite [-{_ + (k + _)}add.assoc] |
                  rewrite [{_ + k}add.comm]),
          apply add_le_add Hle_max_cost dec_trivial }
      }
    }
  }
end)
end loop_4
end

local infix `≼`:25 := asymptotic.le ([at ∞] : filter ℕ)

theorem binary_search_by.spec :
  ∃₀g ∈ 𝓞(λp, log₂ p.1 * p.2) [at ∞ × ∞],
  ∀ needle (st : closure_5594 T × usize × slice T), let self := st.2 in
    st.1.1 = closure_5594.mk needle ∧ st.1.2 = 0 ∧ is_slice self ∧ sorted le self → sem.terminates_with_in
    (binary_search_res self needle)
    (g (length self, Ord'.cmp_max_cost needle self))
    (loop loop_4 st) :=
begin
  apply loop.terminates_with_in_ub
    (λ n, log₂ (2 * n) + 1)
    (λ needle init s, s.1.1 = f needle ∧ loop_4_invar init.2 needle s.2 s.1.2),
  { split,
    calc (λa, log₂ (2 * a) + 1)
        ≼ (λa, log₂ a + 2) : ub_of_eventually_le_at_infty 1 (
          take a, suppose a ≥ 1,
          calc log₂ (2 * a) + 1 = log₂ a + 1 + 1 : { @log.rec 2 dec_trivial _ this }
                            ... ≤ log₂ a + 2     : le_of_eq !add.assoc)
    ... ≼ log₂ : ub_add asymptotic.le.refl (
          calc (λx, 2) ≼ (λx, 1) : ub_const
                   ... ≼ log₂    : asymptotic.le_of_lt (@log_unbounded 2 dec_trivial)),
    show (λa, 1) ≼ (λa, log₂ (2 * a) + 1), from ub_of_eventually_le_at_infty 0 (λ y h, !le_add_left)
  },
  { intro needle st pre,
    split, apply and.left pre,
    cases pre with _ pre,
    cases pre with hbase,
    rewrite hbase,
    let self := st.2,
    show loop_4_invar self needle self 0, from ⦃loop_4_invar,
      s_in_self := !prefixeq.refl,
      insert_pos := and.intro !zero_le (!zero_add⁻¹ ▸ !sorted.insert_pos_le_length),
      needle_mem := id
    ⦄,
  },
  existsi λ n, n + 15,
  split,
  { have id + (λ n, 15) ∈ 𝓞(id) [at ∞] ∩ Ω(λ n, 15) [at ∞], begin
      apply ub_add_const,
      apply and.intro asymptotic.le.refl (ub_of_eventually_le_at_infty 15 (λ y h, h)),
    end,
    exact and.intro (and.left this)
      (asymptotic.le.trans (ub_of_eventually_le_at_infty 0 (λ y h, dec_trivial)) (and.right this))
  },
  intro needle st,
  cases st with st₁ self,
  cases st₁ with f base,
  intro st pre inv,
  cases st with st₁ s,
  cases pre with Hf pre,
  cases pre with _ pre,
  cases pre with Hslice Hsorted,
  cases inv with Hf' Hinv,
  esimp,
  rewrite [-prod.eta, -prod.eta st₁, ▸*, Hf'],
  apply sem.terminates_with_in.imp (!loop_4.spec Hsorted Hslice _ _ Hinv),
  { intro x, cases x with st' r,
    esimp,
    { intro Hstep, cases Hstep with base' s' Hinvar' Hvar Hs_ne_nil,
      esimp,
      split,
      { split, apply rfl, apply Hinvar' },
      calc log₂ (2 * length s') + 1 ≤ log₂ (length s) + 1 : add_le_add_right
        (nondecreasing_log dec_trivial (le.trans (mul_le_mul_left 2 Hvar) (!mul.comm ▸ div_mul_le _ _)))
        _
      ... = log₂ (2 * length s) : by
        rewrite [-@log.rec 2 dec_trivial _ (pos_of_ne_zero `length s ≠ 0`)]
      ... < log₂ (2 * length s) + 1: le.refl,
    },
    apply id,
  },
  esimp
end

theorem binary_search.spec :
  ∃₀f ∈ 𝓞(λp, log₂ p.1 * p.2) [at ∞ × ∞],
  ∀(self : slice T) (needle : T), is_slice self → sorted le self → sem.terminates_with_in
    (binary_search_res self needle)
    (f (length self, Ord'.cmp_max_cost needle self))
    (binary_search self needle) :=
begin
  cases binary_search_by.spec with g spec,
  cases spec with hg spec,
  existsi λ p, g p + 1 * 1,
  split,
  { apply ub_add hg,
    apply ub_mul_prod_filter,
    { apply asymptotic.le_of_lt (@log_unbounded 2 dec_trivial) },
    { apply ub_of_eventually_le (eventually_at_infty_intro (λx Hx, Hx)) },
  },
  { intros,
    rewrite [↑binary_search, ↑binary_search_by, bind_return],
    apply sem.terminates_with_in_incr,
    apply spec needle,
    esimp,
    repeat split,
    repeat (exact rfl | assumption)
  }
end

end binary_search
end slice

end core
