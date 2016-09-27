import core.generated

import algebra.interval
import data.finset
import data.list.sorted

import asymptotic

open bool (tt ff)
open core
open eq.ops
open list
open list.prefixeq
open [class] [notation] nat
open nat (to_bits of_bits)
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

namespace core

/-lemma of_bits_to_bits (x : ℕ) : of_bits (to_bits x) = x :=
begin
  induction x using nat.strong_induction_on,
  unfold to_bits
end-/

attribute bool.has_decidable_eq [unfold 1 2]

namespace nat
  lemma of_bits_ne_zero_of_msb_set : Π{xs : list bool}, last' xs = some tt → of_bits xs ≠ 0
  | []          h := by contradiction
  | [tt]        h := dec_trivial
  | [ff]        h := by injection h; contradiction
  | (x::x'::xs) h :=
    have of_bits (x'::xs) ≠ 0, from of_bits_ne_zero_of_msb_set (last'_cons_eq_last' dec_trivial ▸ h),
    have 2 * of_bits (x'::xs) ≠ 0, from nat.mul_ne_zero dec_trivial this,
    take contr,
    this (nat.eq_zero_of_add_eq_zero_left contr)

  lemma of_bits_to_bits (n : ℕ) : of_bits (to_bits n) = n :=
  begin
    rewrite [↑of_bits, ↑to_bits],
    induction well_founded.apply nat.lt.wf n with n _ ih,
    rewrite well_founded.fix_eq,
    cases (_ : decidable (n = 0)),
    { rewrite [▸*, `n = 0`] },
    {
      esimp,
      rewrite [ih (n / 2) (nat.div_lt_of_ne_zero `n ≠ 0`)],
      cases (_ : decidable (n % 2 = 1)) with odd even,
      { rewrite [▸*, nat.eq_div_mul_add_mod n 2 at {2}, odd, add.comm, mul.comm] },
      {
        have n % 2 = 0, begin
          cases nat.lt_trichotomy (n % 2) 1 with lt eq_or_gt,
          { apply nat.eq_zero_of_le_zero (nat.le_of_lt_succ lt) },
          { cases eq_or_gt,
            { contradiction },
            { intro,
              have n % 2 ≤ 1, from nat.le_of_lt_succ (nat.mod_lt n (show 2 > 0, from dec_trivial)),
              exfalso, apply nat.lt_le_antisymm `n % 2 > 1` this }
          }
        end,
        rewrite [▸*, nat.eq_div_mul_add_mod n 2 at {2}, add.comm, mul.comm, this] }
    },
  end
  
  definition norm (xs : list bool) := last' xs ≠ some ff

  lemma norm_of_norm_cons {x : bool} : Π{xs : list bool}, norm (x::xs) → norm xs
  | []      h := by contradiction
  | (x::xs) h := by exact h

  lemma to_bits_of_bits : Π(xs : list bool), norm xs → to_bits (of_bits xs) = xs
  | []       h := rfl
  | (tt::xs) h := begin
    rewrite [↑of_bits],
    have ∀x, to_bits (1 + 2 * x) = tt :: to_bits x,
    begin
      intro x,
      rewrite [↑to_bits, well_founded.fix_eq,
        dif_neg (show 1 + 2 * x ≠ 0, from nat.ne_zero_of_pos (nat.add_pos_left dec_trivial _)),
        if_pos (show (1 + 2 * x) % 2 = 1, by rewrite [nat.add_mul_mod_self_left]),
        nat.add_mul_div_self_left _ _ (show 2 > 0, from dec_trivial),
        (show (1:ℕ) / 2 = 0, from rfl),
        zero_add
      ],
    end,
    rewrite this,
    have last' xs ≠ some ff, begin
      cases xs,
      { contradiction },
      { exact h }
    end,
    rewrite [to_bits_of_bits xs this],
  end
  | (ff::xs) h := begin
    let x := of_bits xs,
    have last' (ff::xs) = some tt, begin
      eapply generalize_with_eq (last' (ff::xs)), intro lsb lsb_eq,
      cases lsb with lsb,
      { contradiction },
      { cases lsb,
        { rewrite [↑norm at h, lsb_eq at h], exfalso, exact h rfl },
        exact rfl
      }
    end,
    rewrite [↑to_bits, well_founded.fix_eq, ↓to_bits,
      dif_neg (of_bits_ne_zero_of_msb_set this),
      ↑of_bits,
      if_neg (show (0 + 2 * x) % 2 ≠ 1, by rewrite [nat.add_mul_mod_self_left]; apply dec_trivial),
      nat.add_mul_div_self_left _ _ (show 2 > 0, from dec_trivial),
      (show (0:ℕ) / 2 = 0, from rfl),
      zero_add,
      to_bits_of_bits xs (norm_of_norm_cons h)
    ]
  end
end nat

open nat

lemma bitor.rec_norm : Π{xs ys : list bool}, nat.norm xs → nat.norm ys → nat.norm (bitor.rec xs ys)
| [] ys h₁ h₂ := begin
  rewrite [↑bitor.rec, ▸*],
  induction ys; apply h₂; apply h₂
end
| xs [] h₁ h₂ := begin
  rewrite [↑bitor.rec, ▸*],
  induction xs; apply h₁; apply h₁
end
| (x::xs) (y::ys) h₁ h₂ := begin
  rewrite [↑bitor.rec, ▸*],
  note ih := bitor.rec_norm (nat.norm_of_norm_cons h₁) (nat.norm_of_norm_cons h₂),
  revert ih,
  rewrite [↑nat.norm],
  --cases bitor.rec xs ys,
  apply sorry
end

lemma bitand_bitor (x y : ℕ) : (x || y) && y = y :=
begin
  esimp [bitand, bitor],
  induction to_bits x with xb xbs ih,
  {
    rewrite [↑bitor.rec],
    apply generalize_with_eq (to_bits y), intro ybs ybs_eq,
    cases ybs with yb ybs',
    { rewrite [▸*, ↑of_bits, -nat.of_bits_to_bits y, ybs_eq] },
    { rewrite [▸*, -ybs_eq, nat.of_bits_to_bits, map₂_self, map_id' bool.band_self,
        nat.of_bits_to_bits] }
  },
  {
    apply generalize_with_eq (to_bits y), intro ybs ybs_eq,
    cases ybs with yb ybs',
    { rewrite [▸*, map₂_nil2, -nat.of_bits_to_bits y, ybs_eq] },
    apply sorry,
    --{ rewrite [nat.to_bits_of_bits (bitor.rec_norm _ _), ↑bitor.rec] }
  }
end

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

parameter {T : Type₁}
parameter [Ord' T]

attribute FnMut.call_mut [unfold 4]
attribute fn [constructor]

-- use separate section for everything but the main theorem
section

parameter self : slice T
parameter needle : T

hypothesis Hsorted : sorted le self

abbreviation f y := sem.incr 1 (Ord.cmp y needle)
abbreviation cmp_max_cost := Ord'.cmp_max_cost needle self

/- fn binary_search(&self, x: &T) -> Result<usize, usize> where T: Ord

Binary search a sorted slice for a given element.

If the value is found then Ok is returned, containing the index of the matching element; if the value is not found then Err is returned, containing the index where a matching element could be inserted while maintaining sorted order.-/
inductive binary_search_res : Result usize usize → Prop :=
| found     : Πi, nth self i = some needle → binary_search_res (Result.Ok i)
| not_found : Πi, needle ∉ self → sorted le (insert_at self i needle) → binary_search_res (Result.Err i)

section loop_4

variable s : slice T
variable base : usize

private abbreviation loop_4.state := (T → sem cmp.Ordering) × usize × slice T

include self needle base s -- HACK
structure loop_4_invar :=
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

attribute list.has_decidable_eq [unfold 3 4]

private lemma loop_4.sem (Hinvar : loop_4_invar s base) : sem.terminates_with_in
  (loop_4_res s)
  (15 + cmp_max_cost)
  (loop_4 (f, base, s)) :=
have sorted_s : sorted le s, from sorted.sorted_of_prefix_of_sorted
  (loop_4_invar.s_in_self Hinvar)
  (sorted.sorted_dropn_of_sorted Hsorted _),
generalize_with_eq (loop_4 (f, base, s)) (begin
  intro res,
  rewrite [↑loop_4, ↑checked.shr],
  krewrite [pow_one],
  have length s / 2 ≤ length s, from !nat.div_le_self,
  rewrite [▸*, split_at_eq s this, ▸*, is_empty_eq, ▸*],
  let s₁ := firstn (length s / 2) s,
  let s₂ := dropn (length s / 2) s,
  have len_s₁ : length s₁ = length s / 2, by
    rewrite [length_firstn_eq, min_eq_left this],
  eapply generalize_with_eq (dropn (length s / 2) s),
  intro s' Hs, cases s' with x xs,
  { intro H, rewrite -H,
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
    { apply le_add_of_le_right, apply dec_trivial }
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
    rewrite [cmp_eq, ↑ordering, ▸*],
    have nth_x : nth self (base + length s₁) = some x,
    begin
      have nth s (length s / 2) = some x, by rewrite [nth_eq_first'_dropn, Hs, ▸*, nth_zero],
      rewrite [nth_eq_first'_dropn, add.comm, -dropn_dropn, -nth_eq_first'_dropn, len_s₁],
      apply prefixeq.nth_of_nth_prefixeq this (loop_4_invar.s_in_self Hinvar)
    end,
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
        rewrite [{k + _}add.comm],
        apply add_le_add_left Hle_max_cost }
    },
    { intro H, subst H,
      cases (has_decidable_eq : decidable (x = needle)) with Hfound Hnot_found,
      { apply sem.terminates_with_in.mk rfl,
        { left, apply Hfound ▸ nth_x },
        { repeat (rewrite [{k + _ + _}add.assoc] | rewrite [-{_ + (k + _)}add.assoc] |
                  rewrite [{_ + k}add.comm]),
          rewrite [{k + _}add.comm],
          apply add_le_add dec_trivial Hle_max_cost }
      },
      { have Hx_ge_needle : x > needle, from lt_of_le_of_ne (le_of_not_gt Hx_ge_needle) (ne.symm Hnot_found),
        apply sem.terminates_with_in.mk rfl,
        { split,
          exact ⦃loop_4_invar,
            s_in_self := prefixeq.trans !firstn_prefixeq (loop_4_invar.s_in_self Hinvar),
            insert_pos := begin
              split,
              { apply and.left (loop_4_invar.insert_pos Hinvar) },
              { apply sorted.insert_pos_le Hsorted Hx_ge_needle nth_x }
            end,
            needle_mem := assume Hneedle : needle ∈ self,
              have needle ∈ s₁ ++ s₂, by rewrite [firstn_app_dropn_eq_self]; apply loop_4_invar.needle_mem Hinvar Hneedle,
              or.rec_on (mem_or_mem_of_mem_append this)
                (suppose needle ∈ s₁, this)
                (suppose needle ∈ s₂,
                  have x ≤ needle, from sorted.first_le
                    (show sorted le (x::xs), from Hs ▸ sorted.sorted_dropn_of_sorted sorted_s _)
                    (show needle ∈ x::xs, from Hs ▸ this),
                  false.elim (not_le_of_gt Hx_ge_needle this))
          ⦄,
          exact !length_firstn_le,
          exact `length s ≠ 0`
        },
        { repeat (rewrite [{k + _ + _}add.assoc] | rewrite [-{_ + (k + _)}add.assoc] |
                  rewrite [{_ + k}add.comm]),
          rewrite [{k + _}add.comm],
          apply add_le_add dec_trivial Hle_max_cost }
      }
    }
  }
end)

private definition R := measure (λst : loop_4.state, length st.2)

private lemma R_wf [instance] : well_founded R := inv_image.wf'

-- proof via strong induction (probably easier than well-founded induction over the whole state tuple)
include Hsorted
private lemma fix_loop_4 (Hinvar : loop_4_invar s base) : sem.terminates_with_in
  binary_search_res
  ((log₂ (2 * length s) + 1) * (16 + cmp_max_cost))
  (loop.fix loop_4 R (f, base, s)) :=
begin
  eapply generalize_with_eq (length s), intro l,
  revert base s Hinvar,
  induction l using nat.strong_induction_on with l' ih,
  intro base s Hinvar Hlen,
  subst Hlen,
  rewrite loop.fix_eq,
  note Hres := loop_4.sem s base Hinvar, revert Hres,
  eapply generalize_with_eq (loop_4 (f, base, s)), intro res _,
  -- exact match res with -- unifier doesn't like this anymore
  -- | some (sum.inl st', k) := begin
  cases res,
  { intro H, cases H, contradiction },
  { intro H, cases H with _ res k Hsem_eq Hstep Hmax_cost,
    rewrite Hsem_eq,
    cases res with st' r,
    { cases Hstep with base' s' Hinvar' Hvar Hs_ne_nil,
      esimp,
      have R (f, base', s') (f, base, s), from
        lt_of_le_of_lt Hvar (div_lt_of_ne_zero Hs_ne_nil),
      rewrite [if_pos' this],
      cases ih _ this _ _ Hinvar' rfl with _ res' k' Hsem'_eq Hres' Hmax_cost',
      clear ih,
      rewrite Hsem'_eq,      
      esimp,
      apply sem.terminates_with_in.mk rfl,
      exact Hres',
      exact calc k' + k + 1
          = k + k' + 1 : by rewrite (add.comm k k')
      ... ≤ (15 + cmp_max_cost) + k' + 1 : add_le_add_right (add_le_add_right Hmax_cost _) _
      ... ≤ (15 + cmp_max_cost) + (log₂ (length s) + 1) * (16 + cmp_max_cost) + 1 :
        add_le_add_right (add_le_add_left
          (show k' ≤ (log₂ (length s) + 1) * (16 + cmp_max_cost), from le.trans Hmax_cost' (mul_le_mul_right _
            (show log₂ (2 * length s') + 1 ≤ log₂ (length s) + 1, from add_le_add_right
              (nondecreasing_log dec_trivial (le.trans (mul_le_mul_left 2 Hvar) (!mul.comm ▸ div_mul_le _ _)))
              _)))
        _) _
      ... = (log₂ (length s) + 1 + 1) * (16 + cmp_max_cost) :
        by rewrite [add.comm, -+add.assoc, nat.right_distrib (_ + 1), add.comm, one_mul]
      ... = (log₂ (2 * length s) + 1) * (16 + cmp_max_cost) : begin
        { rewrite [-@log.rec 2 dec_trivial _ (pos_of_ne_zero `length s ≠ 0`)] }
      end
    },
    { esimp,
      apply sem.terminates_with_in.mk rfl,
      apply Hstep,
      exact calc 0 + k + 1
          = k + 1 : by rewrite zero_add
      ... ≤ 15 + cmp_max_cost + 1 : add_le_add_right Hmax_cost
      ... = 16 + cmp_max_cost : by rewrite nat.add_right_comm
      ... ≤ (log 2 (2 * length s) + 1) * (16 + cmp_max_cost) : by
        rewrite [nat.right_distrib, one_mul]; apply le_add_left }
  }
end

end loop_4

include Hsorted
theorem binary_search_by.sem : sem.terminates_with_in
  binary_search_res
  ((log₂ (2 * length self) + 1) * (16 + cmp_max_cost))
  (binary_search_by self f) :=
begin
  have loop_4_invar self 0, from ⦃loop_4_invar,
    s_in_self := !prefixeq.refl,
    insert_pos := and.intro !zero_le (!zero_add⁻¹ ▸ !sorted.insert_pos_le_length),
    needle_mem := id
  ⦄,
  note H := fix_loop_4 self 0 this,
  have loop.fix loop_4 R (f, 0, self) ≠ none, begin
    intro Hnonterm, rewrite Hnonterm at H, cases H, contradiction
  end,
  rewrite [↑binary_search_by, -!loop.fix_eq_loop this],
  apply H
end
end

local infix `≼`:25 := asymptotic.le ([at ∞] : filter ℕ)

theorem binary_search.sem :
  ∃₀f ∈ 𝓞(λp, log₂ p.1 * p.2) [at ∞ × ∞],
  ∀(self : slice T) (needle : T), sorted le self → sem.terminates_with_in
    (binary_search_res self needle)
    (f (length self, Ord'.cmp_max_cost needle self))
    (binary_search self needle) :=
begin
  existsi λp, (log₂ (2 * p.1) + 1) * (16 + p.2) + 1,
  split,
  { apply ub_add,
    show (λp, (log₂ (2 * p.1) + 1) * (16 + p.2)) ∈ 𝓞(λp, log₂ p.1 * p.2) [at ∞ × ∞], from
    ub_mul_prod_filter
      (calc (λa, log₂ (2 * a) + 1)
          ≼ (λa, log₂ a + 2) : ub_of_eventually_le (eventually_at_infty_intro (
            take a, suppose a ≥ 1,
            calc log₂ (2 * a) + 1 = log₂ a + 1 + 1 : { @log.rec 2 dec_trivial _ this }
                              ... ≤ log₂ a + 2     : le_of_eq !add.assoc))
      ... ≼ log₂ : ub_add asymptotic.le.refl (
            calc (λx, 2) ≼ (λx, 1) : ub_const
                    ... ≼ log₂    : asymptotic.le_of_lt (@log_unbounded 2 dec_trivial)))
      (have (λa, 16) ≼ id, from ub_of_eventually_le (eventually_at_infty_intro (λx Hx, Hx)),
        calc (λa, 16 + a) = (λa, a + 16) : funext (λa, !add.comm)
                      ... ≼ id           : ub_add asymptotic.le.refl this),
    show (λp, 1) ∈ 𝓞(λp, log₂ p.1 * p.2) [at ∞ × ∞],
    begin
      rewrite [-mul_one 1 at {1}],
      apply ub_mul_prod_filter,
      { apply asymptotic.le_of_lt, apply log_unbounded dec_trivial },
      { apply asymptotic.le_of_lt, apply id_unbounded },
    end
  },
  { intro self needle Hsorted,
    cases binary_search_by.sem self needle Hsorted with  _ res k Hsem_eq Hres Hmax_cost,
    rewrite [↑binary_search, bind_return,
      funext (λx, congr_arg (sem.incr 1) bind_return),
      ↑binary_search_by,
      Hsem_eq],
    apply sem.terminates_with_in.mk rfl,
    apply Hres,
    apply add_le_add_right Hmax_cost }
end

end binary_search
end slice

end core
