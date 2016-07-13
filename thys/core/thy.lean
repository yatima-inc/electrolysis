import core.generated

import algebra.interval
import data.finset
import data.list.sorted
import move

open [class] classical
open core
open eq.ops
open list
open list.prefixeq
open nat
open interval
open option
open partial
open prod.ops
open set

-- doesn't seem to get picked up by class inference
definition inv_image.wf' [trans_instance] {A : Type} {B : Type} {R : B → B → Prop} {f : A → B} [well_founded R] : well_founded (inv_image R f) := inv_image.wf f _

attribute sem [reducible]

namespace core

namespace cmp
  definition ordering {T : Type} [decidable_linear_order T] (x y : T) : cmp.Ordering :=
  if x < y then Ordering.Less
  else if x = y then Ordering.Equal
  else Ordering.Greater

  structure Ord' [class] (T : Type₁) extends Ord T, decidable_linear_order T :=
  (max_cost : ℕ)
  (cmp_eq : ∀x y : T, ∃k, k ≤ max_cost ∧ cmp x y = some (ordering x y, k))

  lemma Ord'.ord_cmp_eq {T : Type₁} [Ord' T] (x y : T) :
    ∃k, k ≤ Ord'.max_cost T ∧ Ord.cmp x y = some (ordering x y, k) := Ord'.cmp_eq x y -- HACK
end cmp

open cmp
open ops
open result

namespace slice

/- The SliceExt trait declares all methods on slices. It has a single implementation
   for [T] (= slice T, rendered as _T_). -/
open _T_.slice_SliceExt

section

parameter {T : Type₁}
variable (s : slice T)

lemma is_empty_eq : SliceExt.is_empty T s = some (s = [], 1) :=
congr_arg some (prod.eq
  (propext (iff.intro
    eq_nil_of_length_eq_zero
    (λHeq, Heq⁻¹ ▸ length_nil)
  ))
  rfl)

-- s[start..]
lemma RangeFrom_index_eq (r : RangeFrom usize) (H : RangeFrom.start r ≤ length s) :
  _T_.ops_Index_ops_RangeFrom_usize__.index s r = some (dropn (RangeFrom.start r) s, 2) :=
begin
  let st := RangeFrom.start r,
  have st ≤ length s ∧ length s ≤ length s, from and.intro H (le.refl _),
  rewrite [↑_T_.ops_Index_ops_RangeFrom_usize__.index, ↑_T_.ops_Index_ops_Range_usize__.index,
    return_bind, if_pos this],
  have firstn (length s - st) (dropn st s) = dropn st s, from
    firstn_all_of_ge (length_dropn st s ▸ le.refl _),
  rewrite this,
end

-- s[..end]
lemma RangeTo_index_eq (r : RangeTo usize) (H : RangeTo.end_ r ≤ length s) :
  _T_.ops_Index_ops_RangeTo_usize__.index s r = some (firstn (RangeTo.end_ r) s, 1) :=
begin
  let e := RangeTo.end_ r,
  have 0 ≤ e ∧ e ≤ length s, by simp,
  rewrite [↑_T_.ops_Index_ops_RangeTo_usize__.index, ↑_T_.ops_Index_ops_Range_usize__.index, if_pos this],
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
open _T_.slice_SliceExt.binary_search_by

parameter {T : Type₁}
parameter [Ord' T]
parameter self : slice T
parameter needle : T

hypothesis Hsorted : sorted le self

abbreviation f y := sem.incr (Ord.cmp y needle)

attribute FnMut.call_mut [unfold 4]
attribute fn [constructor]

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
mk : Πbase' s', loop_4_invar s' base' → length s' < length s → loop_4_step (f, base', s')

abbreviation loop_4_res := sum.rec (loop_4_step s) binary_search_res

attribute sem.return [constructor]
attribute sem.incr [unfold 2]

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

private lemma loop_4.sem (Hinvar : loop_4_invar s base) : sem.terminates_with
  (loop_4_res s)
  (15 + Ord'.max_cost T)
  (loop_4 (f, base, s)) :=
have sorted_s : sorted le s, from sorted.sorted_of_prefix_of_sorted
  (loop_4_invar.s_in_self Hinvar)
  (sorted.sorted_dropn_of_sorted Hsorted _),
generalize_with_eq (loop_4 (f, base, s)) (begin
  intro res,
  rewrite [↑loop_4, ↑checked.shr],
  rewrite [of_int_one, pow_one],
  have length s / 2 ≤ length s, from !nat.div_le_self,
  rewrite [split_at_eq s this, ▸*, is_empty_eq, ▸*],
  let s₁ := firstn (length s / 2) s,
  let s₂ := dropn (length s / 2) s,
  have len_s₁ : length s₁ = length s / 2, by
    rewrite [length_firstn_eq, min_eq_left this],
  eapply generalize_with_eq (dropn (length s / 2) s),
  intro s' Hs, cases s' with x xs,
  { rewrite [if_pos' rfl],
    intro H, rewrite -H,
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
    apply sem.terminates_with.mk rfl,
    { esimp, right,
      { show needle ∉ self, from
        take Hneedle,
        have needle ∈ s, from loop_4_invar.needle_mem Hinvar Hneedle,
        Hs ▸ this },
      { apply sorted.sorted_insert_at_insert_pos Hsorted }
    },
    { apply le_add_of_le_right, apply dec_trivial }
  },
  { have Hwf : length s > length xs, from
      calc length xs < length (x :: xs) : lt_add_succ (length xs) 0
                 ... ≤ length s         : by rewrite [-Hs, length_dropn]; apply sub_le,
    have x :: xs ≠ nil, by contradiction,
    rewrite [if_neg' this],
    have 0 < length (x :: xs), from lt_of_le_of_lt !zero_le (lt_add_succ (length xs) 0),
    rewrite [if_pos' this, ↑get_unchecked, nth_zero, ↑f],
    --obtain k `k ≤ Ord'.max_cost T` cmp_eq, from Ord'.ord_cmp_eq x needle,
    cases Ord'.ord_cmp_eq x needle with k H, cases H with k_le_max_cost cmp_eq,
    rewrite [cmp_eq, ↑ordering, ▸*],
    have nth_x : nth self (base + length s₁) = some x,
    begin
      have nth s (length s / 2) = some x, by rewrite [nth_eq_first'_dropn, Hs, ▸*, nth_zero],
      rewrite [nth_eq_first'_dropn, add.comm, -dropn_dropn, -nth_eq_first'_dropn, len_s₁],
      apply prefixeq.nth_of_nth_prefixeq this (loop_4_invar.s_in_self Hinvar)
    end,
    cases (decidable_lt : decidable (x < needle)) with Hx_lt_needle Hx_ge_needle,
    { have 1 ≤ length (x :: xs), from succ_le_succ !zero_le,
      rewrite [RangeFrom_index_eq _ (RangeFrom.mk _) this, ▸*],
      intro H, rewrite -H,
      apply sem.terminates_with.mk rfl,
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
        exact calc length (dropn 1 (x :: xs)) = length xs : by rewrite [length_dropn, length_cons, ▸*, nat.add_sub_cancel]
                                          ... < length s  : Hwf },
      { repeat (rewrite [{k + _ + _}add.assoc] | rewrite [-{_ + (k + _)}add.assoc] |
                rewrite [{_ + k}add.comm]),
        rewrite [{k + _}add.comm],
        apply add_le_add_left `k ≤ Ord'.max_cost T` }
    },
    { intro H, subst H,
      cases (has_decidable_eq : decidable (x = needle)) with Hfound Hnot_found,
      { apply sem.terminates_with.mk rfl,
        { left, apply Hfound ▸ nth_x },
        { repeat (rewrite [{k + _ + _}add.assoc] | rewrite [-{_ + (k + _)}add.assoc] |
                  rewrite [{_ + k}add.comm]),
          rewrite [{k + _}add.comm],
          apply add_le_add dec_trivial `k ≤ Ord'.max_cost T` }
      },
      { have Hx_ge_needle : x > needle, from lt_of_le_of_ne (le_of_not_gt Hx_ge_needle) (ne.symm Hnot_found),
        apply sem.terminates_with.mk rfl,
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
          { have length s ≠ 0,
            begin
              intro H,
              rewrite (eq_nil_of_length_eq_zero H) at Hs,
              contradiction
            end,
            calc length s₁ ≤ length s / 2 : length_firstn_le
                        ... < length s     : div_lt_of_ne_zero this }
        },
        { repeat (rewrite [{k + _ + _}add.assoc] | rewrite [-{_ + (k + _)}add.assoc] |
                  rewrite [{_ + k}add.comm]),
          rewrite [{k + _}add.comm],
          apply add_le_add dec_trivial `k ≤ Ord'.max_cost T` }
      }
    }
  }
end)

private definition R := measure (λst : loop_4.state, length st.2)

private lemma R_wf [instance] : well_founded R := inv_image.wf'

-- proof via strong induction (probably easier than well-founded induction over the whole state tuple)
include Hsorted
private lemma fix_loop_4 (Hinvar : loop_4_invar s base) : sem.terminates_with
  binary_search_res
  (length s * (15 + Ord'.max_cost T))
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
    { cases Hstep with base' s' Hinvar' Hvar,
      esimp,
      have R (f, base', s') (f, base, s), from Hvar,
      rewrite [if_pos' this],
      cases ih _ Hvar _ _ Hinvar' rfl with _ res' k' Hsem'_eq Hres' Hmax_cost',
      clear ih,
      rewrite Hsem'_eq,      
      esimp,
      apply sem.terminates_with.mk rfl,
      exact Hres',
      exact calc k + k' + 1
          ≤ (15 + Ord'.max_cost T) + k' + 1 : add_le_add_right (add_le_add_right Hmax_cost _) _
      ... ≤ (15 + Ord'.max_cost T) + length s' * (15 + Ord'.max_cost T) + 1 :
        add_le_add_right (add_le_add_left Hmax_cost' _) _
      ... ≤ length s * (15 + Ord'.max_cost T) : sorry
    },
    { esimp,
      apply sem.terminates_with.mk rfl,
      apply Hstep,
      apply sorry
    }
  }
end

end loop_4

include Hsorted
theorem binary_search_by.sem : sem.terminates_with
  binary_search_res
  (length self * (15 + Ord'.max_cost T))
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

theorem binary_search.sem : sem.terminates_with
  binary_search_res
  (length self * (15 + Ord'.max_cost T) + 1)
  (binary_search self needle) :=
begin
  cases binary_search_by.sem with  _ res k Hsem_eq Hres Hmax_cost,
  rewrite [↑binary_search, bind_return,
    funext (λx, congr_arg sem.incr bind_return),
    ↑binary_search_by,
    Hsem_eq],
  apply sem.terminates_with.mk rfl,
  apply Hres,
  apply add_le_add_right Hmax_cost
end

end binary_search
end slice

/-
theorem decidable_eq_decidable {A : Prop} (x y : decidable A) : x = y :=
begin
  cases x,
  { cases y,
    { apply rfl },
    { contradiction },
  },
  { cases y,
    { contradiction },
    { apply rfl }
  }
end

open ops

section
  parameters {Res : Type}
  abbreviation State := Res × Range ℕ
  parameters {P : ℕ → Res → Prop}
  parameters {l r : ℕ} {res₀ : Res}
  parameters {body : (State → option State) → ℕ → Res → Range ℕ → option State} {body' : ℕ → Res → Res}
  hypothesis (Hstart : P l res₀)
  hypothesis (Hdoes_step : ∀{f i res iter}, l ≤ i → i < r → P i res → body f i res iter = f ((body' i res, iter)))
  hypothesis (Hstep : ∀{i res}, l ≤ i → i < r → P i res → P (i+1) (body' i res))

  include Hstart Hdoes_step Hstep

  private definition variant (s : State) := Range.end_ s.2 - Range.start s.2

  inductive invariant (s : State) : Prop :=
  mk : Π(Hlo : l ≤ Range.start s.2)
  (Hhi : Range.start s.2 ≤ max l r)
  (Hend_ : Range.end_ s.2 = r)
  (HP : P (Range.start s.2) s.1), invariant s

  attribute num.u32.One [constructor]
  attribute ops.u32.Add [constructor]
  attribute cmp.impls.u32.PartialOrd [constructor]
  attribute iter.u32.Step [constructor]
  attribute iter.Step.to_PartialOrd [unfold 2]

  theorem loop_range : option.all (λstate, P (max l r) state.1) (fix_opt (λrec__ tmp__,
    match tmp__ with (res, iter) :=
      do tmp__ ← core.iter.ops.Range_A_.Iterator.next iter;
      match tmp__ with (t7, iter) :=
        match t7 with
        | core.option.Option.None := some (res, iter)
        | core.option.Option.Some i := body rec__ i res iter
        end
      end
    end) (res₀, ops.Range.mk l r)) :=
  begin
    apply loop invariant,
    {
      apply invariant.mk,
      all_goals esimp,
      { apply le_max_left },
      { apply Hstart },
    },
    { intro s f Hinv,
      cases Hinv, cases s with res iter,
      esimp at *,
      esimp [iter.ops.Range_A_.Iterator.next, cmp.PartialOrd.lt, mem.swap, num.u32.One.one, ops.u32.Add.add],
      esimp [cmp.impls.u32.PartialOrd.partial_cmp, cmp.impls.u32.Ord.cmp],
      cases classical.em (Range.start iter = Range.end_ iter) with Hend Hnot_end,
      { rewrite [if_pos Hend],
        esimp,
        rewrite [decidable_eq_decidable (classical.prop_decidable false) decidable_false, if_false],
        apply exists.intro,
        apply or.inl rfl,
      },
      { rewrite [if_neg Hnot_end],
        cases classical.em (Range.start iter < Range.end_ iter) with H₁ H₂,
        { rewrite [if_pos H₁],
          esimp,
          rewrite [decidable_eq_decidable (classical.prop_decidable true) decidable_true, if_true],
          apply exists.intro,
          apply or.inr,
          apply Hdoes_step Hlo (Hend_ ▸ H₁) HP
        },
        { rewrite [if_neg H₂],
          esimp,
          rewrite [decidable_eq_decidable (classical.prop_decidable false) decidable_false, if_false],
          apply exists.intro,
          apply or.inl rfl,
        }
      }
    },
    { intro f s s' Hinv,
      cases Hinv, cases s with res iter,
      esimp at *,
      esimp [iter.ops.Range_A_.Iterator.next, cmp.PartialOrd.lt, mem.swap, num.u32.One.one, ops.u32.Add.add],
      esimp [cmp.impls.u32.PartialOrd.partial_cmp, cmp.impls.u32.Ord.cmp],
      cases classical.em (Range.start iter = Range.end_ iter) with Hend Hnot_end,
      { rewrite [if_pos Hend],
        esimp,
        rewrite [decidable_eq_decidable (classical.prop_decidable false) decidable_false, if_false],
        esimp,
        intro Hfs',
      },
      { rewrite [if_neg Hnot_end],
      }
    }
end
-/

end core
