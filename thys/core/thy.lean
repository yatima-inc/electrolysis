import core.generated
import data.finset
import data.list.sorted
import move

open [class] classical
open core
open eq.ops
open finset
open list
open nat
open option
open partial
open prod.ops

-- doesn't seem to get picked up by class inference
definition inv_image.wf' [trans_instance] {A : Type} {B : Type} {R : B → B → Prop} {f : A → B} [well_founded R] : well_founded (inv_image R f) := inv_image.wf f _

open list

namespace core

namespace cmp
  noncomputable definition ordering {T : Type} [linear_strong_order_pair T] (x y : T) : cmp.Ordering :=
  if x < y then Ordering.Less
  else if x = y then Ordering.Equal
  else Ordering.Greater

  structure Ord' [class] (T : Type) extends Ord T, order : linear_strong_order_pair T := -- issue #1066
  (cmp_eq : ∀x y : T, cmp x y = some (@ordering _ order x y))

  lemma Ord'.ord_cmp_eq {T : Type} [Ord' T] (x y : T) : Ord.cmp x y = some (ordering x y) := Ord'.cmp_eq x y -- HACK
end cmp

open cmp
open ops
open result

namespace slice
section

/- The SliceExt trait declares all methods on slices. It has a single implementation
   for [T] (= slice T, rendered as _T_). -/
open _T_.slice_SliceExt

parameter {T : Type}
variable (s : slice T)

lemma is_empty_eq : SliceExt.is_empty T s = some (s = []) :=
congr_arg some (propext (iff.intro
  eq_nil_of_length_eq_zero
  (λHeq, Heq⁻¹ ▸ length_nil)
))

-- s[start..]
lemma RangeFrom_index_eq (r : RangeFrom usize) (H : RangeFrom.start r ≤ length s) : _T_.ops_Index_ops_RangeFrom_usize__.index s r = some (dropn (RangeFrom.start r) s) :=
begin
  let st := RangeFrom.start r,
  have st ≤ length s ∧ length s ≤ length s, from and.intro H (le.refl _),
  rewrite [↑_T_.ops_Index_ops_RangeFrom_usize__.index, ↑_T_.ops_Index_ops_Range_usize__.index, if_pos this],
  have firstn (length s - st) (dropn st s) = dropn st s, from
    firstn_all_of_ge (length_dropn st s ▸ le.refl _),
  rewrite this,
end

-- s[..end]
lemma RangeTo_index_eq (r : RangeTo usize) (H : RangeTo.end_ r ≤ length s) : _T_.ops_Index_ops_RangeTo_usize__.index s r = some (firstn (RangeTo.end_ r) s) :=
begin
  let e := RangeTo.end_ r,
  have 0 ≤ e ∧ e ≤ length s, by simp, -- whoo!
  rewrite [↑_T_.ops_Index_ops_RangeTo_usize__.index, ↑_T_.ops_Index_ops_Range_usize__.index, if_pos this],
end

/- fn split_at(&self, mid: usize) -> (&[T], &[T])

Divides one slice into two at an index.

The first will contain all indices from [0, mid) (excluding the index mid itself) and the second will contain all indices from [mid, len) (excluding the index len itself).

Panics if mid > len.
-/
lemma split_at_eq {mid : usize} (H : mid ≤ length s) :
  split_at s mid = some (firstn mid s, dropn mid s) :=
by rewrite [↑split_at, !RangeTo_index_eq H, !RangeFrom_index_eq H]

/- fn binary_search_by<T, F: FnMut(&T) -> Ordering>(self: &[T], f: F) -> Result<usize, usize> -/
section binary_search_by
open _T_.slice_SliceExt.binary_search_by

variable base : usize
variable f : T ⇀ cmp.Ordering
premise Hf_term : ∀x, x ∈ s → f x ≠ none

private abbreviation loop_4.state := (T ⇀ cmp.Ordering) × usize × slice T

-- force same decidable instance as in generated.lean
attribute classical.prop_decidable [instance] [priority 10000]

attribute FnMut.call_mut [unfold 4]
attribute fn [constructor]

-- loop_4 either recurses with some sub-slice or terminates normally with some value
inductive loop_4.res : option (loop_4.state + result.Result u32 u32) → Prop :=
| cont : Πbase' s', length s' < length s → s' ⊆ s → loop_4.res (some (inl (f, base', s')))
| break: Πr, loop_4.res (some (inr r))

include Hf_term
private lemma loop_4.sem : loop_4.res s f (loop_4 (f, base, s)) :=
generalize_with_eq (loop_4 (f, base, s)) (begin
  intro res,
  rewrite [↑loop_4, ↑checked.shr],
  rewrite [of_int_one, pow_one],
  have length s / 2 ≤ length s, from !nat.div_le_self,
  rewrite [split_at_eq s this, ▸*, is_empty_eq, ▸*],
  eapply generalize_with_eq (dropn (length s / 2) s),
  intro s' Hs, cases s' with x xs,
  { rewrite [if_pos rfl],
    intro H, rewrite -H,
    right },
  { have Hwf : length s > length xs, from
      calc length xs < length (x :: xs) : lt_add_succ (length xs) 0
                 ... ≤ length s         : by rewrite [-Hs, length_dropn]; apply sub_le,
    rewrite [if_neg (λHeq : _ :: _ = nil, list.no_confusion Heq)],
    have 0 < length (x :: xs), from lt_of_le_of_lt !zero_le (lt_add_succ (length xs) 0),
    rewrite [if_pos this, nth_zero, ▸*],
    eapply generalize_with_eq (f x),
    intro fx Hfx, cases fx with ord,
    { exfalso,
      have x ∈ s, from !list.mem_of_mem_dropn (Hs⁻¹ ▸ mem_cons x xs),
      apply Hf_term x this Hfx },
    cases ord,
    { have 1 ≤ length (x :: xs), from succ_le_succ !zero_le,
      rewrite [RangeFrom_index_eq _ (RangeFrom.mk _) this, ▸*],
      intro H, rewrite -H,
      left,
      { calc length (dropn 1 (x :: xs)) = length xs : by rewrite [length_dropn, length_cons, ▸*, nat.add_sub_cancel, ]
                                    ... < length s  : Hwf },
      { rewrite -Hs,
        apply sub.trans, apply list.dropn_sub, apply list.dropn_sub }
    },
    { intro H, subst H,
      right },
    { intro H, subst H,
      left,
      { have length s ≠ 0,
        begin
          intro H,
          rewrite (eq_nil_of_length_eq_zero H) at Hs,
          contradiction
        end,
        calc length (firstn (length s / 2) s) ≤ length s / 2 : length_firstn_le
                                          ... < length s     : div_lt_of_ne_zero this },
      { apply list.firstn_sub }
    }
  }
end)
omit Hf_term

-- ...making it a well-founded recursion

private definition R := measure (λst : loop_4.state, length st.2)

private lemma R_wf [instance] : well_founded R := inv_image.wf'

-- proof via strong induction (probably easier than well-founded induction over the whole state tuple)
include Hf_term
private lemma fix_loop_4 : loop'.fix loop_4 R (f, base, s) ≠ none :=
begin
  eapply generalize_with_eq (length s), intro l,
  revert f base s Hf_term,
  induction l using nat.strong_induction_on with l' ih,
  intro f base s Hf_term Hlen,
  subst Hlen,
  rewrite loop'.fix_eq,
  note H := loop_4.sem s base f Hf_term, revert H,
  eapply generalize_with_eq (loop_4 (f, base, s)), intro res _ Hres,
  cases Hres with base' s' Hlen Hsub r,
  { have R (f, base', s') (f, base, s), from Hlen,
    rewrite [if_pos this],
    apply ih, exact Hlen,
    { intro x Hxs, apply Hf_term x (Hsub Hxs) },
    exact rfl
  },
  { contradiction }
end

lemma binary_search_by_terminates : binary_search_by s f ≠ none :=
begin
  note H := fix_loop_4 s 0 f Hf_term,
  rewrite [↑binary_search_by, -!loop'.fix_eq_loop' H],
  apply H
end

end binary_search_by

parameters [cmp.Ord T]
premise (Hord_term : ∀x y : T, cmp.Ord.cmp x y ≠ none)

/- fn binary_search(&self, x: &T) -> Result<usize, usize> where T: Ord

Binary search a sorted slice for a given element.

If the value is found then Ok is returned, containing the index of the matching element; if the value is not found then Err is returned, containing the index where a matching element could be inserted while maintaining sorted order.-/
include Hord_term
lemma binary_search_terminates (x : T) : binary_search s x ≠ none :=
begin
  rewrite [↑binary_search, bind_some_eq_id],
  apply binary_search_by_terminates,
  intro y Hys, rewrite bind_some_eq_id, apply Hord_term y x
end

end
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
