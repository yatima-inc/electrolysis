import core.generated

open [class] classical
open core
open eq.ops
open list
open nat
open option
open prod.ops
open sum

definition inv_image.wf' [trans_instance] {A : Type} {B : Type} {R : B → B → Prop} {f : A → B} [well_founded R] : well_founded (inv_image R f) := inv_image.wf f _

lemma list.dropn_zero {A : Type} (xs : list A) : dropn 0 xs = xs := rfl

namespace core

open ops

namespace slice
section

open SliceExt
open _T_.SliceExt

parameters {T : Type}
variables (s : slice T)

attribute _T_.SliceExt [constructor]
attribute len [unfold 3]

lemma is_empty_eq : is_empty T s = some (s = []) :=
congr_arg some (propext (iff.intro
  eq_nil_of_length_eq_zero
  (λHeq, Heq⁻¹ ▸ length_nil)
))

lemma RangeFrom_index_eq (r : RangeFrom usize) (H : RangeFrom.start r ≤ length s) : _T_.ops.Index_ops.RangeFrom_usize__.index s r = some (dropn (RangeFrom.start r) s) :=
begin
  let st := RangeFrom.start r,
  have st ≤ length s ∧ length s ≤ length s, from and.intro H (le.refl _),
  rewrite [↑_T_.ops.Index_ops.RangeFrom_usize__.index, ↑_T_.ops.Index_ops.Range_usize__.index, if_pos this],
  have firstn (length s - st) (dropn st s) = dropn st s, from
    firstn_all_of_ge (length_dropn st s ▸ le.refl _),
  rewrite this,
end

lemma RangeTo_index_eq (r : RangeTo usize) (H : RangeTo.end_ r ≤ length s) : _T_.ops.Index_ops.RangeTo_usize__.index s r = some (firstn (RangeTo.end_ r) s) :=
begin
  let e := RangeTo.end_ r,
  have 0 ≤ e ∧ e ≤ length s, by simp, -- whoo!
  rewrite [↑_T_.ops.Index_ops.RangeTo_usize__.index, ↑_T_.ops.Index_ops.Range_usize__.index, if_pos this],
end

/- fn split_at(&self, mid: usize) -> (&[T], &[T])

Divides one slice into two at an index.

The first will contain all indices from [0, mid) (excluding the index mid itself) and the second will contain all indices from [mid, len) (excluding the index len itself).

Panics if mid > len.
-/
lemma split_at_eq {mid : usize} (H : mid ≤ length s) :
  split_at s mid = some (firstn mid s, dropn mid s) :=
by rewrite [↑split_at, !RangeTo_index_eq H, !RangeFrom_index_eq H]

open _T_.SliceExt.binary_search_by

/- fn binary_search_by<T, F: FnMut(&T) -> Ordering>(self: &[T], f: F) -> Result<usize, usize> -/

parameters {F : Type} [f_impl : FnMut T F cmp.Ordering]
variables (f : F)
hypothesis (Hf_impl_term : Πf x, @FnMut.call_mut _ _ _ f_impl f x ≠ none)
include f_impl Hf_impl_term

abbreviation loop_4_state := F × usize × slice T

attribute classical.prop_decidable [instance] [priority 10000]

private lemma loop_4_term (base : nat) : loop' (loop_4 f) (f, base, s) ≠ none :=
begin
  have ∀l base (s : slice T), length s = l → loop' (loop_4 f) (f, base, s) ≠ none,
  begin
    intro l,
    induction l using nat.strong_induction_on with l' ih,
    intro base s Hlen,
    subst Hlen,
    let R := inv_image lt (λs : loop_4_state, length s.2),
    have ∀(s s' : loop_4_state), loop_4 f s = some (inl s') → R s' s, from sorry,
    rewrite [@loop'_eq _ _ _ R _ this],
    rewrite [↑loop_4, ↑loop_4, ↑checked.shr],
    rewrite [of_int_one, pow_one],
    have length s / 2 ≤ length s, from !nat.div_le_self,
    rewrite [split_at_eq s this, ▸*, is_empty_eq, ▸*],
    --apply generalize_with_eq (dropn (length s / 2) s),
    cases dropn (length s / 2) s with x xs,
    { rewrite [if_pos rfl], contradiction },
    { rewrite [if_neg (λHeq : _ :: _ = nil, list.no_confusion Heq)],
      have 0 < length (x :: xs), from lt_of_le_of_lt !zero_le (lt_add_succ (length xs) 0),
      rewrite [if_pos this, nth_zero],
      obtain ret Hret, from ex_some_of_neq_none (Hf_impl_term f x),
      begin
        cases ret with ord f,
        rewrite [▸*, Hret, ▸*],
        cases ord,
        { have 1 ≤ length (x :: xs), from succ_le_succ !zero_le,
          rewrite [RangeFrom_index_eq _ (RangeFrom.mk _) this],
          apply ih, rotate 1,
          { apply rfl },
          { rewrite [length_dropn, length_cons, ▸*, nat.add_sub_cancel], apply sorry } },
        { contradiction },
        { apply ih, rotate 1,
          { apply rfl },
          { calc length (firstn (length s / 2) s) ≤ length s / 2 : length_firstn_le
                                              ... < length s     : div_lt_of_ne_zero sorry },
        }
      end
    }
  end,
  apply generalize_with_eq (length s) (λl, this l base s),
end

lemma binary_search_by_terminates : binary_search_by s f ≠ none := !loop_4_term

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
