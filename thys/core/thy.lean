import core.generated

open [class] classical
open core
open eq.ops
open nat
open option
open prod.ops

namespace core

open ops

namespace slice

open _T_.SliceExt

/- fn binary_search_by<T, F: FnMut(&T) -> Ordering>(self: &[T], f: F) -> Result<usize, usize> -/
lemma binary_search_by_terminates {T F : Type} (s : slice T) (f : F) [f_impl : FnMut T F cmp.Ordering]
  (Hf_impl_term: Πf x, @FnMut.call_mut _ _ _ f_impl f x ≠ none) :
  binary_search_by s f ≠ none :=
begin
  esimp [binary_search_by]
end

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
