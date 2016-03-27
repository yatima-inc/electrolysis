import .pre
import ..core.export

open [class] classical
open core
open eq.ops
open nat
open option (some none)
open prod.ops

namespace option
  variables {A B : Type}

  theorem all.intro (P : A → Prop) {x x'} (Hxx' : x = some x') (HPx' : P x') : all P x :=
  begin
    cases x,
    { apply option.no_confusion Hxx' },
    { esimp,
      injection Hxx',
      apply (a_eq⁻¹ ▸ HPx') }
  end

  theorem bind_eq_some (f : A → option B) {x x' y} (Hxx' : x = some x') (Hfx' : f x' = some y) : bind f x = some y :=
  begin
    cases x,
    { apply option.no_confusion Hxx' },
    { esimp,
      injection Hxx',
      apply (a_eq⁻¹ ▸ Hfx') }
  end
end option 

theorem some_opt.ex {A : Type} {P : A → Prop} (x : A) (H : P x) : ∃y, some_opt P = some y ∧ P y :=
begin
  apply exists.intro (classical.some (exists.intro x H)),
  apply and.intro,
  { unfold [some_opt, dite],
    apply decidable.cases_on _,
    { esimp, intro, apply rfl },
    { intro H', exfalso, apply H' (exists.intro x H) }
  },
  { apply classical.some_spec }
end

open option

section
  parameters {A : Type}
  parameters {P Q : A → Prop} {R : A → A → Prop}
  parameters {s : A} {l : (A → option A) → A → option A}
  hypothesis (Hstart : P s)
  hypothesis (Hdoes_step : ∀s f, P s → l f s ≠ none)
  hypothesis (Hstep : ∀f s s', P s → l f s = f s' → P s')
  hypothesis (Hstop : ∀f s s', P s → l f s = some s' → Q s')
  hypothesis (Hwf_R : well_founded R)
  hypothesis (HR : ∀f s s', P s → l f s = some s' → R s' s)
  
  include Hwf_R

  theorem loop : option.all Q (fix_opt l s) :=
  have ∀(x : A), fix_opt.fix l R Hwf_R x ≠ none, from sorry,
  obtain R' (HR' : some_opt (fix_opt.wf_R l) = some R') (Hwf_R' : (fix_opt.wf_R l) R'),
  from some_opt.ex R (decidable.rec_on_true _ this),
  sorry /-
  begin
    clear H_obtain_from,
    apply option.all.intro,
    { apply bind_eq_some,
      { apply HR' },
      { unfold dite, apply decidable.rec_on, },
    }
  end -/
end

namespace core

structure ops.One' [class] (A : Type) extends num.One A, has_one A renaming one→one_one
structure ops.Add' [class] (A : Type) extends ops.Add A A A, has_add A renaming add→add'
structure cmp.PartialOrd' [class] (A : Type) extends cmp.PartialOrd A A, order_pair A

section
  parameters {Idx Res : Type}
  parameters [ops.One' Idx] [ops.Add' Idx] [cmp.PartialOrd' Idx] [iter.Step Idx]
  parameters [decidable_linear_order Idx] [add_group Idx]
  abbreviation State := Res × ops.Range Idx
  parameters {P : Idx → Res → Prop}
  parameters {l r : Idx} {res₀ : Res}
  parameters {body : (State → option State) → Idx → Res → ops.Range Idx → option State} {body' : Idx → Res → Res}
  hypothesis (Hstart : P l res₀)
  hypothesis (Hdoes_step : ∀f i res iter, l ≤ i → i < r → P i res → body f i res iter = f ((body' i res, iter)))
  hypothesis (Hstep : ∀i res, l ≤ i → i < r → P i res → P (i+1) (body' i res))

  definition variant (r : ops.Range Idx) := ops.Range.end_ r - ops.Range.start r
  
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
    apply loop,
    apply measure.wf (λr, ops.Range.end_ r - ops.Range.start r),
  end
end

end core
