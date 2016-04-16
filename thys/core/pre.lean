import data.nat
open bool
open eq.ops
open nat
open prod
open option
open prod.ops

namespace option
  variables {A B : Type}

  protected definition all [unfold 3] {A : Type} (P : A → Prop) : option A → Prop
  | (some x) := P x
  | none     := false

  protected definition bind [unfold 4] {A B : Type} (f : A → option B) : option A → option B
  | (some x) := f x
  | none     := none

  theorem all.intro (P : A → Prop) {x x'} (Hxx' : x = some x') (HPx' : P x') : option.all P x :=
  begin
    cases x,
    { apply option.no_confusion Hxx' },
    { esimp,
      injection Hxx',
      apply (a_eq⁻¹ ▸ HPx') }
  end

  theorem bind_eq_some {f : A → option B} {x x' y} (Hxx' : x = some x') (Hfx' : f x' = some y) : option.bind f x = some y :=
  begin
    cases x,
    { apply option.no_confusion Hxx' },
    { esimp,
      injection Hxx',
      apply (a_eq⁻¹ ▸ Hfx') }
  end

  theorem neq_none_of_eq_some {A : Type} {x : option A} {y : A} (H : x = some y) : x ≠ none :=
  begin
    cases x,
    { apply option.no_confusion H },
    { apply not.intro, apply option.no_confusion }
  end
end option

open option

notation `do` binder ` ← ` x `; ` r:(scoped f, option.bind f x) := r

open [class] classical

section
  parameters {State : Type}

  inductive loop.control := continue | break

  parameters (body : State → State × loop.control)
  variable (R : State → State → Prop)

  noncomputable definition loop.F (s : State) (f : Π (s' : State), R s' s → option State) : option State :=
  match body s with
  | (s', loop.control.continue) := if H : R s' s then f s' H else none
  | (s', loop.control.break)    := some s'
  end

  noncomputable definition loop.fix (Hwf: well_founded R) (s : State) : option State :=
  well_founded.fix (loop.F R) s

  noncomputable definition loop.wf_R :=
  ∃Hwf : well_founded R, ∀s : State, loop.fix R Hwf s ≠ none

  noncomputable definition loop (s : State) : option State :=
  if Hex : ∃R, loop.wf_R R then
    let R := classical.some Hex in
    loop.fix R (classical.some (classical.some_spec Hex)) s
  else none

  /-theorem loop_inv
    {A : Type}
    (P Q : A → Prop) {R : A → A → Prop}
    {s : A} {l : (A → option A) → A → option A}
    (Hstart : P s)
    (Hdoes_step : ∀s f, P s → ∃s', l f s = some s' ∨ l f s = f s')
    (Hstep : ∀f s s', P s → l f s = f s' → P s')
    (Hstop : ∀f s s', P s → l f s = some s' → Q s')
    (Hwf_R : well_founded R)
    (HR : ∀f s s', P s → l f s = some s' → R s' s) :
    option.all Q (fix_opt l s) :=-/

  theorem loop_eq
    [Hwf_R : well_founded R]
    (HR : ∀s s', body s = (s', loop.control.continue) → R s' s)
    (s : State) :
    loop s = match body s with
    | (s', continue) := loop s'
    | (s', break)    := some s'
    end :=
  have Hex : ∃R, loop.wf_R R,
  begin
    apply exists.intro R,
    apply exists.intro Hwf_R,
    intro s,
    exact @well_founded.induction State R Hwf_R _ s
    (begin
      intro s' Hind,
      rewrite [↑loop.fix, well_founded.fix_eq, ↑loop.F],
      note HR' := HR s',
      revert HR',
      cases body s' with s'' c,
      intro HR',
      cases c,
      { rewrite [dif_pos (HR' s'' rfl)],
        apply Hind _ (HR' s'' rfl) },
      { contradiction }
    end)
  end,
  /-obtain R' (HR' : some_opt loop.wf_R = some R') (Hloop_wf_R' : loop.wf_R R'),
  from some_opt.ex R (decidable.rec_on_true _ this),-/
  begin
    cases body s,
    rewrite [↑loop, ↑loop.fix, dif_pos Hex, dif_pos Hex],
  end
    /-note Hwf_R' := dite_else_false Hloop_wf_R',
    rewrite [↑loop, HR', ▸*, dif_pos Hwf_R'],
    rewrite [↑loop.fix, well_founded.fix_eq, ↑loop.F],
    apply (congr_arg (prod.cases_on (body s))),
    apply funext, intro s',
    have R' s' s, from sorry,
    rewrite [dif_pos this, dif_pos Hwf_R'],
  end-/
end

abbreviation u8 := nat
abbreviation u16 := nat
abbreviation u32 := nat
abbreviation u64 := nat
abbreviation usize := nat

definition checked.sub (n : nat) (m : nat) :=
if n ≥ m then some (n-m) else none

definition checked.div (n : nat) (m : nat) :=
if m ≠ 0 then some (mod n m) else none

definition checked.mod (n : nat) (m : nat) :=
if m ≠ 0 then some (mod n m) else none

definition intrinsics.add_with_overflow (n : nat) (m : nat) := some (n + m, false)

definition core.mem.swap {A : Type} (x y : A) := some (unit.star,y,x)
