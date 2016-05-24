import data.nat data.list

open bool
open eq.ops
open int
open nat
open option
open prod
open prod.ops
open sum

-- things that may or may not belong in the stdlib

namespace nat
  definition of_int : ℤ → ℕ
  | (int.of_nat n) := n
  | _              := 0

  lemma of_int_one : of_int 1 = 1 := rfl
end nat

namespace option
  variables {A B : Type}

  protected definition all [unfold 3] {A : Type} (P : A → Prop) : option A → Prop
  | (some x) := P x
  | none     := false

  theorem ex_some_of_neq_none {x : option A} (H : x ≠ none) : ∃y, x = some y :=
  begin
    cases x with y,
    { exfalso, apply H rfl },
    { existsi y, apply rfl }
  end

  protected definition bind [unfold 4] {A B : Type} (f : A → option B) : option A → option B
  | (some x) := f x
  | none     := none

  theorem bind_neq_none {f : A → option B} {x} (Hx : x ≠ none) (Hf : ∀x', f x' ≠ none) : option.bind f x ≠ none :=
  obtain x' H₁, from ex_some_of_neq_none Hx,
  obtain x'' H₂, from ex_some_of_neq_none (Hf x'),
  by rewrite [H₁, ▸*, H₂]; contradiction
end option

open option

notation `do` binder ` ← ` x `; ` r:(scoped f, option.bind f x) := r

definition sum.inl_opt [unfold 3] {A B : Type} : A + B → option A
| (inl a) := some a
| (inr _) := none

definition sum.inr_opt {A B : Type} : A + B → option B
| (inl _) := none
| (inr b) := some b


namespace partial
infixr ` ⇀ `:25 := λA B, A → option B

section
  parameters {A B : Type} {R : B → B → Prop}
  parameters (f : A ⇀ B)

  definition R' [unfold 3] : option B → option B → Prop
  | (some y) (some x) := R y x
  | _        _        := false

  private definition R'.wf (H : well_founded R) : well_founded R' :=
  begin
    apply well_founded.intro,
    intro x, cases x with x',
    { apply acc.intro,
      intro y,
      cases y; repeat contradiction },
    { induction (well_founded.apply H x') with x' _ ih,
      apply acc.intro,
      intro y HR', cases y with y',
      { contradiction },
      { apply ih _ HR' }
    }
  end

  parameter (R)
  definition inv_image (f : A ⇀ B) : A → A → Prop := inv_image R' f

  parameter {R}
  lemma inv_image.wf (H : well_founded R) : well_founded (inv_image f) :=
  inv_image.wf f (R'.wf H)
end

end partial

open [notation] partial

lemma generalize_with_eq {A : Type} {P : A → Prop} (x : A) (H : ∀y, x = y → P y) : P x := H x rfl

open [class] classical

-- a general loop combinator for separating tail-recursive definitions from their well-foundedness proofs

section
  parameters {State Res : Type}
  parameters (body : State → State + Res)

  section
    parameter (R : State → State → Prop)

    private definition State' := State + Res

    private definition R' [unfold 4] : State' → State' → Prop
    | (inl s') (inl s) := R s' s
    | _        _       := false

    private definition R'.wf (H : well_founded R) : well_founded R' :=
    let f := sum.rec some (λr, none) in
    have subrelation R' (partial.inv_image R f),
    begin
      intro x y R'xy,
      cases x, cases y,
      repeat (apply R'xy),
    end,
    subrelation.wf this (partial.inv_image.wf f H)

    private noncomputable definition F (x : State') (f : Π (x' : State'), R' x' x → option State') : option State' :=
    do s ← sum.inl_opt x;
    match body s with
    | inr r := some (inr r)
    | x'    := if H : R' x' x then f x' H else none
    end

    private noncomputable definition fix (Hwf: well_founded R) (s : State) : option Res :=
    have well_founded R', from R'.wf Hwf,
    do x ← well_founded.fix F (inl s);
    sum.inr_opt x

    private definition term_rel :=
    well_founded R ∧ ∀s s' : State, body s = inl s' → R s' s
  end

  noncomputable definition loop (s : State) : option Res :=
  if Hex : Exists term_rel then
    fix (classical.some Hex) (and.left (classical.some_spec Hex)) s
  else none

  parameter {body}

  theorem loop_eq
    {R : State → State → Prop}
    [well_founded R]
    (HR : ∀s s', body s = inl s' → R s' s)
    {s : State} :
    loop s = match body s with
    | inl s' := loop s'
    | inr r  := some r
    end :=
  have Hterm_rel : Exists term_rel, from exists.intro R (and.intro _ HR),
  let R'₀ := R' (classical.some Hterm_rel) in
  have well_founded R'₀, from R'.wf _ (and.left (classical.some_spec Hterm_rel)),
  begin
    apply generalize_with_eq (body s),
    intro b Heq, cases b with s' r,
    { rewrite [↑loop, ↑fix, +dif_pos Hterm_rel],
      have Hin_R' : R'₀ (inl s') (inl s), from
        and.right (classical.some_spec Hterm_rel) s s' Heq,
      rewrite [well_founded.fix_eq, ↑F at {2}, Heq, ▸*, dif_pos Hin_R'] },
    { rewrite [↑loop, ↑fix, dif_pos Hterm_rel],
      rewrite [well_founded.fix_eq, ↑F at {2}, Heq, ▸*] }
  end
end

-- lifting loop to partial body functions

section
  parameters {State Res : Type}
  parameters (body : State ⇀ State + Res)

  private definition body' (s : State) : State + option Res := match body s with
  | some (inl s') := inl s'
  | some (inr r)  := inr (some r)
  | none          := inr none
  end

  noncomputable definition loop' (s : State) : option Res :=
  do res ← loop body' s;
  res

  theorem loop'_eq
    {R : State → State → Prop}
    [well_founded R]
    (HR : ∀s s', body s = some (inl s') → R s' s)
    {s : State} :
    loop' s = match body s with
    | some (inl s') := loop' s'
    | some (inr r)  := some r
    | none          := none
    end :=
  have ∀s s', body' s = inl s' → R s' s,
  begin
    intro s s' H,
    apply HR s s',
    esimp [body'] at H,
    revert H,
    cases body s with x,
    { contradiction },
    { cases x with s'₂ r,
      { intro H,
        injection H with s'_eq,
        rewrite s'_eq },
      { contradiction },
    }
  end,
  begin
    rewrite [↑loop', loop_eq this, ↑body'],
    rewrite [↑body'], --?
    apply generalize_with_eq (body s), -- I don't actually use Heq, but `cases body s` did not replace all occurences
    intro b Heq, cases b with x,
    { esimp },
    { cases x, repeat esimp }
  end
end

abbreviation u8 := nat
abbreviation u16 := nat
abbreviation u32 := nat
abbreviation u64 := nat
abbreviation usize := nat

abbreviation slice := list

definition checked.sub (n : nat) (m : nat) :=
if n ≥ m then some (n-m) else none

definition checked.div (n : nat) (m : nat) :=
if m ≠ 0 then some (mod n m) else none

definition checked.mod (n : nat) (m : nat) :=
if m ≠ 0 then some (mod n m) else none

/- TODO: actually check something -/
definition checked.shl (n : nat) (m : nat) := some (n * 2^m)
definition checked.shr (n : nat) (m : int) := some (div n (2^nat.of_int m))

namespace core
  abbreviation intrinsics.add_with_overflow (n : nat) (m : nat) := some (n + m, false)

  abbreviation mem.swap {T : Type} (x y : T) := some (unit.star,y,x)

  abbreviation slice._T_.SliceExt.len {T : Type} (self : slice T) := some (list.length self)
  abbreviation slice._T_.SliceExt.get_unchecked [parsing_only] {T : Type} (self : slice T) (index : usize) :=
  list.nth self index
end core

notation `let` binder ` ← ` x `; ` r:(scoped f, f x) := r
