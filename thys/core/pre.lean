import data.nat data.list
import move

open bool
open eq.ops
open int
open nat
open option
open [notation] partial
open prod
open prod.ops
open sum

open option

notation `do` binder ` ← ` x `; ` r:(scoped f, option.bind f x) := r


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

    private definition R'.wf [trans_instance] [H : well_founded R] : well_founded R' :=
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

    protected noncomputable definition loop.fix [Hwf: well_founded R] (s : State) : option Res :=
    do x ← well_founded.fix F (inl s);
    sum.inr_opt x

    private noncomputable definition term_rel (s : State) :=
    if Hwf : well_founded R then loop.fix s ≠ none
    else false
  end

  noncomputable definition loop (s : State) : option Res :=
  if Hex : ∃ R, term_rel R s then
    @loop.fix (classical.some Hex) (classical.dite_else_false (classical.some_spec Hex)) s
  else none

  parameter {body}

  protected theorem loop.fix_eq
    {R : State → State → Prop}
    [Hwf_R : well_founded R]
    {s : State} :
    loop.fix R s = match body s with
    | inl s' := if R s' s then loop.fix R s' else none
    | inr r  := some r
    end :=
  begin
    rewrite [↑loop.fix, well_founded.fix_eq, ↑F at {2}],
    cases body s with s' r,
    { esimp,
      cases classical.prop_decidable (R s' s), esimp, esimp
    },
    { esimp }
  end

  private lemma fix_eq_fix
    {R₁ R₂ : State → State → Prop}
    [Hwf_R₁ : well_founded R₁] [well_founded R₂]
    {s : State}
    (Hterm₁ : loop.fix R₁ s ≠ none) (Hterm₂ : loop.fix R₂ s ≠ none) :
    loop.fix R₁ s = loop.fix R₂ s :=
  begin
    revert Hterm₁ Hterm₂,
    induction (well_founded.apply Hwf_R₁ s) with s acc ih,
    rewrite [↑loop.fix, well_founded.fix_eq (F R₁), well_founded.fix_eq (F R₂), ↑F at {2, 4}],
    cases body s with s' r,
    { esimp,
      cases classical.prop_decidable (R₁ s' s) with HR₁,
      { cases classical.prop_decidable (R₂ s' s) with HR₂ HnR₂,
        { esimp, intro Hterm₁ Hterm₂, apply ih _ HR₁ Hterm₁ Hterm₂ },
        { esimp, intro Hterm₁ Hterm₂, exfalso, apply Hterm₂ rfl }
      },
      { esimp, intro Hterm₁ Hterm₂, exfalso, apply Hterm₁ rfl }
    },
    { intros, apply rfl }
  end

  protected theorem loop.fix_eq_loop
    {R : State → State → Prop}
    [Hwf_R : well_founded R]
    {s : State}
    (Hterm : loop.fix R s ≠ none) :
    loop.fix R s = loop s :=
  have Hterm_rel : ∃ R, term_rel R s,
  begin
    existsi R,
    rewrite [↑term_rel, dif_pos _],
    assumption
  end,
  let R₀ := classical.some Hterm_rel in
  have well_founded R₀, from classical.dite_else_false (classical.some_spec Hterm_rel),
  have loop.fix R₀ s ≠ none, from dif_pos this ▸ classical.some_spec Hterm_rel,
  begin
    rewrite [↑loop, dif_pos Hterm_rel],
    apply fix_eq_fix Hterm this,
  end
end

-- lifting loop to partial body functions

section
  parameters {State Res : Type}
  parameters (body : State ⇀ State + Res)
  parameter (R : State → State → Prop)
  parameter [well_founded R]
  variable (s : State)

  private definition body' : State + option Res := match body s with
  | some (inl s') := inl s'
  | some (inr r)  := inr (some r)
  | none          := inr none
  end

  protected noncomputable definition loop'.fix :=
  do res ← loop.fix body' R s;
  res

  noncomputable definition loop' : option Res :=
  do res ← loop body' s;
  res

  parameters {body}

  protected theorem loop'.fix_eq :
    loop'.fix s = match body s with
    | some (inl s') := if R s' s then loop'.fix s' else none
    | some (inr r)  := some r
    | none          := none
    end :=
  begin
    rewrite [↑loop'.fix, loop.fix_eq, ↑body'],
    apply generalize_with_eq (body s),
    intro b, cases b with x',
    { intro, apply rfl },
    { intro, cases x' with s' r,
      { esimp, cases classical.prop_decidable (R s' s), esimp, esimp },
      esimp
    }
  end

  theorem loop'.fix_eq_loop' (Hterm : loop'.fix s ≠ none) :
    loop'.fix s = loop' s :=
  have loop.fix body' R s ≠ none,
  begin
    intro Hcontr,
    esimp [loop'.fix] at Hterm,
    apply (Hcontr ▸ Hterm) rfl
  end,
  begin
    rewrite [↑loop', ↑loop'.fix, loop.fix_eq_loop this]
  end
end

abbreviation u8 [parsing_only] := nat
abbreviation u16 [parsing_only] := nat
abbreviation u32 [parsing_only] := nat
abbreviation u64 [parsing_only] := nat
abbreviation usize [parsing_only] := nat

abbreviation slice [parsing_only] := list

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

  abbreviation slice._T_.slice_SliceExt.len {T : Type} (self : slice T) := some (list.length self)
  abbreviation slice._T_.slice_SliceExt.get_unchecked [parsing_only] {T : Type} (self : slice T) (index : usize) :=
  list.nth self index

  namespace ops
    structure FnOnce [class] (Args : Type) (Self : Type) (Output : Type) :=
    (call_once : Self → Args → option (Output))

    -- easy without mutable closures
    abbreviation FnMut [parsing_only] := FnOnce
    abbreviation Fn := FnOnce

    definition FnMut.call_mut [unfold_full] (Args : Type) (Self : Type) (Output : Type) [FnOnce : FnOnce Args Self Output] : Self → Args → option (Output × Self) := λself x,
      do y ← @FnOnce.call_once Args Self Output FnOnce self x;
      some (y, self)

    definition Fn.call (Args : Type) (Self : Type) (Output : Type) [FnMut : FnMut Args Self Output] : Self → Args → option Output := @FnOnce.call_once Args Self Output FnMut
  end ops
end core

open core.ops

definition fn [instance] {A B : Type} : FnOnce A (A → option B) B := ⦃FnOnce,
  call_once := id
⦄

notation `let` binder ` ← ` x `; ` r:(scoped f, f x) := r
