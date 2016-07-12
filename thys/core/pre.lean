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

open [class] classical

-- fix semantics monad
definition sem (a : Type₁) := option (a × nat)

definition sem.incr {a : Type₁} : sem a → sem a
| (some (x, k)) := some (x, k+1)
| none          := none

definition sem.return {a : Type₁} (x : a) : sem a := some (x, 0)
definition sem.bind {a b : Type₁} (m : sem a) (f : a → sem b) : sem b :=
option.bind m (λs, match s with
| (x, k) :=
  option.bind (f x) (λs', match s' with
  | (x', k') := some (x', k+k')
  end)
end)
definition sem.zero {a : Type₁} : sem a := none

definition sem.is_monad_zero [instance] [constructor] : monad_zero sem :=
monad_zero.mk @sem.return @sem.bind @sem.zero

-- TODO: move into monad class
attribute sem.bind [unfold 3]
lemma bind_return {A B : Type₁} {a : A} {f : A → sem B} : (return a >>= f) = f a :=
begin
  rewrite [▸*, ↑sem.return],
  cases f a with a',
  { esimp },
  { cases a', rewrite [▸*, !zero_add] }
end

lemma bind.assoc {A B C : Type₁} {m : sem A} {f : A → sem B} {g : B → sem C} :
  (m >>= f >>= g) = (m >>= (λx, f x >>= g)) :=
begin
  cases m with m',
  { esimp },
  { cases m' with a k, esimp, cases f a with m'',
    { esimp },
    { cases m'' with a' k', esimp, cases g a' with m''',
      { esimp },
      { esimp, apply prod.cases_on, intros, rewrite [▸*, add.assoc] }
    }
  }
end

attribute sem [irreducible]

notation `dostep` binder ` ← ` x `; ` r:(scoped f, sem.incr (sem.bind x f)) := r

-- a general loop combinator for separating tail-recursive definitions from their well-foundedness proofs

section
  parameters {State Res : Type₁}
  parameters (body : State → sem (State + Res))

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

    private noncomputable definition F (x : State') (f : Π (x' : State'), R' x' x → sem State') : sem State' :=
    do s ← monad_zero.of_option (sum.inl_opt x);
    dostep x' ← body s;
    match x' with
    | inr r := monad.ret sem (inr r)
    | x'    := if H : R' x' x then f x' H else mzero
    end

    protected noncomputable definition loop.fix [Hwf: well_founded R] (s : State) : sem Res :=
    do x ← well_founded.fix F (inl s);
    monad_zero.of_option (sum.inr_opt x)

    private noncomputable definition term_rel (s : State) :=
    if Hwf : well_founded R then loop.fix s ≠ mzero
    else false
  end

  noncomputable definition loop (s : State) : sem Res :=
  if Hex : ∃ R, term_rel R s then
    @loop.fix (classical.some Hex) (classical.dite_else_false (classical.some_spec Hex)) s
  else mzero

  parameter {body}

  protected theorem loop.fix_eq
    {R : State → State → Prop}
    [Hwf_R : well_founded R]
    {s : State} :
    loop.fix R s = do x' ← body s; match x' with
    | inl s' := sem.incr (if R s' s then loop.fix R s' else mzero)
    | inr r  := return r
    end :=
  begin
    rewrite [↑loop.fix, well_founded.fix_eq, ↑F at {2}, bind_return, bind.assoc],
    apply congr_arg (monad.bind (body s)), apply funext, intro x',
    cases x' with s' r,
    { esimp,
      cases classical.prop_decidable (R s' s), esimp, esimp
    },
    { esimp }
  end

  /-private lemma fix_eq_fix
    {R₁ R₂ : State → State → Prop}
    [Hwf_R₁ : well_founded R₁] [well_founded R₂]
    {s : State}
    (Hterm₁ : loop.fix R₁ s ≠ mzero) (Hterm₂ : loop.fix R₂ s ≠ mzero) :
    loop.fix R₁ s = loop.fix R₂ s :=
  begin
    revert Hterm₁ Hterm₂,
    induction (well_founded.apply Hwf_R₁ s) with s acc ih,
    rewrite [↑loop.fix, well_founded.fix_eq (F R₁), well_founded.fix_eq (F R₂), ↑F at {2, 4},
      +bind_return],
    now,
    apply congr_arg (monad.bind (body s)), apply funext, intro x',
    cases x' with s' r,
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
    (Hterm : loop.fix R s ≠ mzero) :
    loop.fix R s = loop s :=
  have Hterm_rel : ∃ R, term_rel R s,
  begin
    existsi R,
    rewrite [↑term_rel, dif_pos _],
    assumption
  end,
  let R₀ := classical.some Hterm_rel in
  have well_founded R₀, from classical.dite_else_false (classical.some_spec Hterm_rel),
  have loop.fix R₀ s ≠ nonterm, from dif_pos this ▸ classical.some_spec Hterm_rel,
  begin
    rewrite [↑loop, dif_pos Hterm_rel],
    apply fix_eq_fix Hterm this,
  end-/
end

abbreviation u8 [parsing_only] := nat
abbreviation u16 [parsing_only] := nat
abbreviation u32 [parsing_only] := nat
abbreviation u64 [parsing_only] := nat
abbreviation usize [parsing_only] := nat

abbreviation slice [parsing_only] := list

definition checked.sub (x y : nat) : sem nat :=
if x ≥ y then return (x-y) else mzero

definition checked.div (x y : nat) : sem nat :=
if y ≠ 0 then return (div x y) else mzero

definition checked.mod (x y : nat) : sem nat :=
if y ≠ 0 then return (mod x y) else mzero

/- TODO: actually check something -/
definition checked.shl (x y : nat) : sem nat := return (x * 2^y)
definition checked.shr (x : nat) (y : int) : sem nat := return (div x (2^nat.of_int y))

namespace core
  abbreviation intrinsics.add_with_overflow (x y : nat) : sem (nat × Prop) := return (x + y, false)

  abbreviation mem.swap {T : Type₁} (x y : T) : sem (unit × T × T) := return (unit.star,y,x)

  abbreviation slice._T_.slice_SliceExt.len {T : Type₁} (self : slice T) : sem nat :=
  return (list.length self)
  definition slice._T_.slice_SliceExt.get_unchecked {T : Type₁} (self : slice T) (index : usize)
    : sem T :=
  option.rec mzero return (list.nth self index)

  namespace ops
    structure FnOnce [class] (Args : Type₁) (Self : Type₁) (Output : Type₁) :=
    (call_once : Self → Args → sem Output)

    -- easy without mutable closures
    abbreviation FnMut [parsing_only] := FnOnce
    abbreviation Fn := FnOnce

    definition FnMut.call_mut [unfold_full] (Args : Type₁) (Self : Type₁) (Output : Type₁)
      [FnOnce : FnOnce Args Self Output] : Self → Args → sem (Output × Self) := λself x,
      do y ← @FnOnce.call_once Args Self Output FnOnce self x;
      return (y, self)

    definition Fn.call (Args : Type₁) (Self : Type₁) (Output : Type₁)
      [FnMut : FnMut Args Self Output] : Self → Args → sem Output := FnOnce.call_once Output
  end ops
end core

open core.ops

definition fn [instance] {A B : Type₁} : FnOnce A (A → sem B) B := ⦃FnOnce,
  call_once := id
⦄

notation `let` binder ` ← ` x `; ` r:(scoped f, f x) := r
