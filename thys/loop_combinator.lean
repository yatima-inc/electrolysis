import sem
import asymptotic

open eq.ops
open [notation] function
open nat
open option
open [notation] partial
open [notation] set
open sum

open [class] classical

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
    do s ← sem.lift_opt (sum.inl_opt x);
    dostep x' ← body s;
    match x' with
    | inr r := return (inr r)
    | x'    := if H : R' x' x then f x' H else mzero
    end

    protected noncomputable definition loop.fix [irreducible] [Hwf: well_founded R] (s : State) : sem Res :=
    do x ← well_founded.fix F (inl s);
    sem.lift_opt (sum.inr_opt x)

    private noncomputable definition term_rel (s : State) :=
    if Hwf : well_founded R then loop.fix s ≠ mzero
    else false
  end

  noncomputable definition loop [irreducible] (s : State) : sem Res :=
  if Hex : ∃ R, term_rel R s then
    @loop.fix (classical.some Hex) (classical.dite_else_false (classical.some_spec Hex)) s
  else mzero

  parameter {body}

  protected theorem loop.fix_eq
    {R : State → State → Prop}
    [Hwf_R : well_founded R]
    {s : State} :
    loop.fix R s = dostep x' ← body s; match x' with
    | inl s' := if R s' s then loop.fix R s' else mzero
    | inr r  := return r
    end :=
  begin
    rewrite [↑loop.fix, well_founded.fix_eq, ↑F at {2}, return_bind, -incr_bind, bind.assoc],
    apply congr_arg (sem.incr 1), apply congr_arg (sem.bind (body s)), apply funext, intro x',
    cases x' with s' r,
    { esimp,
      cases classical.prop_decidable (R s' s), esimp, esimp
    },
    { esimp }
  end

  private lemma fix_eq_fix
    {R₁ R₂ : State → State → Prop}
    [Hwf_R₁ : well_founded R₁] [well_founded R₂]
    {s : State}
    (Hterm₁ : loop.fix R₁ s ≠ sem.zero) (Hterm₂ : loop.fix R₂ s ≠ sem.zero) :
    loop.fix R₁ s = loop.fix R₂ s :=
  begin
    revert Hterm₁ Hterm₂,
    induction (well_founded.apply Hwf_R₁ s) with s acc ih,
    rewrite [↑loop.fix, well_founded.fix_eq (F R₁), well_founded.fix_eq (F R₂), ↑F at {2, 4},
      +return_bind],
    cases body s with x',
    { intros, apply rfl },
    { esimp,
      cases x' with st k, cases st with s' r,
      { esimp, cases classical.prop_decidable (R₁ s' s) with HR₁,
        { cases classical.prop_decidable (R₂ s' s) with HR₂ HnR₂,
          { esimp,
            rewrite [-+incr_bind],
            intro Hterm₁ Hterm₂,
            apply congr_arg (sem.incr 1),
            have loop.fix R₁ s' = loop.fix R₂ s',
            begin
              apply ih _ HR₁,
              unfold loop.fix; exact neq_mzero_of_incr_neq_mzero (neq_mzero_of_incr_neq_mzero Hterm₁),
              unfold loop.fix; exact neq_mzero_of_incr_neq_mzero (neq_mzero_of_incr_neq_mzero Hterm₂)
            end,
            note ih' := congr_arg (sem.incr k) this,
            rewrite [↑loop.fix at ih'],
            exact ih'
          },
          { esimp, intro Hterm₁ Hterm₂, exfalso, apply Hterm₂ rfl }
        },
        { esimp, intro Hterm₁ Hterm₂, exfalso, apply Hterm₁ rfl }
      },
      { intros, exact rfl }
    },
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
  have term_rel R₀ s, from classical.some_spec Hterm_rel,
  have loop.fix R₀ s ≠ none, begin
    rewrite [↑term_rel at this {2}, dif_pos `well_founded R₀` at this],
    apply this,
  end,
  begin
    rewrite [↑loop, dif_pos Hterm_rel],
    apply fix_eq_fix Hterm this,
  end

  /-protected theorem loop.terminates_with
    {R : State → State → Prop}
    [Hwf_R : well_founded R]
    (s : State)
    (p : State → Prop)
    (q : Res → Prop)
    (start : p s)
    (inv : ∀ s s', p s → sem.terminates_with (λ x, x = inl s') (body s) → p s' ∧ R s s')
    (fin : ∀ s r, p s → sem.terminates_with (λ x, x = inr r) (body s) → q r) :
    sem.terminates_with q (loop s)

  section
    open topology
    open asymptotic
    open prod.ops

    parameters 
      {R : State → State → Prop}
      [Hwf_R : well_founded R]
      (p : State → State → Prop)
      (q : State → Res → Prop)

    include State Res body R p q
    structure loop.state_terminates_with_in_ub (init : State) (ub₁ ub₂ : ℕ) : Prop :=
    (start : p init init)
    (inv : ∀ s s', p init s →
      sem.terminates_with_in (λ x, x = inl s') ub₁ (body s) → p init s' ∧ R s s')
    (fin : ∀ s r, p init s → sem.terminates_with_in (λ x, x = inr r) ub₂ (body s) → q init r)

    protected theorem loop.terminates_with_in_ub
      (c₁ c₂ : State → ℕ)
      (asym₁ asym₂ : ℕ → ℕ)
      (h : ∀ s, ∃₀ f₁ ∈ 𝓞(asym₁) [at ∞], ∃₀ f₂ ∈ 𝓞(asym₂) [at ∞],
        @loop.state_terminates_with_in_ub _ _ body R p q s (f₁ (c₁ s)) (f₂ (c₂ s))) :
      ∀ s, ∃₀ f ∈ 𝓞(λ p, asym₁ p.1 * asym₂ p.2) [at ∞ × ∞],
        sem.terminates_with_in (q s) (f (c₁ s, c₂ s)) (loop s)
  end-/
end
