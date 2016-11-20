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

    hypothesis [decidable_rel R]

    private definition R'.dec [instance] : decidable_rel R' :=
    begin
      intro x' x,
      cases x',
      { cases x,
        { apply (_ : decidable_rel R) },
        { apply decidable_false }
      },
      { apply decidable_false }
    end

    private definition R'.wf [instance] [H : well_founded R] : well_founded R' :=
    let f := sum.rec some (λr, none) in
    have subrelation R' (partial.inv_image R f),
    begin
      intro x y R'xy,
      cases x, cases y,
      repeat (apply R'xy),
    end,
    subrelation.wf this (partial.inv_image.wf f H)

    private definition F (x : State') (f : Π (x' : State'), R' x' x → sem State') : sem State' :=
    do s ← sem.lift_opt (sum.inl_opt x);
    dostep x' ← body s;
    match x' with
    | inr r := return (inr r)
    | x'    := if H : R' x' x then f x' H else mzero
    end

    protected definition loop.fix [irreducible] [Hwf: well_founded R] (s : State) : sem Res :=
    do x ← well_founded.fix F (inl s);
    sem.lift_opt (sum.inr_opt x)

    private abbreviation terminating (s : State) :=
    ∃ Hwf : well_founded R, loop.fix s ≠ mzero
  end

  noncomputable definition loop [irreducible] (s : State) : sem Res :=
  if Hex : ∃ R, terminating R s then
    @loop.fix (classical.some Hex) _ (classical.some (classical.some_spec Hex)) s
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
    { esimp [R'.dec],
      cases classical.prop_decidable (R s' s), esimp, esimp },
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
      { esimp [R'.dec], cases classical.prop_decidable (R₁ s' s) with HR₁,
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
  have term : ∃ R, terminating R s, from exists.intro R (exists.intro Hwf_R Hterm),
  let R₀ := classical.some term in
  begin
    cases classical.some_spec term with wf_R₀ term_R₀,
    rewrite [↑loop, dif_pos term],
    apply fix_eq_fix Hterm term_R₀,
  end

  protected theorem loop.terminates_with
    {R : State → State → Prop}
    [Hwf_R : well_founded R]
    (s : State)
    (p : State → Prop)
    (q : Res → Prop)
    (start : p s)
    (step : ∀ s, p s → match body s with
      | some (inl s', _) := p s' ∧ R s' s
      | some (inr r, _)  := q r
      | none := false
      end) :
    sem.terminates_with q (loop s) :=
  have ∀ s, p s → sem.terminates_with q (loop.fix R s),
  begin
    intro s hp,
    induction (well_founded.apply Hwf_R s) with s₀ acc ih,
    rewrite [loop.fix_eq],
    note step := step s₀ hp,
    revert step,
    cases body s₀ with x,
    { contradiction },
    { cases x with st' k,
      cases st' with s' r,
      { esimp,
        intro inv, cases inv,        
        rewrite [if_pos `R s' s₀`],
        apply sem.terminates_with_incr,
        apply sem.terminates_with_incr,
        apply ih, repeat assumption
      },
      { apply id }
    }
  end,
  have t : sem.terminates_with q (loop.fix R s), from this s start,
  have loop.fix R s ≠ mzero,
  begin
    revert t,
    cases loop.fix R s,
    { contradiction },
    { contradiction }
  end,
  begin
    rewrite [-loop.fix_eq_loop this],
    apply t,
  end
end

section
  open topology
  open asymptotic
  open prod.ops

  protected theorem loop.terminates_with_in_ub
    {In State Res : Type₁}
    (citer : ℕ → ℕ)
    (p : In → State → State → Prop)
    (pre : In → State → Prop)
    (q : In → State → Res → Prop)
    (miter : State → ℕ)
    (mbody : In → State → ℕ)
    (aiter abody : ℕ → ℕ)
    (body : In → State → sem (State + Res))
    (citer_aiter : citer ∈ 𝓞(aiter) [at ∞] ∩ Ω(1) [at ∞])
    (pre_p : ∀ args s, pre args s → p args s s)
    (step : ∃₀ f ∈ 𝓞(abody) [at ∞] ∩ Ω(1) [at ∞], ∀ args init s, pre args init → p args init s →
      sem.terminates_with_in (λ x, match x with
        | inl s' := p args init s' ∧ citer (miter s') < citer (miter s)
        | inr r  := q args init r
        end) (f (mbody args init)) (body args s)) :
    ∃₀ f ∈ 𝓞(λ p, aiter p.1 * abody p.2) [at ∞ × ∞], ∀ args s, pre args s →
      sem.terminates_with_in (q args s) (f (miter s, mbody args s)) (loop (body args) s) :=
    begin
      cases step with cbody step,
      cases step with cbody_abody step,
      existsi λ p, (citer p.1 + 1) * (cbody p.2 + 1),
      split,
      { apply ub_mul_prod_filter
          (and.left $ ub_add_const citer_aiter)
          (and.left $ ub_add_const cbody_abody) },
      { intro args init hpre,
        esimp,
        let R := measure (citer ∘ miter),
        have well_founded R, from measure.wf _,
        have ∀ s, p args init s → sem.terminates_with_in (q args init)
          ((citer (miter s) + 1) * (cbody (mbody args init) + 1))
          (loop.fix (body args) R s),
        begin
          intro s₀ hp,
          induction well_founded.apply `well_founded R` s₀ with s acc ih,
          rewrite loop.fix_eq,
          note step' := step args init s hpre hp,
          clear step,
          cases step' with ret x k h_eq h hk,
          cases x with s' r,
          { cases h with hps' var,
            note ih' := ih s' var hps',
            clear acc ih,
            rewrite [h_eq, ▸*, incr_incr, if_pos (show R s' s, from var)],
            revert var,
            cases citer (miter s) with i,
            { intro var, exfalso, apply not_lt_zero _ var },
            { intro var,
              rewrite [succ_eq_add_one, nat.right_distrib, one_mul],
              have sem.terminates_with_in (q args init)
                ((i + 1) * (cbody (mbody args init) + 1) + (1 + k))
                (sem.incr (1 + k) (loop.fix (body args) (measure (citer ∘ miter)) s')),
              begin
                apply sem.terminates_with_in_incr,
                apply sem.terminates_with_in.imp ih',
                { intros, assumption },
                { apply nat.mul_le_mul (nat.add_le_add_right (nat.le_of_succ_le_succ var) _) !le.refl },
              end,
              apply sem.terminates_with_in.imp this,
              { intros, assumption },
              { apply nat.add_le_add_left,
                rewrite nat.add_comm,
                apply nat.add_le_add_right hk }
            }
          },
          { esimp at h,
            rewrite [h_eq, ▸*],
            apply sem.terminates_with_in.mk rfl,
            { apply h },
            { rewrite [zero_add, nat.right_distrib, one_mul],
              apply le_add_of_le_left,
              apply nat.add_le_add_right hk,
            }
          }
        end,
        have sem.terminates_with_in (q args init)
          ((citer (miter init) + 1) * (cbody (mbody args init) + 1))
          (loop.fix (body args) R init), from this init (pre_p args init hpre),
        rewrite [-loop.fix_eq_loop (show loop.fix (body args) R init ≠ mzero,
          begin
            revert this,
            intro t, cases t with ret x k hq hk ht,
            intro contr, rewrite contr at hq, contradiction
          end)],
        apply this,
      }
    end
end
