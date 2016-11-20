import theories.topology.limit
import move

open eq.ops
open function
open nat
open prod.ops
open set
open set.filter
open topology

lemma eventually_of_always {A : Type} {F : filter A} {P : A → Prop} (H : ∀a, P a) : eventually P F :=
eventually_mono (eventually_true F) (λa Ha, H a)

attribute set_of [unfold_full]

definition fun_has_add [instance] (A B : Type) [has_add B] : has_add (A → B) :=
has_add.mk (λf g x, f x + g x)

namespace asymptotic
  -- single parameter:
  --definition ub (f : ℕ → ℕ) : set (ℕ → ℕ) :=
  --λg, ∃c n₀, ∀n, n ≥ n₀ → f n ≤ c * g n

  section
    parameters {A : Type} (F : filter A)
    variables  (e f g : A → ℕ)

    protected definition le : Prop := ∃c, eventually {a | f a ≤ c * g a} F
    protected definition lt : Prop := ∀c, eventually {a | c * f a ≤ g a} F
    protected definition equiv : Prop := le f g ∧ le g f

    definition ub  := {f | le f g}
    definition sub := {f | lt f g}
    definition lb  := {f | le g f}
    definition slb := {f | lt g f}

    parameters {F}
    variables {e f g}

    protected lemma le.refl [refl] : le f f := begin
      existsi 1,
      apply eventually_mono (eventually_true F),
      intros a _,
      esimp,
      rewrite one_mul,
    end

    protected lemma le.trans [trans] : le e f → le f g → le e g :=
    take He Hf,
    obtain c₁ Hc₁, from He,
    obtain c₂ Hc₂, from Hf,
    exists.intro (c₁ * c₂) (eventually_mono (eventually_and Hc₁ Hc₂) (
      take a Ha,
      calc e a ≤ c₁ * f a        : and.left Ha
          ... ≤ c₁ * (c₂ * g a) : mul_le_mul_left c₁ (and.right Ha)
          ... = c₁ *  c₂ * g a  : mul.assoc))

    protected lemma lt_of_lt_of_le : lt e f → le f g → lt e g :=
    take He Hf c,
    obtain c₂ Hc₂, from Hf,
    eventually_mono (eventually_and (He ((c₂ + 1) * c)) Hc₂) (
      take a Ha,
      have (c₂ + 1) * (c * e a) ≤ (c₂ + 1) * g a, from calc
        (c₂ + 1) * (c * e a) = (c₂ + 1) * c * e a : mul.assoc
                         ... ≤ f a                : and.left Ha
                         ... ≤ c₂ * g a           : and.right Ha
                         ... ≤ (c₂ + 1) * g a     : mul_le_mul_right _ !le_succ,
      le_of_mul_le_mul_left this !zero_lt_succ)

    protected lemma le_of_lt : lt f g → le f g :=
    take Hf,
    have {a | 1 * f a ≤ g a} = {a | f a ≤ 1 * g a}, by rewrite [funext (λa, one_mul _) ],
    exists.intro 1 (this ▸ Hf 1)
  end

  notation `𝓞(` g `) ` F:max := ub F g
  notation `𝓸(` g `) ` F:max := sub F g
  notation `Ω(` g `) ` F:max := lb F g
  notation `ω(` g `) ` F:max := slb F g

  notation `Θ(` g `) ` := equiv g

  notation `𝓞(1` `) ` F:max := 𝓞(λx, 1) F
  notation `𝓸(1` `) ` F:max := 𝓸(λx, 1) F
  notation `Ω(1` `) ` F:max := Ω(λx, 1) F
  notation `ω(1` `) ` F:max := ω(λx, 1) F
  notation `Θ(1` `) ` F:max := Θ(λx, 1) F

  notation `[at ` `∞` ` × ` `∞]` := prod_filter [at ∞] [at ∞]

  variables {A : Type} {F F₁ F₂ : filter A} {f f₁ f₂ g : A → ℕ}

  lemma eventually_image_at_infty {f : ℕ → ℕ} {P : set ℕ} (H : eventually P [at ∞])
    (Hf : f ∈ ω(1) [at ∞]) : eventually {n | P (f n)} [at ∞] :=
  obtain n₀ (Hn₀ : ∀n, n ≥ n₀ → P n), from eventually_at_infty_dest H,
  eventually_mono (Hf n₀) (
    take n,
    suppose n₀ * 1 ≤ f n,
    show P (f n), from Hn₀ (f n) (mul_one _ ▸ this))

  lemma ub_subset_ub (Hf : f ∈ 𝓞(g) F) : 𝓞(f) F ⊆ 𝓞(g) F :=
  take e He,
  obtain c₁ Hc₁, from He,
  obtain c₂ Hc₂, from Hf,
  exists.intro (c₁ * c₂) (eventually_mono (eventually_and Hc₁ Hc₂) (
    take a Ha,
    calc e a ≤ c₁ * f a        : and.left Ha
         ... ≤ c₁ * (c₂ * g a) : mul_le_mul_left c₁ (and.right Ha)
         ... = c₁ *  c₂ * g a  : mul.assoc))

  -- TODO: can this work for arbitrary domains?
  lemma ub_comp_of_nondecreasing_of_ub {f₁ f₂ g₁ g₂ : ℕ → ℕ}
    (Hf₁ : f₁ ∈ 𝓞(g₁) [at ∞])
    (Hf₂ : f₂ ∈ 𝓞(g₂) [at ∞])
    (Hunb : f₂ ∈ ω(1) [at ∞]) -- the other case should also hold, but probably not that interesting
    (Hg₁ : ∀c, (λx, g₁ (c * x)) ∈ 𝓞(g₁) [at ∞])
    (Hmono : nondecreasing g₁) :
    f₁ ∘ f₂ ∈ 𝓞(g₁ ∘ g₂) [at ∞] :=
  obtain c₁ Hc₁, from Hf₁,
  obtain c₂ Hc₂, from Hf₂,
  obtain c₃ Hc₃, from Hg₁ c₂,
  have g₂ ∈ ω(1) [at ∞], from asymptotic.lt_of_lt_of_le Hunb Hf₂,
  exists.intro (c₁ * c₃) (eventually_mono
    (eventually_and
      (eventually_image_at_infty Hc₁ Hunb)
      (eventually_and
        Hc₂
        (eventually_image_at_infty Hc₃ this)))
    (take a Ha,
     obtain Hc₁ Hc₂ Hc₃, from Ha,
     calc (f₁ ∘ f₂) a ≤ c₁ * g₁ (f₂ a)        : Hc₁
                  ... ≤ c₁ * g₁ (c₂ * g₂ a)   : mul_le_mul_left _ (Hmono Hc₂)
                  ... ≤ c₁ * (c₃ * g₁ (g₂ a)) : mul_le_mul_left _ Hc₃
                  ... = c₁ * c₃ * (g₁ ∘ g₂) a : mul.assoc))

  lemma ub_add (H₁ : f₁ ∈ 𝓞(g) F) (H₂ : f₂ ∈ 𝓞(g) F) : f₁ + f₂ ∈ 𝓞(g) F :=
  obtain c₁ Hc₁, from H₁,
  obtain c₂ Hc₂, from H₂,
  exists.intro (c₁ + c₂) (eventually_mono (eventually_and Hc₁ Hc₂) (
    take a Ha,
    calc f₁ a + f₂ a ≤ c₁ * g a + c₂ * g a : add_le_add (and.left Ha) (and.right Ha)
                 ... = (c₁ + c₂) * g a     : nat.right_distrib))

  lemma ub_add_left (g₁ : A → ℕ) {g₂ : A → ℕ} (h : f ∈ 𝓞(g₂) F) : f ∈ 𝓞(g₁ + g₂) F :=
  obtain c hc, from h,
  exists.intro c (eventually_mono hc
    (λ x h, nat.le_trans h (nat.mul_le_mul !nat.le_refl !le_add_left)))

  lemma ub_add_const {k : ℕ} (h : f₁ ∈ 𝓞(g) F ∩ Ω(λ x, k) F) : f₁ + (λ x, k) ∈ 𝓞(g) F ∩ Ω(λ x, k) F :=
  obtain h₁ h₂, from h,
  and.intro (ub_add h₁ (asymptotic.le.trans h₂ h₁))
    (have (λ x, k) ∈ 𝓞(f₁ + (λ x, k)) F, from ub_add_left f₁ (@le.refl _ _ (λ x, k)),
     show f₁ + (λ x, k) ∈ Ω(λ x, k) F, from this)

  lemma ub_mul_prod_filter {A B : Type} {f₁ g₁ : A → ℕ} {f₂ g₂ : B → ℕ} {F₁ : filter A}
    {F₂ : filter B} (H₁ : f₁ ∈ 𝓞(g₁) F₁) (H₂ : f₂ ∈ 𝓞(g₂) F₂) :
    (λp, f₁ p.1 * f₂ p.2) ∈ 𝓞(λp, g₁ p.1 * g₂ p.2) (prod_filter F₁ F₂) :=
  obtain c₁ Hc₁, from H₁,
  obtain c₂ Hc₂, from H₂,
  exists.intro (c₁ * c₂) (bounded_exists.intro Hc₁ (bounded_exists.intro Hc₂ (
    take p Hp,
    obtain Hp₁ Hp₂, from Hp,
    calc f₁ p.1 * f₂ p.2 ≤ c₁ * g₁ p.1 * (c₂ * g₂ p.2) : nat.mul_le_mul Hp₁ Hp₂
                     ... = c₁ * c₂ * (g₁ p.1 * g₂ p.2) : by simp
  )))

  lemma log_unbounded {b : ℕ} (H : b > 1) : log b ∈ ω(1) [at ∞] :=
  take c, eventually_at_infty_intro (take a,
    suppose a ≥ b^c,
    calc c * 1 = log b (b^c) : by rewrite [mul_one, log_pow H]
           ... ≤ log b a     : nondecreasing_log H this)

  lemma id_unbounded : id ∈ ω(1) [at ∞] :=
  take c, eventually_at_infty_intro (take a,
    suppose a ≥ c,
    show c * 1 ≤ a, by rewrite mul_one; apply this)

  lemma ub_of_eventually_le (H : eventually (λa, f₁ a ≤ f₂ a) F) : f₁ ∈ 𝓞(f₂) F :=
  exists.intro 1 (eventually_mono H (take a Ha,
    show f₁ a ≤ 1 * f₂ a, by rewrite one_mul; apply Ha))

  lemma ub_of_eventually_le_at_infty [linear_strong_order_pair A] (x : A)
    (H : ∀ y, y ≥ x → f₁ y ≤ f₂ y) : f₁ ∈ 𝓞(f₂) [at ∞] :=
  ub_of_eventually_le (eventually_at_infty_intro H)

  lemma ub_const (k : ℕ) : (λa, k) ∈ 𝓞(1) F := exists.intro k (eventually_of_always
    (λa, le_of_eq (mul_one _)⁻¹))
end asymptotic
