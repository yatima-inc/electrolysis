import theories.topology.limit
import move

open eq.ops
open function
open nat
open prod.ops
open set
open topology

namespace asymptotic
  -- single parameter:
  --definition ub (f : ℕ → ℕ) : set (ℕ → ℕ) :=
  --λg, ∃c n₀, ∀n, n ≥ n₀ → f n ≤ c * g n

  section
    variables {A : Type} (g : A → ℕ) (F : filter A)

    definition ub : set (A → ℕ) :=
    {f | ∃c, filter.eventually {a | f a ≤ c * g a} F}
    notation `𝓞(` g `)` := ub g

    definition strict_ub : set (A → ℕ) :=
    {f | ∀c, filter.eventually {a | c * f a ≤ g a} F}
    notation `𝓸(` g `)` := strict_ub g

    definition lb : set (A → ℕ) := {f | g ∈ 𝓞(f) F}
    notation `Ω(` g `)` := lb g

    definition strict_lb : set (A → ℕ) := {f | g ∈ 𝓸(f) F}
    notation `ω(` g `)` := strict_lb g

    definition equiv : set (A → ℕ) := 𝓞(g) F ∩ Ω(g) F
    notation `Θ(` g `)` := equiv g
  end

  notation `𝓞(1` `)`  := 𝓞(λx, 1)
  notation `𝓸(1` `)`  := 𝓸(λx, 1)
  notation `Ω(1` `)`  := Ω(λx, 1)
  notation `ω(1` `)`  := ω(λx, 1)
  notation `Θ(1` `)`  := Θ(λx, 1)

  notation `[at ` `∞` ` × ` `∞]` := prod_filter at_infty at_infty

  lemma ub_comp_of_nondecreasing_of_ub {A : Type} {F : filter A} {h : ℕ → ℕ} (Hh : nondecreasing h)
    {f g : A → ℕ} (Hg : f ∈ 𝓞(g) F) : h ∘ f ∈ 𝓞(h ∘ g) F := sorry

  lemma ub_add_const {A : Type} {F : filter A} {f g : A → ℕ} (Hg : f ∈ 𝓞(g) F) {k : ℕ}
    (Hk : g ∈ ω(1) F) : (λx, f x + k) ∈ 𝓞(g) F :=
  obtain c Hc, from Hg,   exists.intro (c + 1) (filter.is_mono F (take x,
      suppose f x ≤ c * g x ∧ k * 1 ≤ g x,
      calc f x + k ≤ c * g x + g x : add_le_add (and.left this) (mul_one k ▸ and.right this)
               ... = (c + 1) * g x : by rewrite [nat.right_distrib, one_mul])
    (filter.inter_closed F Hc (Hk k)))

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

  lemma log_unbounded {b : ℕ} (H : b > 1) : log b ∈ (ω(1) [at ∞]) :=
  take c, eventually_at_infty_intro (take a,
    suppose a ≥ b^c,
    calc c * 1 = log b (b^c) : by rewrite [mul_one, log_pow H]
           ... ≤ log b a     : nondecreasing_log H this)
end asymptotic
