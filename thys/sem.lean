import move

open eq.ops
open nat
open [notation] partial
open prod.ops
open option
open - [class] set

open [class] classical

-- fix semantics monad
definition sem (a : Type₁) := option (a × ℕ)

definition sem.incr [unfold 3] {a : Type₁} (n : ℕ) : sem a → sem a
| (some (x, k)) := some (x, k+n)
| none          := none

definition sem.terminates_with [unfold 3] {a : Type₁} (H : a → Prop) (s : sem a) : Prop :=
option.any (λ p, H p.1) s

definition sem.terminates [unfold 2] {a : Type₁} (s : sem a) : Prop :=
sem.terminates_with (λ a, true) s

lemma sem.terminates_with_incr {a : Type₁} {p : a → Prop} (k : ℕ) {s : sem a}
  (h : sem.terminates_with p s) : sem.terminates_with p (sem.incr k s) :=
begin
  cases s with x,
  { contradiction },
  { cases x, apply h }
end

inductive sem.terminates_with_in {a : Type₁} (H : a → Prop) (max_cost : ℕ) : sem a → Prop :=
mk : Π {ret x k}, ret = some (x, k) → H x → k ≤ max_cost → sem.terminates_with_in H max_cost ret

lemma sem.terminates_with_in.imp {a : Type₁} {h₁ h₂ : a → Prop} {c₁ c₂ : ℕ} {s : sem a}
  (h : sem.terminates_with_in h₁ c₁ s) (hh : ∀ a, h₁ a → h₂ a) (hc : c₁ ≤ c₂) :
  sem.terminates_with_in h₂ c₂ s :=
begin
  cases h with ret x k hr hx hk,
  apply sem.terminates_with_in.mk hr (hh x hx) (le.trans hk hc)
end

lemma sem.terminates_with_in_incr {a : Type₁} {p : a → Prop} {c : ℕ} (k : ℕ) {s : sem a}
  (h : sem.terminates_with_in p c s) : sem.terminates_with_in p (c+k) (sem.incr k s) :=
begin
  cases h with ret x k hr hx hk,
  rewrite hr,
  apply sem.terminates_with_in.mk rfl, apply hx, apply add_le_add_right hk
end

lemma sem.terminates_with_in_of_incr {a : Type₁} {p : a → Prop} {c₁ c₂ : ℕ} {s : sem a}
  (h : sem.terminates_with_in p (c₁+c₂) (sem.incr c₂ s)) : sem.terminates_with_in p c₁ s :=
begin
  cases h with ret x k hr hx hk,
  cases s with s',
  { contradiction },
  { cases s' with x' k', injection hr with x'_eq k'_eq,
    esimp at hr,
    apply sem.terminates_with_in.mk rfl,
    { apply (x'_eq⁻¹ ▸ hx) },
    { exact le_of_add_le_add_right (k'_eq⁻¹ ▸ hk) },
  }
end

definition sem.map [unfold 4] {a b : Type₁} (f : a → b) (m : sem a) : sem b :=
option.map (λs, match s with
| (x, k) := (f x, k)
end) m

definition sem.return {a : Type₁} (x : a) : sem a := some (x, 0)
definition sem.return_incr [constructor] {a : Type₁} (x : a) (n : ℕ) : sem a := some (x, n)
definition sem.bind {a b : Type₁} (m : sem a) (f : a → sem b) : sem b :=
option.bind m (λs, match s with
| (x, k) := sem.incr k (f x)
end)
definition sem.zero {a : Type₁} : sem a := none

abbreviation return {a : Type₁} : a → sem a := sem.return
abbreviation mzero  {a : Type₁} : sem a := sem.zero
infixl ` >>= `:2 := sem.bind
notation `do ` binder ` ← ` x `; ` r:(scoped f, sem.bind x f) := r
notation `dostep ` binder ` ← ` x `; ` r:(scoped f, sem.incr 1 (sem.bind x f)) := r

definition sem.unwrap [unfold 3] {a : Type₁} {H : a → Prop} :
  Π{s : sem a}, sem.terminates_with H s → a
| (some (x, k)) _ := x
| none          H := false.rec _ H

lemma sem.sem_unwrap {a : Type₁} {H : a → Prop} {s : sem a} (term : sem.terminates_with H s) :
  H (sem.unwrap term) :=
begin
  cases s with p,
  { contradiction },
  { cases p, esimp at *, assumption }
end

definition sem.lift_opt [unfold 2] {a : Type₁} : option a → sem a :=
option.rec sem.zero return

definition sem.guard [reducible] {a : Type₁} (p : Prop) [decidable p] (s : sem a) : sem a :=
if p then s else mzero

attribute sem.bind [unfold 3]
attribute sem.return [constructor]

lemma sem.terminates_with_eq {a : Type₁} {P : a → Prop} {s : sem a} :
  sem.terminates_with P s → ∃ x k, s = sem.return_incr x k ∧ P x :=
begin
  cases s with p,
  { contradiction },
  { esimp,
    intro H,
    existsi p.1, existsi p.2,
    split,
    { rewrite [↑sem.return_incr, prod.eta] },
    { exact H }
  }
end

lemma sem.not_terminates_mzero {a : Type₁} : ¬sem.terminates (mzero : sem a) :=
id

lemma return_bind {A B : Type₁} {a : A} {f : A → sem B} : (return a >>= f) = f a :=
begin
  esimp,
  cases f a with a',
  { esimp },
  { cases a', esimp }
end
lemma bind_return {A : Type₁} {m : sem A} : (m >>= return) = m :=
begin
  cases m with a',
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
      { cases m''', rewrite [▸*, add.assoc] }
    }
  }
end

lemma incr_bind {A B : Type₁} {k : ℕ} {m : sem A} {f : A → sem B} :
  sem.incr k (sem.bind m f) = sem.bind (sem.incr k m) f :=
begin
  cases m with x,
  { esimp },
  { cases x with a k, esimp, cases f a with x',
    { esimp },
    { apply prod.cases_on, esimp, intros, rewrite [add.assoc] }
  }
end

lemma incr_incr {A : Type₁} (k k' : ℕ) (m : sem A) :
  sem.incr k (sem.incr k' m) = sem.incr (k + k') m :=
begin
  cases m with x,
  { esimp },
  { cases x with a k, esimp, rewrite [add.assoc, {k + k'}add.comm] }
end

lemma neq_mzero_of_incr_neq_mzero {A : Type₁} {k : ℕ} {m : sem A} (H : sem.incr k m ≠ mzero) :
  m ≠ mzero :=
begin
  cases m with x,
  { exact H },
  { cases x with a k, esimp, contradiction }
end
