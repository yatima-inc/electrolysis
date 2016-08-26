import move

open nat
open [notation] partial
open prod.ops
open option
open - [class] set

open [class] classical

-- fix semantics monad
definition sem (a : Type₁) := option (a × nat)

definition sem.incr [unfold 3] {a : Type₁} (n : ℕ) : sem a → sem a
| (some (x, k)) := some (x, k+n)
| none          := none

inductive sem.terminates_with {a : Type₁} (H : a → Prop) (max_cost : ℕ) : sem a → Prop :=
mk : Π {ret x k}, ret = some (x, k) → H x → k ≤ max_cost → sem.terminates_with H max_cost ret

definition sem.map [unfold 4] {a b : Type₁} (f : a → b) (m : sem a) : sem b :=
option.map (λs, match s with
| (x, k) := (f x, k)
end) m

definition sem.return {a : Type₁} (x : a) : sem a := some (x, 0)
definition sem.bind {a b : Type₁} (m : sem a) (f : a → sem b) : sem b :=
option.bind m (λs, match s with
| (x, k) :=
  option.bind (f x) (λs', match s' with
  | (x', k') := some (x', k+k')
  end)
end)
definition sem.zero {a : Type₁} : sem a := none

abbreviation return {a : Type₁} : a → sem a := sem.return
abbreviation mzero  {a : Type₁} : sem a := sem.zero
infixl ` >>= `:2 := sem.bind
notation `do` binder ` ← ` x `; ` r:(scoped f, sem.bind x f) := r
notation `dostep ` binder ` ← ` x `; ` r:(scoped f, sem.incr 1 (sem.bind x f)) := r


definition sem.lift_opt [unfold 2] {a : Type₁} : option a → sem a :=
option.rec sem.zero return

attribute sem.bind [unfold 3]
attribute sem.return [constructor]
lemma return_bind {A B : Type₁} {a : A} {f : A → sem B} : (return a >>= f) = f a :=
begin
  esimp,
  cases f a with a',
  { esimp },
  { cases a', rewrite [▸*, !zero_add] }
end
lemma bind_return {A : Type₁} {m : sem A} : (m >>= return) = m :=
begin
  cases m with a',
  { esimp },
  { cases a', esimp }
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

lemma incr_bind {A B : Type₁} {k : ℕ} {m : sem A} {f : A → sem B} :
  sem.incr k (sem.bind m f) = sem.bind (sem.incr k m) f :=
begin
  cases m with x,
  { esimp },
  { cases x with a k, esimp, cases f a with x',
    { esimp },
    { apply prod.cases_on, esimp, intros, rewrite [add.right_comm] }
  }
end

lemma neq_mzero_of_incr_neq_mzero {A : Type₁} {k : ℕ} {m : sem A} (H : sem.incr k m ≠ mzero) :
  m ≠ mzero :=
begin
  cases m with x,
  { exact H },
  { cases x with a k, esimp, contradiction }
end
