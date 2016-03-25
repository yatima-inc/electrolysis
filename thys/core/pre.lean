import data.nat
open bool
open nat
open prod
open option
open prod.ops

definition option.bind {A B : Type} (f : A → option B) : option A → option B
| (some x) := f x
| none     := none

notation `do` binder ` ← ` x `; ` r:(scoped f, option.bind f x) := r

open [class] classical

noncomputable definition some_opt {A : Type} (P : A → Prop) : option A :=
if H : Exists P then some (classical.some H)
else none

section
  parameters {A B : Type}
  parameters (F : (A → option B) → option B)

  private noncomputable definition fix_opt.F (R : A → A → Prop) (x : A) (f : Π (y : A), R y x → option B) : option B :=
  F (λy, if H : R y x then f y H else none)

  private noncomputable definition fix_opt.fix (R : A → A → Prop) (Hwf: well_founded R) (x : A) : option B :=
  @well_founded.fix A (λx, option B) R Hwf (fix_opt.F R) x

  noncomputable definition fix_opt (x : A) : option B :=
  do R ← some_opt (λR, if Hwf : well_founded R then ∀x : A, fix_opt.fix R Hwf x ≠ none else false);
  if Hwf : well_founded R then fix_opt.fix R Hwf x else none

  theorem fix_opt_eq {R : A → A → Prop} [Hwf : well_founded R] (Hf_wf : ∀x : A, fix_opt.fix R Hwf x ≠ none) (x : A) :
    fix_opt x = F (λx, fix_opt x) :=
  sorry
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
