import data.nat data.list
import theories.topology.limit
import loop_combinator

infix `=ᵈ`:50 := λ a b, bool.of_decidable (_ : decidable (a = b))
infix `≠ᵈ`:50 := λ a b, bool.of_decidable (decidable_ne a b)
infix `≤ᵈ`:50 := λ a b, bool.of_decidable (decidable_le a b)
infix `<ᵈ`:50 := λ a b, bool.of_decidable (decidable_lt a b)
infix `≥ᵈ`:50 := λ a b, b ≤ᵈ a
infix `>ᵈ`:50 := λ a b, b <ᵈ a

open bool
open int
open function
open list
open nat
open option

structure lens (Outer Inner : Type₁) :=
(get : Outer → sem Inner)
(set : Outer → Inner → sem Outer)

definition lens.id [constructor] {Inner : Type₁} : lens Inner Inner :=
⦃lens, get := return, set := λ o, return⦄

definition lens.comp [unfold 4 5] {A B C : Type₁} (l₁ : lens A B) (l₂ : lens B C) : lens A C :=
⦃lens, get := λ o,
  do o' ← lens.get l₁ o;
  lens.get l₂ o',
 set := λ o i,
  do o' ← lens.get l₁ o;
  do o' ← lens.set l₂ o' i;
  lens.set l₁ o o'⦄

infixr ` ∘ₗ `:60 := lens.comp

definition lens.index [constructor] (Inner : Type₁) (index : ℕ) : lens (list Inner) Inner :=
⦃lens,
  get := λ self, sem.lift_opt (list.nth self index),
  set := λ self, sem.lift_opt ∘ list.update self index⦄

/-
inductive lens' : Type₁ → Type₁ → Type :=
| arbitrary : Π{Outer Inner : Type₁}, lens Outer Inner → lens' Outer Inner
| index : Π(Inner : Type₁), ℕ → lens' (list Inner) Inner
| comp : Π{A B C : Type₁}, lens' A B → lens' B C → lens' A C

infixr ` ∘ ` := lens'.comp

definition lens'.id {Outer : Type₁} : lens' Outer Outer :=
lens'.arbitrary (lens.mk return (λ o, return))

definition lens'.get [unfold 3] : Π{Outer Inner : Type₁}, lens' Outer Inner → Outer → sem Inner
| _ _ (lens'.arbitrary l) o := lens.get l o
| ⌞_⌟ _ (lens'.index I n) o := sem.lift_opt (nth o n)
| _ _ (lens'.comp l₁ l₂) o :=
  do i' ← lens'.get l₁ o;
  lens'.get l₂ i'

definition lens'.set [unfold 3] : Π{Outer Inner : Type₁}, lens' Outer Inner → Outer → Inner → sem Outer
| _ _ (lens'.arbitrary l) o i := lens.set l o i
| ⌞_⌟ _ (lens'.index I n) o i := sem.lift_opt (list.update o n i)
| _ _ (lens'.comp l₁ l₂) o i :=
  do o' ← lens'.get l₁ o;
  do o' ← lens'.set l₂ o' i;
  lens'.set l₁ o o'


definition lens'.incr : Π{Outer Inner : Type₁}, lens' Outer Inner → option (lens' Outer Inner)
| _ _ (lens'.arbitrary l) := none
| ⌞_⌟ _ (lens'.index I n) := some (lens'.index I (n+1))
| _ _ (lens'.comp l₁ l₂) := option.map (λ l₂', lens'.comp l₁ l₂') (lens'.incr l₂)
-/


abbreviation u8 [parsing_only] := nat
abbreviation u16 [parsing_only] := nat
abbreviation u32 [parsing_only] := nat
abbreviation u64 [parsing_only] := nat
abbreviation usize [parsing_only] := nat

abbreviation i8 [parsing_only] := int
abbreviation i16 [parsing_only] := int
abbreviation i32 [parsing_only] := int
abbreviation i64 [parsing_only] := int
abbreviation isize [parsing_only] := int

abbreviation slice [parsing_only] := list

definition isize_to_usize (x : isize) : sem usize :=
if x ≥ 0 then return (nat.of_int x)
else mzero

definition bool_to_usize (x : bool) : sem usize :=
return (if x = tt then 1 else 0)

abbreviation isize_to_u32 [parsing_only] := isize_to_usize

definition checked.sub (x y : nat) : sem nat :=
if x ≥ y then return (x-y) else mzero

definition checked.div (x y : nat) : sem nat :=
if y ≠ 0 then return (div x y) else mzero

definition checked.mod (x y : nat) : sem nat :=
if y ≠ 0 then return (mod x y) else mzero

/- TODO: actually check something -/
definition checked.shl (x : nat) (y : int) : sem nat := return (x * 2^nat.of_int y)
definition checked.shr (x : nat) (y : int) : sem nat := return (div x (2^nat.of_int y))

definition nat.to_bits (n : ℕ) : list bool :=
nat.strong_rec_on n (λ n rec,
if H : n = 0 then []
else (if n % 2 = 1 then tt else ff) :: rec (n / 2) (div_lt_of_ne_zero H))

definition nat.of_bits : list bool → ℕ
| [] := 0
| (x::xs) := (if x = tt then 1 else 0) + 2 * nat.of_bits xs

definition bitand (x y : nat) : nat :=
nat.of_bits (map₂ band (nat.to_bits x) (nat.to_bits y))

infix && := bitand

definition bitor (x y : nat) : nat :=
have rec : list bool → list bool → list bool
| xs []           := xs
| [] ys           := ys
| (x::xs) (y::ys) := (x || y) :: rec xs ys,
nat.of_bits (rec (nat.to_bits x) (nat.to_bits y))

infix || := bitor

namespace core
  abbreviation intrinsics.add_with_overflow (x y : nat) : sem (nat × Prop) := return (x + y, false)

  abbreviation mem.swap {T : Type₁} (x y : T) : sem (unit × T × T) := return (unit.star,y,x)

  abbreviation «[T] as core.slice.SliceExt».len {T : Type₁} (self : slice T) : sem nat :=
  return (list.length self)
  definition «[T] as core.slice.SliceExt».get_unchecked {T : Type₁} (self : slice T) (index : usize)
    : sem T :=
  option.rec mzero return (list.nth self index)

  /- This trait has way too many freaky dependencies -/
  structure fmt.Debug [class] (Self : Type₁) := mk ::

  namespace ops
    structure FnOnce [class] (Self : Type₁) (Args : Type₁) (Output : Type₁) :=
    (call_once : Self → Args → sem Output)

    -- easy without mutable closures
    abbreviation FnMut [parsing_only] := FnOnce
    abbreviation Fn := FnOnce

    definition FnMut.call_mut [unfold_full] (Args : Type₁) (Self : Type₁) (Output : Type₁)
      [FnOnce : FnOnce Self Args Output] : Self → Args → sem (Output × Self) := λself x,
      do y ← @FnOnce.call_once Self Args Output FnOnce self x;
      return (y, self)

    definition Fn.call (Self : Type₁) (Args : Type₁) (Output : Type₁)
      [FnMut : FnMut Self Args Output] : Self → Args → sem Output := FnOnce.call_once Output
  end ops
end core

open core.ops

definition fn [instance] {A B : Type₁} : FnOnce (A → sem B) A B := ⦃FnOnce,
  call_once := id
⦄

notation `let'` binder ` ← ` x `; ` r:(scoped f, f x) := r
notation `if' ` b ` then ` t ` else ` f := bool.rec_on b t f
attribute sem [irreducible]
