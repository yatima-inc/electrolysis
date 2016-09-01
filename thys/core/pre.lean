import data.nat data.list
import theories.topology.limit
import loop_combinator

open bool
open int
open list
open nat

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
attribute sem [irreducible]
