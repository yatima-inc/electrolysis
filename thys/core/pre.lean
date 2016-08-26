import data.nat data.list
import theories.topology.limit
import loop_combinator

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

  abbreviation «[T] as core.slice.SliceExt».len {T : Type₁} (self : slice T) : sem nat :=
  return (list.length self)
  definition «[T] as core.slice.SliceExt».get_unchecked {T : Type₁} (self : slice T) (index : usize)
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

notation `let'` binder ` ← ` x `; ` r:(scoped f, f x) := r
attribute sem [irreducible]
