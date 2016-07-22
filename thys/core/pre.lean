import data.nat data.list
import loop_combinator

open nat
open option

abbreviation u8 [parsing_only] := nat
abbreviation u16 [parsing_only] := nat
abbreviation u32 [parsing_only] := nat
abbreviation u64 [parsing_only] := nat
abbreviation usize [parsing_only] := nat

abbreviation slice [parsing_only] := list

definition checked.sub (n : nat) (m : nat) :=
if n ≥ m then some (n-m) else none

definition checked.div (n : nat) (m : nat) :=
if m ≠ 0 then some (div n m) else none

definition checked.mod (n : nat) (m : nat) :=
if m ≠ 0 then some (mod n m) else none

/- TODO: actually check something -/
definition checked.shl (n : nat) (m : nat) := some (n * 2^m)
definition checked.shr (n : nat) (m : int) := some (div n (2^nat.of_int m))

namespace core
  abbreviation intrinsics.add_with_overflow (n : nat) (m : nat) := some (n + m, false)

  abbreviation mem.swap {T : Type} (x y : T) := some (unit.star,y,x)

  abbreviation slice._T_.slice_SliceExt.len {T : Type} (self : slice T) := some (list.length self)
  abbreviation slice._T_.slice_SliceExt.get_unchecked [parsing_only] {T : Type} (self : slice T) (index : usize) :=
  list.nth self index

  namespace ops
    structure FnOnce [class] (Args : Type) (Self : Type) (Output : Type) :=
    (call_once : Self → Args → option (Output))

    -- easy without mutable closures
    abbreviation FnMut [parsing_only] := FnOnce
    abbreviation Fn := FnOnce

    definition FnMut.call_mut [unfold_full] (Args : Type) (Self : Type) (Output : Type) [FnOnce : FnOnce Args Self Output] : Self → Args → option (Output × Self) := λself x,
      do y ← @FnOnce.call_once Args Self Output FnOnce self x;
      some (y, self)

    definition Fn.call (Args : Type) (Self : Type) (Output : Type) [FnMut : FnMut Args Self Output] : Self → Args → option Output := @FnOnce.call_once Args Self Output FnMut
  end ops
end core

open core.ops

definition fn [instance] {A B : Type} : FnOnce A (A → option B) B := ⦃FnOnce,
  call_once := id
⦄

notation `let` binder ` ← ` x `; ` r:(scoped f, f x) := r
