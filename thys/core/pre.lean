import data.nat data.list
import theories.topology.limit
import bitvec
import loop_combinator


open bool
open int
open list
open nat
open option
open prod.ops

infixr ∘ := function.comp
notation f ` $ `:1 x:0 := f x

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

definition u8.bits [reducible] : ℕ := 8
definition u16.bits [reducible] : ℕ := 16
definition u32.bits [reducible] : ℕ := 32
definition u64.bits [reducible] : ℕ := 64

-- Should perhaps be a constant-axiom pair, but that would break computability.
-- TODO: `usize::MAX` will be determined by the current host anyway right now.
definition usize.bits : ℕ := 16
definition usize.bits_ge_16 : usize.bits ≥ 16 := dec_trivial
attribute usize.bits [irreducible]

definition i8.bits [reducible] : ℕ := 8
definition i16.bits [reducible] : ℕ := 16
definition i32.bits [reducible] : ℕ := 32
definition i64.bits [reducible] : ℕ := 64
definition isize.bits : ℕ := usize.bits

definition unsigned.max (bits : ℕ) : ℕ := 2^bits - 1
abbreviation u8.max : ℕ := unsigned.max u8.bits
abbreviation u16.max : ℕ := unsigned.max u16.bits
abbreviation u32.max : ℕ := unsigned.max u32.bits
abbreviation u64.max : ℕ := unsigned.max u64.bits
abbreviation usize.max : ℕ := unsigned.max usize.bits

definition signed.min (bits : ℕ) : ℤ := -2^(bits-1)
definition signed.max (bits : ℕ) : ℤ := 2^(bits-1) - 1

definition isize_to_usize (x : isize) : sem usize :=
if x ≥ 0 then return (nat.of_int x)
else mzero

definition bool_to_usize (x : bool) : sem usize :=
return (if x = tt then 1 else 0)

definition isize_to_u32 (x : isize) :=
do x ← isize_to_usize x;
if x ≤ u32.max then return x
else mzero


definition check_unsigned [reducible] (bits : ℕ) (x : nat) : sem nat :=
sem.guard (x ≤ unsigned.max bits) (return x)

definition checked.add [reducible] (bits : ℕ) (x y : nat) : sem nat :=
check_unsigned bits (x+y)

definition checked.div [reducible] (bits : ℕ) (x y : nat) : sem nat :=
sem.guard (y ≠ 0) $ return (div x y)

definition checked.rem [reducible] (bits : ℕ) (x y : nat) : sem nat :=
sem.guard (y ≠ 0) $ return (mod x y)

abbreviation binary_bitwise_op (bits : ℕ) (op : bitvec bits → bitvec bits → bitvec bits)
  (a b : nat) : nat :=
bitvec.to ℕ (op (bitvec.of bits a) (bitvec.of bits b))

definition bitor [reducible] bits := binary_bitwise_op bits bitvec.or
definition bitand [reducible] bits := binary_bitwise_op bits bitvec.and
definition bitxor [reducible] bits := binary_bitwise_op bits bitvec.xor

notation a ` ||[`:65 n `] ` b:65  := bitor n a b
notation a ` &&[`:70 n `] ` b:70  := bitand n a b

definition checked.shl [reducible] (bits : ℕ) (x : nat) (y : u32) : sem nat :=
sem.guard (y < bits) $ return $ bitvec.to ℕ $ bitvec.shl (bitvec.of bits x) y

-- allows for arbitrary range of x in contrast to bitvec.ushr
definition checked.shr [reducible] (bits : ℕ) (x : nat) (y : u32) : sem nat :=
sem.guard (y < bits) $ return (x / 2^y)

definition checked.shrs [reducible] (bits : ℕ) (x : nat) (y : i32) : sem nat :=
sem.guard (0 ≤ y) $ checked.shr bits x (nat.of_int y)


definition check_signed [reducible] (bits : ℕ) (x : int) : sem int :=
sem.guard (signed.min bits ≤ x ∧ x ≤ signed.max bits) $ return x

definition checked.sadd [reducible] (bits : ℕ) (x y : int) : sem int :=
check_signed bits (x+y)

infix `=ᵇ`:50 := λ a b, bool.of_Prop (a = b)
infix `≠ᵇ`:50 := λ a b, bool.of_Prop (a ≠ b)
infix `≤ᵇ`:50 := λ a b, @bool.of_Prop (a ≤ b) (decidable_le a b) -- small elaborator hint
infix `<ᵇ`:50 := λ a b, @bool.of_Prop (a < b) (decidable_lt a b)
infix `≥ᵇ`:50 := λ a b, b ≤ᵇ a
infix `>ᵇ`:50 := λ a b, b <ᵇ a

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

    structure FnMut [class] (Self : Type₁) (Args : Type₁) (Output : Type₁)
      extends FnOnce Self Args Output :=
    (call_mut : Self → Args → sem (Output × Self))

    abbreviation Fn := FnMut
    definition Fn.call (Self : Type₁) (Args : Type₁) (Output : Type₁)
      [FnMut : FnMut Self Args Output] : Self → Args → sem Output :=
    FnOnce.call_once Output
  end ops
end core

open core.ops

definition fn [instance] {A B : Type₁} : FnOnce (A → sem B) A B := ⦃FnOnce,
  call_once := id
⦄

-- only immutable closures for now
definition fn_mut [instance] {A B : Type₁} : FnMut (A → sem (B × A)) A B := ⦃FnMut,
  call_once := λ f a, do p ← f a; return p.1,
  call_mut := λ f a, do p ← f a; return (p.1, f)
⦄

notation `let'` binder ` ← ` x `; ` r:(scoped f, f x) := r
attribute sem [irreducible]
