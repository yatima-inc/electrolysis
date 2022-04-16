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

definition lens.comp [unfold 4 5] {A B C : Type₁} (l₂ : lens B C) (l₁ : lens A B) : lens A C :=
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

abbreviation char32 [parsing_only] := nat

abbreviation i8 [parsing_only] := int
abbreviation i16 [parsing_only] := int
abbreviation i32 [parsing_only] := int
abbreviation i64 [parsing_only] := int
abbreviation isize [parsing_only] := int

definition u8.bits [reducible] : ℕ := 8
definition u16.bits [reducible] : ℕ := 16
definition u32.bits [reducible] : ℕ := 32
definition u64.bits [reducible] : ℕ := 64

-- Should perhaps be a constant-axiom pair, but that would break computability.
definition usize.bits : ℕ := 16
lemma usize.bits_ge_16 : usize.bits ≥ 16 := dec_trivial
attribute usize.bits [irreducible]

definition char32.bits [reducible] : ℕ := 32

definition i8.bits [reducible] : ℕ := 8
definition i16.bits [reducible] : ℕ := 16
definition i32.bits [reducible] : ℕ := 32
definition i64.bits [reducible] : ℕ := 64
definition isize.bits : ℕ := usize.bits

definition unsigned.max [reducible] (bits : ℕ) : ℕ := 2^bits - 1
abbreviation u8.max : ℕ := unsigned.max u8.bits
abbreviation u16.max : ℕ := unsigned.max u16.bits
abbreviation u32.max : ℕ := unsigned.max u32.bits
abbreviation u64.max : ℕ := unsigned.max u64.bits
abbreviation usize.max : ℕ := unsigned.max usize.bits

definition signed.min (bits : ℕ) : ℤ := -2^(bits-1)
definition signed.max (bits : ℕ) : ℤ := 2^(bits-1) - 1

definition is_bounded_nat [class] [reducible] (bits x : ℕ) :=
x < 2^bits
definition is_bounded_int [class] [reducible] (bits : ℕ) (x : int) :=
-2^(bits-1) ≤ x ∧ x < 2^(bits-1)

abbreviation is_usize := is_bounded_nat usize.bits
abbreviation is_index := is_bounded_nat (usize.bits - 1)
abbreviation is_i32 := is_bounded_int i32.bits


definition check_unsigned [reducible] (bits : ℕ) (x : nat) : sem nat :=
sem.guard (is_bounded_nat bits x) (return x)

definition checked.add [reducible] (bits : ℕ) (x y : nat) : sem nat :=
check_unsigned bits (x+y)

definition checked.sub [reducible] (bits : ℕ) (x y : nat) : sem nat :=
check_unsigned bits (x-y)

definition checked.mul [reducible] (bits : ℕ) (x y : nat) : sem nat :=
check_unsigned bits (x*y)

definition checked.div [reducible] (bits : ℕ) (x y : nat) : sem nat :=
sem.guard (y ≠ 0) $ return (div x y)

definition checked.rem [reducible] (bits : ℕ) (x y : nat) : sem nat :=
sem.guard (y ≠ 0) $ return (mod x y)


abbreviation unary_unsigned_bitwise_op (bits : ℕ) (op : bitvec bits → bitvec bits)
  (a : nat) : nat :=
bitvec.toNat (op (bitvec.ofNat bits a))

abbreviation binary_unsigned_bitwise_op (bits : ℕ) (op : bitvec bits → bitvec bits → bitvec bits)
  (a b : nat) : nat :=
bitvec.toNat (op (bitvec.ofNat bits a) (bitvec.ofNat bits b))

definition bitor [reducible] bits := binary_unsigned_bitwise_op bits bitvec.or
definition bitand [reducible] bits := binary_unsigned_bitwise_op bits bitvec.and
definition bitxor [reducible] bits := binary_unsigned_bitwise_op bits bitvec.xor
definition bitnot [reducible] bits := unary_unsigned_bitwise_op bits bitvec.not


abbreviation unary_signed_bitwise_op (bits : ℕ)
  (op : Π {bits}, bitvec (succ bits) → bitvec (succ bits)) (a : int) : int :=
match bits with
| 0 := 0
| succ bits := bitvec.toInt (op (bitvec.ofInt (succ bits) a))
end

abbreviation binary_signed_bitwise_op (bits : ℕ)
  (op : Π {bits}, bitvec (succ bits) → bitvec (succ bits) → bitvec (succ bits)) (a b : int) : int :=
match bits with
| 0 := 0
| succ bits := bitvec.toInt (op (bitvec.ofInt (succ bits) a) (bitvec.ofInt (succ bits) b))
end

definition sbitor [reducible] bits := binary_signed_bitwise_op bits $ λ n, bitvec.or
definition sbitand [reducible] bits := binary_signed_bitwise_op bits $ λ n, bitvec.and
definition sbitxor [reducible] bits := binary_signed_bitwise_op bits $ λ n, bitvec.xor
definition sbitnot [reducible] bits := unary_signed_bitwise_op bits $ λ n, bitvec.not


notation a ` ||[`:65 n `] ` b:65  := bitor n a b
notation a ` &&[`:70 n `] ` b:70  := bitand n a b

definition checked.shl [reducible] (bits : ℕ) (x : nat) (y : u32) : sem nat :=
sem.guard (y < bits) $ return $ unary_unsigned_bitwise_op bits (λ x, bitvec.shl x y) x

definition checked.shls [reducible] (bits : ℕ) (x : nat) (y : i32) : sem nat :=
sem.guard (0 ≤ y ∧ y < bits) $ return $ unary_unsigned_bitwise_op bits (λ x, bitvec.shl x (nat.of_int y)) x

-- allows for arbitrary range of x in contrast to bitvec.ushr
definition checked.shr [reducible] (bits : ℕ) (x : nat) (y : u32) : sem nat :=
sem.guard (y < bits) $ return (x / 2^y)

definition checked.shrs [reducible] (bits : ℕ) (x : nat) (y : i32) : sem nat :=
sem.guard (0 ≤ y) $ checked.shr bits x (nat.of_int y)


definition checked.sshl [reducible] (bits : ℕ) (x : int) (y : u32) : sem int :=
sem.guard (y < bits) $ return $ unary_signed_bitwise_op bits (λ n x, bitvec.shl x y) x

definition checked.sshls [reducible] (bits : ℕ) (x : int) (y : i32) : sem int :=
sem.guard (0 ≤ y ∧ y < bits) $ return $ unary_signed_bitwise_op bits (λ n x, bitvec.shl x (nat.of_int y)) x


definition checked.sshr [reducible] (bits : ℕ) (x : int) (y : u32) : sem int :=
sem.guard (y < bits) $ return $ unary_signed_bitwise_op bits (λ n x, bitvec.sshr x y) x

definition checked.sshrs [reducible] (bits : ℕ) (x : int) (y : i32) : sem int :=
sem.guard (0 ≤ y) $ checked.sshr bits x (nat.of_int y)


definition check_signed [reducible] (bits : ℕ) (x : int) : sem int :=
sem.guard (is_bounded_int bits x) $ return x

definition checked.sadd [reducible] (bits : ℕ) (x y : int) : sem int :=
check_signed bits (x+y)

definition checked.ssub [reducible] (bits : ℕ) (x y : int) : sem int :=
check_signed bits (x-y)

definition checked.smul [reducible] (bits : ℕ) (x y : int) : sem int :=
check_signed bits (x+y)

definition checked.sdiv [reducible] (bits : ℕ) (x y : int) : sem int :=
sem.guard (y ≠ 0) $ check_signed bits (div x y)

definition checked.srem [reducible] (bits : ℕ) (x y : int) : sem int :=
sem.guard (y ≠ 0) $ check_signed bits (mod x y)

definition checked.neg [reducible] (bits : ℕ) (x : int) : sem int :=
check_signed bits (-x)


definition unsigned_to_unsigned (bits : ℕ) (x : nat) : sem nat :=
check_unsigned bits x

definition signed_to_unsigned (bits : ℕ) (x : int) : sem nat :=
sem.guard (x ≥ 0) $ check_unsigned bits (nat.of_int x)

definition unsigned_to_signed (bits : ℕ) (x : nat) : sem int :=
check_signed bits x

definition signed_to_signed (bits : ℕ) (x : int) : sem int :=
check_signed bits x

definition bool_to_unsigned (bits : ℕ) (x : bool) : sem nat :=
return (if x = tt then 1 else 0)

definition char_to_unsigned (bits : ℕ) (x : char32) : sem nat :=
check_unsigned bits x

-- statically checked by rustc by only allowing casts from `u8`
definition unsigned_to_char (bits : ℕ) (x : nat) : sem char32 :=
return x

infix `=ᵇ`:50 := λ a b, bool.of_Prop (a = b)
infix `≠ᵇ`:50 := λ a b, bool.of_Prop (a ≠ b)
infix `≤ᵇ`:50 := λ a b, @bool.of_Prop (a ≤ b) (decidable_le a b) -- small elaborator hint
infix `<ᵇ`:50 := λ a b, @bool.of_Prop (a < b) (decidable_lt a b)
infix `≥ᵇ`:50 := λ a b, b ≤ᵇ a
infix `>ᵇ`:50 := λ a b, b <ᵇ a


abbreviation array [parsing_only] (A : Type₁) (n : ℕ) := list A
abbreviation slice [parsing_only] := list

definition is_slice [class] [reducible] {T : Type₁} (xs : slice T) :=
is_index (length xs)

definition wrap_signed (bits : ℕ) (a : int) : int := (a + 2^(bits-1)) % 2^bits - 2^(bits-1)
definition overflowing_signed (op : int → int → int) (bits : ℕ) (a b : int) : sem (int × bool) :=
return (wrap_signed bits (op a b), bool.of_Prop $ ¬is_bounded_int bits (op a b))

namespace core
  namespace intrinsics
    definition add_with_overflow (bits : ℕ) (a b : nat) : sem (nat × bool) :=
    return ((a + b) % 2^bits, a + b ≥ᵇ 2^bits)
    definition sub_with_overflow (bits : ℕ) (a b : nat) : sem (nat × bool) :=
    return ((a + 2^bits - b) % 2^bits, a <ᵇ b)
    definition mul_with_overflow (bits : ℕ) (a b : nat) : sem (nat × bool) :=
    return (a * b % 2^bits, a * b ≥ᵇ 2^bits)

    definition add_with_overflow_signed := overflowing_signed add
    definition sub_with_overflow_signed := overflowing_signed sub
    definition mul_with_overflow_signed := overflowing_signed mul

    definition overflowing_add (bits : ℕ) (a b : nat) := sem.map prod.pr1 (add_with_overflow bits a b)
    definition overflowing_sub (bits : ℕ) (a b : nat) := sem.map prod.pr1 (sub_with_overflow bits a b)
    definition overflowing_mul (bits : ℕ) (a b : nat) := sem.map prod.pr1 (mul_with_overflow bits a b)

    definition overflowing_add_signed (bits : ℕ) (a b : int) := sem.map prod.pr1 (overflowing_signed add bits a b)
    definition overflowing_sub_signed (bits : ℕ) (a b : int) := sem.map prod.pr1 (overflowing_signed sub bits a b)
    definition overflowing_mul_signed (bits : ℕ) (a b : int) := sem.map prod.pr1 (overflowing_signed mul bits a b)
  end intrinsics

  abbreviation mem.swap {T : Type₁} (x y : T) : sem (unit × T × T) := return (unit.star,y,x)

  abbreviation «[T] as core.slice.SliceExt».len {T : Type₁} (self : slice T) : sem nat :=
  return (list.length self)
  definition «[T] as core.slice.SliceExt».get_unchecked {T : Type₁} (self : slice T) (index : usize)
    : sem T :=
  sem.lift_opt (list.nth self index)

  /- This trait has way too many freaky dependencies -/
  structure fmt.Debug [class] (Self : Type₁) := mk ::

  -- common dependency
  inductive option.Option (T : Type₁) :=
  | None {} : option.Option T
  | Some {} : T → option.Option T

  -- architecture dependent
  definition isize.min_value := return $ signed.min isize.bits
  definition usize.min_value := return (0 : nat)

  definition num.wrapping.shift_max.platform.isize := return isize.bits
  definition num.wrapping.shift_max.platform.usize := return usize.bits

  definition usize.overflowing_shl (a b : nat) :=
  return (unary_unsigned_bitwise_op usize.bits (λ a, bitvec.shl a b) (a % usize.bits), a ≥ᵇ usize.bits)
  definition usize.overflowing_shr (a b : nat) :=
  return (unary_unsigned_bitwise_op usize.bits (λ a, bitvec.ushr a b) (a % usize.bits), a ≥ᵇ usize.bits)

  definition isize.overflowing_shl (a : int) (b : nat) :=
  return (unary_signed_bitwise_op isize.bits (λ n a, bitvec.shl a b) (a % isize.bits), a ≥ᵇ isize.bits)
  definition isize.overflowing_shr (a : int) (b : nat) :=
  return (unary_signed_bitwise_op isize.bits (λ n a, bitvec.sshr a b) (a % isize.bits), a ≥ᵇ isize.bits)

  namespace ops
    structure FnOnce [class] (Self : Type₁) (Args : Type₁) (Output : Type₁) :=
    (call_once : Self → Args → sem Output)

    definition FnOnce.mk_simple := @FnOnce.mk

    structure FnMut [class] (Self : Type₁) (Args : Type₁) (Output : Type₁) extends FnOnce Self Args Output :=
    (call_mut : Self → Args → sem (Output × Self))
    attribute [coercion] FnMut.to_FnOnce

    definition FnMut.mk_simple [constructor] {Self Args Output : Type₁} (call_mut : Self → Args → sem (Output × Self)) :
      FnMut Self Args Output :=
    ⦃FnMut, call_mut := call_mut,
     call_once := λ self args, sem.map prod.pr1 (call_mut self args)⦄

    structure Fn [class] (Self : Type₁) (Args : Type₁) (Output : Type₁) extends FnMut Self Args Output :=
    (call : Self → Args → sem Output)
    attribute [coercion] Fn.to_FnMut

    definition Fn.mk_simple [constructor] {Self Args Output : Type₁} (call : Self → Args → sem Output) :
      Fn Self Args Output :=
    ⦃Fn, call := call, call_once := call,
     call_mut := λ self args, do x ← call self args;
       return (x, self)⦄
  end ops
end core

export [class] [coercion] core.ops

notation `let'` binder ` ← ` x `; ` r:(scoped f, f x) := r
attribute sem [irreducible]
