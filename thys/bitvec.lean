/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich

Basic operations on bitvectors.
-/
import move
import theories.move

open bool
open eq.ops
open nat
open prod
open subtype
open tuple

attribute bool.cond [unfold 2]

lemma nat.mod_2_eq_0_of_ne_1 {n : ℕ} (h : n % 2 ≠ 1) : n % 2 = 0 :=
match nat.lt_trichotomy (n % 2) 1 with
| or.inl lt := nat.eq_zero_of_le_zero (nat.le_of_lt_succ lt)
| or.inr (or.inl eq) := by contradiction
| or.inr (or.inr gt) :=
  have n % 2 ≤ 1, from nat.le_of_lt_succ (nat.mod_lt n (show 2 > 0, from dec_trivial)),
  false.elim (nat.lt_le_antisymm gt this)
end

definition bitvec [reducible] (n : ℕ) := tuple bool n

namespace bitvec
-- Create a zero bitvector
protected definition zero [reducible] (n : ℕ) : bitvec n := replicate n ff

-- Create a bitvector with the constant one
protected definition one : Π (n : ℕ), bitvec n
| 0 := replicate 0 ff
| (succ n) := replicate n ff ++ [tt]

protected definition cong [unfold 4] {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| (tag x p) := tag x (h ▸ p)

section shift
  variable {n : ℕ}

  -- shift left
  definition shl (x : bitvec n) (i : ℕ) : bitvec n :=
  let r := dropn i x ++ replicate (min n i) ff in
  have length r = n, by rewrite [nat.sub_add_min_cancel],
  bitvec.cong this r

  definition fill_shr (x : bitvec n) (i : ℕ) (fill : bool) : bitvec n :=
  let y := replicate (min n i) fill ++ firstn (n-i) x in
  have length y = n, from if h : i ≤ n then
    by rewrite [↑length, min_eq_right h, min_eq_left !sub_le, -nat.add_sub_assoc h,
      nat.add_sub_cancel_left]
  else
    have h : i ≥ n, from le_of_not_ge h,
    by rewrite [↑length, min_eq_left h, sub_eq_zero_of_le h, min_eq_left !zero_le],
  bitvec.cong this y

  -- unsigned shift right
  definition ushr (x : bitvec n) (i : ℕ) : bitvec n :=
  fill_shr x i ff

  -- signed shift right
  definition sshr {m : ℕ} (x : bitvec (succ m)) (i : ℕ) : bitvec (succ m) :=
  head x :: fill_shr (tail x) i (head x)

end shift

section bitwise
  variable {n : ℕ}

  definition not [reducible] : bitvec n → bitvec n := map bnot
  definition and [reducible] : bitvec n → bitvec n → bitvec n := map₂ band
  definition or  [reducible] : bitvec n → bitvec n → bitvec n := map₂ bor
  definition xor [reducible] : bitvec n → bitvec n → bitvec n := map₂ bxor

  infix && := and
  infix || := or

  lemma or_zero : Π{n : ℕ} (v : bitvec n), v || bitvec.zero n = v
  | 0 v := by rewrite [tuple0_eq_nil v]
  | (succ n) v := by rewrite [-eta v, replicate_succ, map₂_cons, bor_ff, or_zero]

  lemma and_or_distrib_right {n : ℕ} (x y z : bitvec n) : (x || y) && z = (x && z) || (y && z) :=
  begin
    induction n with n ih,
    { rewrite [tuple0_eq_nil x, tuple0_eq_nil y, tuple0_eq_nil z] },
    { rewrite [-eta x, -eta y, -eta z, +map₂_cons, band_bor_distrib, ih] }
  end

  lemma and_self : Π{n : ℕ} (v : bitvec n), v && v = v
  | 0 v := by rewrite [tuple0_eq_nil v]
  | (succ n) v := by rewrite [-eta v, map₂_cons, band_self, and_self]

  lemma and.comm : Π{n : ℕ} (x y : bitvec n), x && y = y && x
  | 0 x y := by rewrite [tuple0_eq_nil x, tuple0_eq_nil y]
  | (succ n) x y := by rewrite [-eta x, -eta y, +map₂_cons, band_comm, and.comm]

  lemma and_zero : Π{n : ℕ} (v : bitvec n), v && bitvec.zero n = bitvec.zero n
  | 0 v := by rewrite [tuple0_eq_nil v]
  | (succ n) v := by rewrite [-eta v, replicate_succ, map₂_cons, band_ff, and_zero]

  lemma and_or_cancel : Π{n : ℕ} (x y : bitvec n), (x || y) && y = y
  | 0 x y := by rewrite [tuple0_eq_nil x, tuple0_eq_nil y]
  | (succ n) x y := begin
    rewrite [-eta x, -eta y, +map₂_cons, and_or_cancel],
    congruence,
    cases head y,
    { rewrite [band_ff] },
    { rewrite [bor_tt, tt_band] }
  end
end bitwise

section arith
  variable {n : ℕ}

  protected definition xor3 (x:bool) (y:bool) (c:bool) := bxor (bxor x y) c
  protected definition carry (x:bool) (y:bool) (c:bool) :=
    x && y || x && c || y && c

  protected definition neg : bitvec n → bitvec n
  | x :=
    let f := λy c, (y || c, bxor y c) in
    pr₂ (mapAccumR f x ff)

  -- Add with carry (no overflow)
  definition adc : bitvec n → bitvec n → bool → bitvec (n+1)
  | x y c :=
    let f := λx y c, (bitvec.carry x y c, bitvec.xor3 x y c) in
    let z := tuple.mapAccumR₂ f x y c in
    (pr₁ z) :: (pr₂ z)

  protected definition add : bitvec n → bitvec n → bitvec n
  | x y := tail (adc x y ff)

  protected definition borrow (x:bool) (y:bool) (b:bool) :=
    bnot x && y || bnot x && b || y && b

  -- Subtract with borrow
  definition sbb : bitvec n → bitvec n → bool → bool × bitvec n
  | x y b :=
    let f := λx y c, (bitvec.borrow x y c, bitvec.xor3 x y c) in
    tuple.mapAccumR₂ f x y b

  protected definition sub : bitvec n → bitvec n → bitvec n
  | x y := pr₂ (sbb x y ff)

  definition bitvec_has_zero [instance] : has_zero (bitvec n) := has_zero.mk (bitvec.zero n)
  definition bitvec_has_one  [instance] : has_one (bitvec n)  := has_one.mk (bitvec.one n)
  definition bitvec_has_add  [instance] : has_add (bitvec n)  := has_add.mk bitvec.add
  definition bitvec_has_sub  [instance] : has_sub (bitvec n)  := has_sub.mk bitvec.sub
  definition bitvec_has_neg  [instance] : has_neg (bitvec n)  := has_neg.mk bitvec.neg

  protected definition mul : bitvec n → bitvec n → bitvec n
  | x y :=
    let f := λr b, cond b (r + r + y) (r + r) in
    list.foldl f 0 (to_list x)

  definition bitvec_has_mul  [instance] : has_mul (bitvec n)  := has_mul.mk bitvec.mul

  definition ult : bitvec n → bitvec n → bool := λx y, pr₁ (sbb x y ff)
  definition ugt : bitvec n → bitvec n → bool := λx y, ult y x
  definition ule : bitvec n → bitvec n → bool := λx y, bnot (ult y x)
  definition uge : bitvec n → bitvec n → bool := λx y, ule y x

  definition slt : bitvec (succ n) → bitvec (succ n) → bool := λx y,
    cond (head x)
         (cond (head y)
               (ult (tail x) (tail y))  -- both negative
               tt)                         -- x is negative and y is not
         (cond (head y)
               ff                          -- y is negative and x is not
               (ult (tail x) (tail y))) -- both positive
  definition sgt : bitvec (succ n) → bitvec (succ n) → bool := λx y, slt y x
  definition sle : bitvec (succ n) → bitvec (succ n) → bool := λx y, bnot (slt y x)
  definition sge : bitvec (succ n) → bitvec (succ n) → bool := λx y, sle y x
end arith

section convert
  section
  parameters {A : Type} [has_add A] [has_zero A] [has_one A]

  protected definition of [has_div A] [has_mod A] [decidable_eq A] : Π(n : nat), A → bitvec n
  | 0 x := nil
  | (succ n) x := of n (x / 2) ++ [if x % 2 = 1 then tt else ff]

  parameter (A)
  definition bitsTo [reducible] (v : list bool) : A :=
  list.foldl (λr b, r + r + cond b 1 0) 0 v

  protected definition to {n : nat} (v : bitvec n) : A :=
  bitsTo (to_list v)
  end

  lemma of_zero : Π(n : ℕ), bitvec.of n (0:ℕ) = bitvec.zero n
  | 0 := rfl
  | (succ n) := by rewrite [↑bitvec.of, if_neg (show (0:ℕ) % 2 ≠ 1, from dec_trivial),
    nat.zero_div, of_zero, replicate_succ_right]

  lemma of_one : Π{n : ℕ}, bitvec.of (succ n) (1:ℕ) = replicate n ff ++ [tt]
  | 0 := rfl
  | (succ n) := by rewrite [↑bitvec.of, (show (1:ℕ) / 2 = 0, from dec_trivial), of_zero]

  open list

  lemma bitsTo_aux : Π bs x,
    foldl (λ r b, r + r + bool.cond b 1 0) x bs = x * 2^length bs + bitsTo ℕ bs :=
  begin
    intro bs, induction bs with b bs ih, all_goals intro x,
    { rewrite [↑foldl, ↑length, pow_zero], simp },
    { rewrite [↑foldl, -mul_two, ih, nat.right_distrib, mul.assoc, -pow_succ, ↑bitsTo at {2}, ↑foldl,
        +zero_add, ih (cond b 1 0), add.assoc] }
  end

  lemma bitsTo_cons (b) (bs) : bitsTo ℕ (b::bs) = cond b 1 0 * 2^length bs + bitsTo ℕ bs :=
  by rewrite [↑bitsTo at {1}, ↑foldl, bitsTo_aux, +zero_add]

  lemma bitsTo_snoc (b) (bs) : bitsTo ℕ (bs++[b]) = 2 * bitsTo ℕ bs + cond b 1 0 :=
  begin
    induction bs with b bs ih,
    { esimp },
    { rewrite [append_cons, +foldl_cons, bitsTo_aux, bitsTo_aux bs, ih, nat.left_distrib,
        -mul.assoc, length_append, length_cons, length_nil, +zero_add, add_one, pow_succ,
        -mul.assoc, {_*2}mul.comm, add.assoc] }
  end

  lemma bitsTo_append : Π bs bs', bitsTo ℕ (bs ++ bs') = bitsTo ℕ bs * 2^length bs' + bitsTo ℕ bs'
  | [] bs' := by simp
  | (b::bs) bs' := by rewrite [bitsTo_cons, append_cons, bitsTo_cons, bitsTo_append, nat.right_distrib,
    mul.assoc, length_append, pow_add, add.assoc]

  lemma bitsTo_replicate_ff : Π(n : ℕ), bitsTo ℕ (replicate n ff) = 0
  | 0 := rfl
  | (succ n) := by rewrite [↑replicate, bitsTo_cons, cond_ff, zero_mul, bitsTo_replicate_ff]

  lemma to_of : Π {n x : ℕ} (h : x < 2^n), bitvec.to ℕ (bitvec.of n x) = x
  | 0 0 h := rfl
  | 0 (succ x) h := false.elim (lt_le_antisymm h (succ_le_succ !zero_le))
  | (succ n) x h := begin
    note ih := @to_of n (x / 2) (nat.div_lt_of_lt_mul (!mul.comm ▸ h)),
    apply generalize_with_eq (bitvec.of n (x / 2)), intro v' v'_eq,
    cases v' with bs _,
    rewrite [↑bitvec.of, ↑bitvec.to, v'_eq at *,
      ↑bitvec.to at ih, ↑to_list at *, bitsTo_snoc, ih],
    cases (_ : decidable (x % 2 = 1)) with hodd heven,
    { rewrite [▸*, nat.eq_div_mul_add_mod x 2 at {2}, hodd, mul.comm] },
    { rewrite [▸*, nat.eq_div_mul_add_mod x 2 at {2}, nat.mod_2_eq_0_of_ne_1 heven, mul.comm] }
  end

  lemma of_to : Π {n : ℕ} (v : bitvec n), bitvec.of n (bitvec.to ℕ v) = v
  | 0 v := by rewrite [tuple0_eq_nil, tuple0_eq_nil v]
  | (succ n) (tag v h) := begin
    apply eq_of_list_eq,
    rewrite [↑bitvec.to],
    have v ≠ nil, from ne_nil_of_length_eq_succ h,
    note bl := eq.symm (butlast_append_last `v ≠ nil`),
    rewrite [↑bitvec.of,
      bl at {1}, if_congr (iff.of_eq (bl ▸ rfl)) rfl rfl,
      bitsTo_snoc, add.comm, !nat.add_mul_div_self_left (show 2 > 0, from dec_trivial),
      add_mul_mod_self_left],
    krewrite [to_list_append],
    have cond (last v this) (1:ℕ) 0 < 2, begin
      cases last v this, all_goals (esimp; apply dec_trivial),
    end,
    krewrite [▸*, div_eq_zero_of_lt this, zero_add,
      of_to (tag (butlast v) (succ.inj (h ▸ length_butlast_nonnil `v ≠ nil`)))],
    have ∀ b, ite (cond b (1:ℕ) 0 % 2 = 1) tt ff = b, begin
      intro b, cases b, all_goals esimp
    end,
    rewrite [this, ▸*, -bl]
  end

  lemma to_lt : Π {n : ℕ} (v : bitvec n), bitvec.to ℕ v < 2^n
  | 0 v := by rewrite [tuple0_eq_nil, ▸*, ↑bitvec.to, foldl_nil]; apply dec_trivial
  | (succ n) v := begin
    rewrite [↑bitvec.to, -eta v, to_list_cons, bitsTo_cons, pow_succ, two_mul, length_to_list],
    apply λ h, add_lt_add_of_le_of_lt h (to_lt (tail v)),
    cases head v,
    { esimp, rewrite zero_mul, apply zero_le },
    { esimp, rewrite one_mul },
  end
end convert
end bitvec
