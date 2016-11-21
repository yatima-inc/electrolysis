import core.generated

noncomputable theory

open bool
open [class] classical
open [notation] function
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

structure test.S := mk {} ::
(x : (array i32 2))

definition test.foo (sₐ : (test.S)) : sem (i32) :=
let' s ← sₐ;
let' t4 ← list.length (test.S.x s);
let' t5 ← (0 : nat) <ᵇ t4;
let' p ← (lens.index _ (0 : nat) ∘ₗ lens.mk (return ∘ test.S.x) (λ (o : test.S) i, return ⦃ test.S, x := i ⦄));
do «$tmp» ← lens.get p s;
do «$tmp0» ← lens.get p s;
let' t6 ← «$tmp0»;
let' ret ← t6;
return (ret)


