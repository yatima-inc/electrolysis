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

definition test.foo (sₐ : (test.S)) : sem (i32 × (test.S)) :=
let' s ← @lens.id (test.S);
do «$tmp0» ← do «$tmp0» ← do «$tmp0» ← lens.get s sₐ;
return ((test.S.x «$tmp0»));
return (list.length «$tmp0»);
let' t4 ← «$tmp0»;
let' t5 ← (0 : nat) <ᵇ t4;
let' p ← (lens.index _ (0 : nat) ∘ₗ lens.mk (return ∘ test.S.x) (λ (o : test.S) i, return ⦃ test.S, x := i ⦄) ∘ₗ s);
do «$tmp0» ← lens.get p sₐ;
let' t6 ← «$tmp0»;
let' ret ← t6;
return (ret, sₐ)


