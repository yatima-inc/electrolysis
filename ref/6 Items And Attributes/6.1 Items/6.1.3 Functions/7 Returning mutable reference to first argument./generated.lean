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

definition test.foo (xsₐ : (slice i32)) : sem ((lens (slice i32) i32) × (slice i32)) :=
let' xs ← @lens.id (slice i32);
do «$tmp0» ← do «$tmp0» ← lens.get xs xsₐ;
return (list.length «$tmp0»);
let' t4 ← «$tmp0»;
let' t5 ← (0 : nat) <ᵇ t4;
let' t3 ← (lens.index _ (0 : nat) ∘ₗ xs);
do «$tmp» ← lens.get t3 xsₐ;
let' ret ← (t3);
do «$tmp» ← lens.get ret xsₐ;
return (ret, xsₐ)


