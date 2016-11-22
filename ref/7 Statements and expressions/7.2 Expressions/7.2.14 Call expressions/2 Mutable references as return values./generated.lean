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
let' t5 ← «$tmp0»;
let' t6 ← (0 : nat) <ᵇ t5;
let' t4 ← (lens.index _ (0 : nat) ∘ₗ xs);
do «$tmp» ← lens.get t4 xsₐ;
let' t3 ← (t4);
do «$tmp» ← lens.get t3 xsₐ;
let' ret ← (t3);
do «$tmp» ← lens.get ret xsₐ;
return (ret, xsₐ)


definition test.bar (xsₐ : (slice i32)) : sem (unit × (slice i32)) :=
let' xs ← @lens.id (slice i32);
let' t4 ← (xs);
do «$tmp» ← lens.get t4 xsₐ;
do «$tmp0» ← lens.get t4 xsₐ;
dostep «$tmp» ← @test.foo «$tmp0»;
match «$tmp» with («t3$», «t4$») :=
do xsₐ ← lens.set t4 xsₐ «t4$»;
let' t3 ← («t3$» ∘ₗ t4);
do xsₐ ← lens.set t3 xsₐ (2 : int);
let' ret ← ⋆;
return (ret, xsₐ)
end


