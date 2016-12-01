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

definition test.foo (sₐ : (test.S)) (iₐ : usize) : sem ((test.S)) :=
let' «s$3» ← sₐ;
let' «i$4» ← iₐ;
let' t5 ← «i$4»;
let' t6 ← list.length (test.S.x «s$3»);
let' t7 ← t5 <ᵇ t6;
do «$tmp2» ← sem.lift_opt (list.update (test.S.x «s$3») t5 (2 : int));
let' «s$3» ← ⦃ (test.S), x := «$tmp2» ⦄;
let' t8 ← «s$3»;
let' ret ← t8;
return (ret)


