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
let' s ← sₐ;
let' i ← iₐ;
let' t5 ← i;
let' t6 ← list.length (test.S.x s);
let' t7 ← t5 <ᵇ t6;
do «$tmp2» ← sem.lift_opt (list.update (test.S.x s) t5 (2 : int));
let' s ← ⦃ test.S, x := «$tmp2» ⦄;
let' t8 ← s;
let' ret ← t8;
return (ret)


