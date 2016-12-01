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

definition test.add (xₐ : i32) (yₐ : i32) : sem (i32) :=
let' «x$3» ← xₐ;
let' «y$4» ← yₐ;
let' t5 ← «x$3»;
let' t6 ← «y$4»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits t5 t6);
let' t7 ← «$tmp0»;
let' ret ← t7.1;
return (ret)


definition test.first («$a1» : (i32 × i32)) : sem (i32) :=
let' «value$2» ← «$a1».1;
let' t3 ← «value$2»;
let' ret ← t3;
return (ret)


