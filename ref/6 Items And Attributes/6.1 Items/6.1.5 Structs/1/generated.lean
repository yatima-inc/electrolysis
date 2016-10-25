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

structure test.Point := mk {} ::
(x : i32)
(y : i32)

definition test.main : sem (unit) :=
let' p ← test.Point.mk (10 : int) (11 : int);
let' t3 ← (test.Point.x p);
let' px ← t3;
let' ret ← ⋆;
return (ret)


