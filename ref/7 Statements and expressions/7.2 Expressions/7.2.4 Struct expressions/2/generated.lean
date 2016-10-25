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

structure test.main.Point3d := mk {} ::
(x : i32)
(y : i32)
(z : i32)

definition test.main : sem (unit) :=
let' base ← test.main.Point3d.mk (1 : int) (2 : int) (3 : int);
let' t2 ← test.main.Point3d.mk (test.main.Point3d.x base) (0 : int) (10 : int);
let' ret ← ⋆;
return (ret)


