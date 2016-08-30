import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

structure Point := mk {} ::
(x : i32)
(y : i32)

definition main : sem (unit) :=
let' p ← Point.mk (10 : int) (11 : int);
let' t0 ← (Point.x p);
let' px ← t0;
let' ret ← ⋆;
return (ret)


end test