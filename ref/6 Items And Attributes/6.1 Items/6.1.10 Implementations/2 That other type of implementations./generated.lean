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

definition test.Point.log (selfₐ : (test.Point)) : sem (unit) :=
let' self ← selfₐ;
let' ret ← ⋆;
return (ret)


definition test.main : sem (unit) :=
let' my_point ← test.Point.mk (10 : int) (11 : int);
let' t3 ← my_point;
dostep «$tmp» ← @test.Point.log t3;
let' t2 ← «$tmp»;
let' ret ← ⋆;
return (ret)


