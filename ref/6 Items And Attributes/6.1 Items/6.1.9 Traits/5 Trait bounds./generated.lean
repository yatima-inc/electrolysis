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

structure test.Surface := mk {} ::


structure test.Shape [class] (Self : Type₁) :=
(draw : (Self → (test.Surface) → sem (unit)))

definition test.draw_twice {T : Type₁} [«test.Shape T» : test.Shape T] (surfaceₐ : (test.Surface)) (shₐ : T) : sem (unit) :=
let' «surface$3» ← surfaceₐ;
let' «sh$4» ← shₐ;
let' t6 ← «sh$4»;
let' t9 ← «surface$3»;
let' t8 ← t9;
dostep «$tmp» ← @test.Shape.draw T «test.Shape T» t6 t8;
let' t5 ← «$tmp»;
let' t11 ← «sh$4»;
let' t13 ← «surface$3»;
let' t12 ← t13;
dostep «$tmp» ← @test.Shape.draw T «test.Shape T» t11 t12;
let' t10 ← «$tmp»;
let' ret ← ⋆;
return (⋆)


