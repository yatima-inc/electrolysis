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
let' ret ← (0 : int);
return (ret)


definition test.main : sem (unit) :=
dostep «$tmp» ← @test.add (1 : int) (2 : int);
let' «x$1» ← «$tmp»;
let' ret ← ⋆;
return (⋆)


