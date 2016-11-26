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
let' x ← xₐ;
let' y ← yₐ;
let' ret ← (0 : int);
return (ret)


definition test.main : sem (unit) :=
dostep «$tmp» ← @test.add (1 : int) (2 : int);
let' x ← «$tmp»;
let' ret ← ⋆;
return (⋆)


