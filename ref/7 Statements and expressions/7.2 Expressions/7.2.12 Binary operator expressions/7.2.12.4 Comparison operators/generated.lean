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

definition test.foo (xₐ : i32) (yₐ : i32) : sem (bool) :=
let' «x$3» ← xₐ;
let' «y$4» ← yₐ;
let' t5 ← «x$3»;
let' t6 ← «y$4»;
let' ret ← t5 <ᵇ t6;
return (ret)


