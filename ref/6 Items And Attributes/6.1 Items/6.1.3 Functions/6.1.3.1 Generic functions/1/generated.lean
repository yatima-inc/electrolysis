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

definition test.foo {A : Type₁} {B : Type₁} (xₐ : A) (yₐ : B) : sem (unit) :=
let' «x$3» ← xₐ;
let' «y$4» ← yₐ;
let' ret ← ⋆;
return (⋆)


