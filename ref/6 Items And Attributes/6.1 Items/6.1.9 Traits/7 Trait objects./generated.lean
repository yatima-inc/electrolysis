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

structure test.Shape [class] (Self : Type₁) := mk

definition test.Shape.draw {Self : Type₁} [«test.Shape Self» : test.Shape Self] (selfₐ : Self) : sem (unit) :=
let' «self$2» ← selfₐ;
let' ret ← ⋆;
return (⋆)


/- test.main: unimplemented: trait object -/

definition test.«i32 as test.Shape» [instance] := ⦃
  test.Shape i32
⦄

