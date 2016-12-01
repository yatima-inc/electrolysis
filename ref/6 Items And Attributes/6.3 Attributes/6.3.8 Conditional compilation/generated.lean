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

definition test.foo : sem (unit) :=
let' ret ← ⋆;
return (⋆)


definition test.not_foo : sem (unit) :=
let' ret ← ⋆;
return (⋆)


definition test.not_test : sem (unit) :=
let' ret ← ⋆;
return (⋆)


