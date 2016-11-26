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

definition test.main : sem (unit) :=
let' x ← (1 : int);
let' x ← (2 : int);
let' ret ← ⋆;
return (⋆)


