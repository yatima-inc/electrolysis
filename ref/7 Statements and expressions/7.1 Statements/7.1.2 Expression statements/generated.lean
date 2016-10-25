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
let' t1 ← (1 : int);
let' ret ← ⋆;
return (ret)


