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

definition test.foo (xₐ : (array u32 2)) : sem ((slice u32)) :=
let' «x$2» ← xₐ;
let' t3 ← «x$2»;
let' ret ← t3;
return (ret)


