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

definition test.foo : sem (i32) :=
let' a ← (1 : int);
let' t2 ← a;
let' ret ← t2;
return (ret)


