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
let' x ← (5 : int);
let' t2 ← x;
let' ret ← t2;
return (ret)


