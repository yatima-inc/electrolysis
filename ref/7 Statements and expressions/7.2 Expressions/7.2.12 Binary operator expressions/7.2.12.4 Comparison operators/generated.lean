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
let' x ← xₐ;
let' y ← yₐ;
let' t5 ← x;
let' t6 ← y;
let' ret ← t5 <ᵇ t6;
return (ret)


