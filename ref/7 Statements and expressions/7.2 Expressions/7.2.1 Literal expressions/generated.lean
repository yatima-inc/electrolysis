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
let' t1 ← ⋆;
let' t2 ← "hello";
let' t3 ← (5 : int);
let' ret ← ⋆;
return (⋆)


