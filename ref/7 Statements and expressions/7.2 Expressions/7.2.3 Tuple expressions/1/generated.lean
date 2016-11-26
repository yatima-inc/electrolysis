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
let' t1 ← ((0 : int), (4 : int));
let' t2 ← ("a", (4 : nat), tt);
let' ret ← ⋆;
return (⋆)


