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
let' t1 ← [(1 : int), (2 : int), (3 : int), (4 : int)];
let' t2 ← ["a", "b", "c", "d"];
let' t3 ← list.replicate 128 (0 : int);
let' t4 ← [(0 : nat), (0 : nat), (0 : nat), (0 : nat)];
let' ret ← ⋆;
return (ret)


