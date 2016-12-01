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
let' t2 ← [(1 : int), (2 : int), (3 : int), (4 : int)];
let' t3 ← list.length t2;
let' t4 ← (0 : nat) <ᵇ t3;
do «$tmp0» ← core.«[T] as core.slice.SliceExt».get_unchecked t2 (0 : nat);
let' t1 ← «$tmp0»;
let' ret ← t1;
return (ret)


definition test.bar : sem (string) :=
let' «n$1» ← (10 : nat);
let' t4 ← ["a", "b"];
let' t5 ← «n$1»;
let' t6 ← list.length t4;
let' t7 ← t5 <ᵇ t6;
do «$tmp0» ← core.«[T] as core.slice.SliceExt».get_unchecked t4 t5;
let' t3 ← «$tmp0»;
let' «y$2» ← t3;
let' ret ← «y$2»;
return (ret)


