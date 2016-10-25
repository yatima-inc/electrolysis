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

structure test.main.Point := mk {} ::
(x : i64)
(y : i64)

inductive test.main.TuplePoint :=
mk {} : i64 → i64 → test.main.TuplePoint

definition test.main : sem (unit) :=
let' t3 ← test.main.Point.mk (10 : int) (20 : int);
let' t2 ← (test.main.Point.x t3);
let' t1 ← t2;
let' t6 ← test.main.TuplePoint.mk (10 : int) (20 : int);
let' t5 ← match t6 with test.main.TuplePoint.mk x0 x1 := x0 end;
let' t4 ← t5;
let' ret ← ⋆;
return (ret)


