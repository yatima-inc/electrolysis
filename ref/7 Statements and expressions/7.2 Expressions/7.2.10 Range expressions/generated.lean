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
let' t2 ← (1 : int);
let' t3 ← (2 : int);
let' t1 ← core.ops.Range.mk t2 t3;
let' t5 ← (3 : int);
let' t4 ← core.ops.RangeFrom.mk t5;
let' t7 ← (4 : int);
let' t6 ← core.ops.RangeTo.mk t7;
let' t8 ← core.ops.RangeFull.mk;
let' ret ← ⋆;
return (⋆)


