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

namespace test

inductive Point :=
mk {} : i32 → i32 → Point

definition main : sem (unit) :=
let' p ← (Point.mk ((10 : int)) ((11 : int)));
let' x ← (match (p) with Point.mk x0 x1 := x0 end);
let' t0 ← (x);
let' px ← (t0);
let' ret ← (⋆);
return (ret)


end test