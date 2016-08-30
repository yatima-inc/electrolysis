import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

definition add (x : i32) (y : i32) : sem (i32) :=
let' t0 ← x;
let' t1 ← y;
let' t2 ← (t0 + t1, true);
let' ret ← t2.1;
return (ret)


definition first (p0 : (i32 × i32)) : sem (i32) :=
let' value ← p0.1;
let' t0 ← value;
let' ret ← t0;
return (ret)


end test