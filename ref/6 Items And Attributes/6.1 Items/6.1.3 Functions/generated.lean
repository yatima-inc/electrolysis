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

definition add (xₐ : i32) (yₐ : i32) : sem (i32) :=
let' x ← (xₐ);
let' y ← (yₐ);
let' t5 ← (x);
let' t6 ← (y);
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits (t5) (t6));
let' t7 ← «$tmp0»;
let' ret ← ((t7).1);
return (ret)


definition first (a1 : (i32 × i32)) : sem (i32) :=
let' value ← ((a1).1);
let' t3 ← (value);
let' ret ← (t3);
return (ret)


end test