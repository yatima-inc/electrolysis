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

definition test.set (xₐ : i32) (yₐ : i32) : sem (unit × i32) :=
let' x ← @lens.id i32;
let' y ← yₐ;
let' t5 ← y;
do xₐ ← lens.set x xₐ t5;
let' ret ← ⋆;
return (ret, xₐ)


definition test.foo : sem (i32) :=
let' x ← (1 : int);
let' t4 ← @lens.id i32;
do «$tmp» ← lens.get t4 x;
let' t3 ← (t4);
do «$tmp» ← lens.get t3 x;
do «$tmp0» ← lens.get t3 x;
dostep «$tmp» ← @test.set «$tmp0» (2 : int);
match «$tmp» with (t2, «t3$») :=
do x ← lens.set t3 x «t3$»;
let' t5 ← x;
let' ret ← t5;
return (ret)
end


