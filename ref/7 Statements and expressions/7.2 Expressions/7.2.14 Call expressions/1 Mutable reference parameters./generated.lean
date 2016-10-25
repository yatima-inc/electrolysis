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

definition test.add (xₐ : i32) (yₐ : i32) : sem (unit × i32) :=
let' x ← @lens.id i32;
let' y ← yₐ;
let' t5 ← y;
do «$tmp0» ← sem.map (λx, (x, tt)) (do «$tmp0» ← lens.get x xₐ;
checked.sadd i32.bits «$tmp0» t5);
let' t6 ← «$tmp0»;
do xₐ ← lens.set x xₐ t6.1;
let' ret ← ⋆;
return (ret, xₐ)


definition test.foo : sem (i32) :=
let' x ← (1 : int);
let' t4 ← @lens.id i32;
let' t3 ← (t4);
do «$tmp0» ← lens.get t3 x;
dostep «$tmp» ← @test.add «$tmp0» (2 : int);
match «$tmp» with (t2, «t3$») :=
do x ← lens.set t3 x «t3$»;
let' t5 ← x;
let' ret ← t5;
return (ret)
end


