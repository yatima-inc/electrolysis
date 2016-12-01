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
let' «x$3» ← @lens.id i32;
let' «y$4» ← yₐ;
let' t5 ← «y$4»;
do xₐ ← lens.set «x$3» xₐ t5;
let' ret ← ⋆;
return (⋆, xₐ)


definition test.foo : sem (i32) :=
let' «x$1» ← (1 : int);
let' t4 ← @lens.id i32;
do «$tmp» ← lens.get t4 «x$1»;
let' t3 ← (t4);
do «$tmp» ← lens.get t3 «x$1»;
do «$tmp0» ← lens.get t3 «x$1»;
dostep «$tmp» ← @test.set «$tmp0» (2 : int);
match «$tmp» with (t2, «t3$») :=
do «x$1» ← lens.set t3 «x$1» «t3$»;
let' t5 ← «x$1»;
let' ret ← t5;
return (ret)
end


