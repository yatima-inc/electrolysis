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

definition test.foo {T : Type₁} [«core.default.Default T» : core.default.Default T] (xₐ : (slice T)) : sem (unit) :=
let' x ← xₐ;
let' ret ← ⋆;
return (⋆)


definition test.main : sem (unit) :=
do promoted_0 ←
let' t1 ← [(1 : int), (2 : int)];
let' ret ← t1;
return (ret)
;
let' t4 ← promoted_0;
let' t3 ← t4;
let' t2 ← t3;
dostep «$tmp» ← @test.foo _ (@core.«i32 as core.default.Default» ) t2;
let' t1 ← «$tmp»;
let' ret ← ⋆;
return (⋆)


