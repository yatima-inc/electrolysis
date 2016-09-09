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

definition foo {T : Type₁} [«core.default.Default T» : core.default.Default T] (xₐ : (slice T)) : sem (unit) :=
let' x ← (xₐ);
let' ret ← (⋆);
return (ret)


definition main : sem (unit) :=
do promoted_0 ←
let' t0 ← ([((1 : int)), ((2 : int))]);
let' ret ← (t0);
return (ret)
;
let' t3 ← (promoted_0);
let' t2 ← (t3);
let' t1 ← (t2);
dostep «$tmp» ← @foo _ (core.«i32 as core.default.Default» ) (t1);
let' t0 ← «$tmp»;
let' ret ← (⋆);
return (ret)


end test