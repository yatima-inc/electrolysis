import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

structure Cookie := mk {} ::

definition main : sem (unit) :=
let' t0 ← Cookie.mk;
let' t1 ← Cookie.mk;
let' t2 ← Cookie.mk;
let' t3 ← Cookie.mk;
let' c ← [t0, t1, t2, t3];
let' ret ← ⋆;
return (ret)


end test