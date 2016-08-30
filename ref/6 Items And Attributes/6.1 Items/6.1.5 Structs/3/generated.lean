import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

structure Cookie := «{{constructor}}» {} ::

definition main : sem (unit) :=
let' t0 ← Cookie.«{{constructor}}»;
let' t1 ← Cookie.«{{constructor}}»;
let' t2 ← Cookie.«{{constructor}}»;
let' t3 ← Cookie.«{{constructor}}»;
let' c ← [t0, t1, t2, t3];
let' ret ← ⋆;
return (ret)


end test