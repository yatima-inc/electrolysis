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

structure Cookie := mk {} ::

definition main : sem (unit) :=
let' t2 ← (Cookie.mk);
let' t3 ← (Cookie.mk);
let' t4 ← (Cookie.mk);
let' t5 ← (Cookie.mk);
let' c ← ([(t2), (t3), (t4), (t5)]);
let' ret ← (⋆);
return (ret)


end test