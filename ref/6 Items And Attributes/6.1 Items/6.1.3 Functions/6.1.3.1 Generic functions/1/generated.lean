import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

definition foo {A : Type₁} {B : Type₁} (x : A) (y : B) : sem (unit) :=
let' ret ← ⋆;
return (ret)


end test