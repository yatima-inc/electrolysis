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

definition LEVELS : sem u32 :=
let' ret ← ((0 : nat));
return (ret)


end test