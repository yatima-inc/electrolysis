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

/- LEVELS: unimplemented: mutable static "LEVELS" -/

/- bump_levels_unsafe1: failed dependencies LEVELS -/

definition LEVELS2 : sem u32 :=
let' ret ← ((0 : nat));
return (ret)


end test