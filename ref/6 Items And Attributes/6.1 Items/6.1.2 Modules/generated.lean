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

inductive foo.Bar :=
mk {} : (core.cmp.Ordering) → foo.Bar

end test