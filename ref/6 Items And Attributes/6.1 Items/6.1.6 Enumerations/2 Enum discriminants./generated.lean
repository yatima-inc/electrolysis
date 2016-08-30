import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

inductive Foo :=
| Bar {} : Foo

/- main: unimplemented: rvalue tmp0 as u32 (Misc) -/

end test