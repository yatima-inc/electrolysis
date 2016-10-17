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

inductive Foo :=
| Bar {} : Foo

definition Foo.discr (self : Foo) : isize := match self with
| Foo.Bar := 123
end

definition main : sem (unit) :=
let' t2 ← (Foo.Bar);
do «$tmp0» ← (isize_to_u32 (Foo.discr (t2)));
let' x ← «$tmp0»;
let' ret ← (⋆);
return (ret)


end test