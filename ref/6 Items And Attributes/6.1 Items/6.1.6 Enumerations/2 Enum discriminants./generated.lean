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

definition Foo.discr (self : Foo) : isize := match self with
| Foo.Bar := 123
end

definition main : sem (unit) :=
let' t0 ← Foo.Bar;
do tmp__ ← (isize_to_u32 (Foo.discr t0));
let' x ← tmp__;
let' ret ← ⋆;
return (ret)


end test