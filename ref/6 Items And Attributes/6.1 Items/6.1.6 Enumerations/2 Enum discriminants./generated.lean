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

inductive test.Foo :=
| Bar {} : test.Foo

definition test.Foo.discr (self : test.Foo) : isize := match self with
| test.Foo.Bar := 123
end

definition test.main : sem (unit) :=
let' t2 ← test.Foo.Bar;
do «$tmp0» ← (isize_to_u32 (test.Foo.discr t2));
let' x ← «$tmp0»;
let' ret ← ⋆;
return (ret)


