import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

inductive Animal :=
| Dog {} : Animal
| Cat {} : Animal

definition Animal.discr (self : Animal) : isize := match self with
| Animal.Dog := 0
| Animal.Cat := 1
end

definition main : sem (unit) :=
let' a ← Animal.Dog;
let' a ← Animal.Cat;
let' ret ← ⋆;
return (ret)


end test