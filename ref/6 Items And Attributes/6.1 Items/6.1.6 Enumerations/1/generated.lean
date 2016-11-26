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

inductive test.Animal :=
| Dog {} : test.Animal
| Cat {} : test.Animal

definition test.Animal.discr (self : test.Animal) : isize := match self with
| test.Animal.Dog := 0
| test.Animal.Cat := 1
end

definition test.main : sem (unit) :=
let' a ← test.Animal.Dog;
let' a ← test.Animal.Cat;
let' ret ← ⋆;
return (⋆)


