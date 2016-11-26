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

structure test.Name := mk {} ::

structure test.Animal.Cat.struct := mk {} ::
(name : (test.Name))
(weight : u32)

inductive test.Animal :=
| Dog {} : (test.Name) → u32 → test.Animal
| Cat {} : test.Animal.Cat.struct → test.Animal

definition test.main : sem (unit) :=
let' t2 ← test.Name.mk;
let' a ← test.Animal.Dog t2 (37 : nat);
let' t3 ← test.Name.mk;
let' a ← test.Animal.Cat (test.Animal.Cat.struct.mk t3 (2 : nat));
let' ret ← ⋆;
return (⋆)


