import collections.generated
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

structure test.Container [class] (Self : Type₁) («<Self as Container>.E» : Type₁) :=
(empty : sem (Self))
(insert : Self → «<Self as Container>.E» → sem (unit × Self))

definition test.«collections.vec.Vec<T> as test.Container».empty {T : Type₁} : sem ((collections.vec.Vec T)) :=
dostep «$tmp» ← @collections.vec.«Vec<T>».new _;
let' ret ← «$tmp»;
return (ret)


definition test.«collections.vec.Vec<T> as test.Container».insert {T : Type₁} (selfₐ : (collections.vec.Vec T)) (xₐ : T) : sem (unit × (collections.vec.Vec T)) :=
let' self ← @lens.id (collections.vec.Vec T);
let' x ← xₐ;
let' t6 ← (self);
do «$tmp» ← lens.get t6 selfₐ;
let' t8 ← x;
do «$tmp0» ← lens.get t6 selfₐ;
dostep «$tmp» ← @collections.vec.«Vec<T>».push _ «$tmp0» t8;
match «$tmp» with (t5, «t6$») :=
do selfₐ ← lens.set t6 selfₐ «t6$»;
let' ret ← ⋆;
return (⋆, selfₐ)
end


definition test.«collections.vec.Vec<T> as test.Container» [instance] {T : Type₁} := ⦃
  test.Container (collections.vec.Vec T) T,
  empty := @test.«collections.vec.Vec<T> as test.Container».empty T,
  insert := @test.«collections.vec.Vec<T> as test.Container».insert T
⦄

