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

structure test.Foo := mk {} ::

definition test.«test.Foo as test.Shape».area (selfₐ : (test.Foo)) : sem (i64) :=
let' self ← selfₐ;
let' ret ← (1 : int);
return (ret)


definition test.«test.Foo as test.Circle».radius (selfₐ : (test.Foo)) : sem (i64) :=
let' self ← selfₐ;
let' ret ← (-1 : int);
return (ret)


structure test.Shape [class] (Self : Type₁)  :=
(area : Self → sem (i64))

structure test.Circle [class] (Self : Type₁)  extends test.Shape Self :=
(radius : Self → sem (i64))

definition test.«test.Foo as test.Shape» [instance] := ⦃
  test.Shape (test.Foo),
  area := test.«test.Foo as test.Shape».area
⦄

definition test.«test.Foo as test.Circle» [instance] := ⦃
  test.Circle (test.Foo),
  (test.«test.Foo as test.Shape» ),
  radius := test.«test.Foo as test.Circle».radius
⦄

definition test.main : sem (unit) :=
let' c ← test.Foo.mk;
let' t3 ← c;
dostep «$tmp» ← @test.«test.Foo as test.Circle».radius t3;
let' t2 ← «$tmp»;
let' ret ← ⋆;
return (ret)


