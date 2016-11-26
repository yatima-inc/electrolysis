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

structure test.Foo [class] (Self : Type₁)  :=
(bar : Self → sem (unit))

definition test.Foo.baz {Self : Type₁} [«test.Foo Self» : test.Foo Self] (selfₐ : Self) : sem (unit) :=
let' self ← selfₐ;
let' t3 ← self;
dostep «$tmp» ← @test.Foo.bar _ (_ : test.Foo Self) t3;
let' ret ← «$tmp»;
return (⋆)


structure test.Bar := mk {} ::

definition test.«test.Bar as test.Foo».bar (selfₐ : (test.Bar)) : sem (unit) :=
let' self ← selfₐ;
let' ret ← ⋆;
return (⋆)


definition test.«test.Bar as test.Foo».baz (selfₐ : (test.Bar)) : sem (unit) :=
let' self ← selfₐ;
let' ret ← ⋆;
return (⋆)


/- test.«test.Bar as test.Foo»: unimplemented: overriding default method "test.«test.Bar as test.Foo».baz" -/

