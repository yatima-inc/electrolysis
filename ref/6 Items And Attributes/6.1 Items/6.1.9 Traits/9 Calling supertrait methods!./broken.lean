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

structure test.Shape [class] (Self : Type₁)  :=
(area : Self → sem (i64))

structure test.Circle [class] (Self : Type₁) («<Self as Circle>.Foo» : Type₁) extends test.Shape Self :=
(radius : Self → sem (i64))

definition test.radius_times_area {T : Type₁} («<T as Circle>.Foo» : Type₁) [«test.Circle T» : test.Circle T «<T as Circle>.Foo»] (cₐ : T) : sem (i64) :=
let' c ← cₐ;
let' t4 ← c;
dostep «$tmp» ← @test.Circle.radius _ _ «test.Circle T» t4;
let' t3 ← «$tmp»;
let' t7 ← c;
dostep «$tmp» ← @test.Shape.area _ (_ : test.Shape T) t7;
let' t6 ← «$tmp»;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.smul i64.bits t3 t6);
let' t8 ← «$tmp0»;
let' ret ← t8.1;
return (ret)


