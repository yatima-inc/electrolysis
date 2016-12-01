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

structure test.main.Point := mk {} ::
(x : i64)
(y : i64)

structure test.main.NothingInMe := mk {} ::


inductive test.main.TuplePoint :=
mk {} : i64 → i64 → test.main.TuplePoint

structure test.main.game.User := mk {} ::
(name : string)
(age : u32)
(score : usize)

structure test.main.Cookie := mk {} ::

definition test.main.some_fn {T : Type₁} (tₐ : T) : sem (unit) :=
let' «t$2» ← tₐ;
let' ret ← ⋆;
return (⋆)


definition test.main : sem (unit) :=
let' t1 ← test.main.Point.mk (10 : int) (20 : int);
let' t2 ← test.main.NothingInMe.mk;
let' t3 ← test.main.TuplePoint.mk (10 : int) (20 : int);
let' t6 ← "Joe";
let' t5 ← t6;
let' «u$4» ← test.main.game.User.mk t5 (35 : nat) (100000 : nat);
let' t8 ← test.main.Cookie.mk;
dostep «$tmp» ← @test.main.some_fn (test.main.Cookie) t8;
let' t7 ← «$tmp»;
let' ret ← ⋆;
return (⋆)


