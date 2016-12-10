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

structure test.Num [class] (Self : Type₁) :=
(from_i32 : (i32 → sem (Self)))

definition test.«i64 as test.Num».from_i32 (nₐ : i32) : sem (i64) :=
let' «n$2» ← nₐ;
let' t3 ← «n$2»;
do «$tmp0» ← (signed_to_signed i64.bits t3);
let' ret ← «$tmp0»;
return (ret)


definition test.«i64 as test.Num» [instance] := ⦃
  test.Num i64,
  from_i32 := @test.«i64 as test.Num».from_i32
⦄

definition test.main : sem (unit) :=
dostep «$tmp» ← @test.«i64 as test.Num».from_i32 (42 : int);
let' «x$1» ← «$tmp»;
let' ret ← ⋆;
return (⋆)


