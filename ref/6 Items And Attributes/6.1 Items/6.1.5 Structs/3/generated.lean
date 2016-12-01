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

structure test.Cookie := mk {} ::

definition test.main : sem (unit) :=
let' t2 ← test.Cookie.mk;
let' t3 ← test.Cookie.mk;
let' t4 ← test.Cookie.mk;
let' t5 ← test.Cookie.mk;
let' «c$1» ← [t2, t3, t4, t5];
let' ret ← ⋆;
return (⋆)


