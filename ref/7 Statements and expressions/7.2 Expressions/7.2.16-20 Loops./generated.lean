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

section
parameters 
parameters 
section
parameters (xₐ : i32)

definition test.foo.loop_1 (state__ : i32) : sem (sum (i32) (unit)) :=
let' x ← state__;
let' t4 ← x;
let' t3 ← t4 ≠ᵇ (0 : int);
if t3 = bool.tt then
let' t8 ← x;
let' t7 ← t8 =ᵇ (1 : int);
if t7 = bool.tt then
return (sum.inl (x))
else
let' t6 ← ⋆;
let' t12 ← x;
let' t11 ← t12 =ᵇ (2 : int);
if t11 = bool.tt then
do tmp__ ← let' ret ← ⋆;
return (ret)
;
return (sum.inr tmp__)else
let' t10 ← ⋆;
let' t17 ← x;
let' t16 ← t17 =ᵇ (3 : int);
if t16 = bool.tt then
do tmp__ ← let' ret ← ⋆;
return (ret)
;
return (sum.inr tmp__)else
let' t15 ← ⋆;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.ssub i32.bits x (1 : int));
let' t20 ← «$tmp0»;
let' x ← t20.1;
let' t5 ← ⋆;
return (sum.inl (x))
else
do tmp__ ← let' ret ← ⋆;
return (ret)
;
return (sum.inr tmp__)

definition test.foo : sem (unit) :=
let' x ← xₐ;
loop (test.foo.loop_1) (x)
end
end

