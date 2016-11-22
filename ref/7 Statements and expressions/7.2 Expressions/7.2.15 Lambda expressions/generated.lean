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

definition test.apply {T : Type₁} {R : Type₁} {F : Type₁} [«core.ops.FnOnce F (T)» : core.ops.FnOnce F (T) R] (fₐ : F) (xₐ : T) : sem (R) :=
let' f ← fₐ;
let' x ← xₐ;
let' t5 ← f;
let' t8 ← x;
let' t7 ← (t8);
dostep «$tmp» ← @core.ops.FnOnce.call_once _ _ _ «core.ops.FnOnce F (T)» t5 t7;
let' ret ← «$tmp»;
return (ret)


section
parameters 
parameters 

structure test.foo.closure_13 (U0 : Type₁) := (val : U0)

section
parameters (a1 : (test.foo.closure_13 i32)) (xₐ : i32)



definition test.foo.closure_13.fn : sem (i32) :=
let' x ← xₐ;
let' t4 ← x;
let' t5 ← (test.foo.closure_13.val a1);
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits t4 t5);
let' t6 ← «$tmp0»;
let' ret ← t6.1;
return (ret)

end

definition test.foo.closure_13.inst [instance] : core.ops.FnOnce (test.foo.closure_13 i32) i32 i32 :=
core.ops.FnOnce.mk test.foo.closure_13.fn

end

definition test.foo (xₐ : i32) (yₐ : i32) : sem (i32) :=
let' x ← xₐ;
let' y ← yₐ;
let' t6 ← y;
let' t5 ← test.foo.closure_13.mk t6;
let' t7 ← x;
dostep «$tmp» ← @test.apply _ _ _ _ t5 t7;
let' ret ← «$tmp»;
return (ret)


