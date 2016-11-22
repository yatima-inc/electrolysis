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

definition test.apply {T : Type₁} {F : Type₁} [«core.ops.FnMut F (T)» : core.ops.FnMut F (T) T] (fₐ : F) (xₐ : T) : sem (T) :=
let' f ← fₐ;
let' x ← xₐ;
let' t6 ← @lens.id F;
do «$tmp» ← lens.get t6 f;
let' t9 ← x;
let' t8 ← (t9);
do «$tmp0» ← lens.get t6 f;
dostep «$tmp» ← @core.ops.FnMut.call_mut _ _ _ «core.ops.FnMut F (T)» «$tmp0» t8;
match «$tmp» with (y, «t6$») :=
do f ← lens.set t6 f «t6$»;
let' t10 ← @lens.id F;
do «$tmp» ← lens.get t10 f;
let' t12 ← y;
let' t11 ← (t12);
do «$tmp0» ← lens.get t10 f;
dostep «$tmp» ← @core.ops.FnMut.call_mut _ _ _ «core.ops.FnMut F (T)» «$tmp0» t11;
match «$tmp» with (ret, «t10$») :=
do f ← lens.set t10 f «t10$»;
return (ret)
end
end


section
parameters 
parameters 

structure test.foo.closure_13 (U0 : Type₁) := (val : U0)

section
parameters (a1 : (test.foo.closure_13 i32)) (xₐ : i32)



definition test.foo.closure_13.fn : sem (i32 × (test.foo.closure_13 i32)) :=
let' x ← xₐ;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits (test.foo.closure_13.val a1) (1 : int));
let' t4 ← «$tmp0»;
let' a1 ← test.foo.closure_13.mk (t4.1);
let' t5 ← x;
let' t6 ← (test.foo.closure_13.val a1);
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits t5 t6);
let' t7 ← «$tmp0»;
let' ret ← t7.1;
return (ret, a1)

end

definition test.foo.closure_13.inst [instance] : core.ops.FnMut (test.foo.closure_13 i32) i32 i32 :=
core.ops.FnMut.mk test.foo.closure_13.fn

end

definition test.foo (xₐ : i32) (yₐ : i32) : sem (i32) :=
let' x ← xₐ;
let' y ← yₐ;
let' t6 ← y;
let' t5 ← test.foo.closure_13.mk t6;
let' t7 ← x;
dostep «$tmp» ← @test.apply _ _ _ t5 t7;
let' ret ← «$tmp»;
return (ret)


