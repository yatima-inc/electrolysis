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

definition test.apply {T : Type₁} {F : Type₁} [«core.ops.FnMut F T» : core.ops.FnMut F T T] (fₐ : F) (xₐ : T) : sem (T) :=
let' «f$3» ← fₐ;
let' «x$4» ← xₐ;
let' t6 ← @lens.id F;
do «$tmp» ← lens.get t6 «f$3»;
let' t9 ← «x$4»;
let' t8 ← t9;
do «$tmp0» ← lens.get t6 «f$3»;
dostep «$tmp» ← @core.ops.FnMut.call_mut F T T «core.ops.FnMut F T» «$tmp0» t8;
match «$tmp» with («y$5», «t6$») :=
do «f$3» ← lens.set t6 «f$3» «t6$»;
let' t10 ← @lens.id F;
do «$tmp» ← lens.get t10 «f$3»;
let' t12 ← «y$5»;
let' t11 ← t12;
do «$tmp0» ← lens.get t10 «f$3»;
dostep «$tmp» ← @core.ops.FnMut.call_mut F T T «core.ops.FnMut F T» «$tmp0» t11;
match «$tmp» with (ret, «t10$») :=
do «f$3» ← lens.set t10 «f$3» «t10$»;
return (ret)
end
end


section

structure test.foo.closure_13 (U0 : Type₁) := (val : U0)



definition test.foo.closure_13.fn («$a1» : (test.foo.closure_13 i32)) (xₐ : i32) : sem (i32 × (test.foo.closure_13 i32)) :=
let' «x$3» ← xₐ;
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits (test.foo.closure_13.val «$a1») (1 : int));
let' t4 ← «$tmp0»;
let' «$a1» ← test.foo.closure_13.mk t4.1;
let' t5 ← «x$3»;
let' t6 ← (test.foo.closure_13.val «$a1»);
do «$tmp0» ← sem.map (λx, (x, tt)) (checked.sadd i32.bits t5 t6);
let' t7 ← «$tmp0»;
let' ret ← t7.1;
return (ret, «$a1»)



definition test.foo.closure_13.inst [instance] : core.ops.FnMut (test.foo.closure_13 i32) i32 i32 :=
core.ops.FnMut.mk (λ self args, let' xₐ ← args;
  test.foo.closure_13.fn self xₐ
)

end

definition test.foo (xₐ : i32) (yₐ : i32) : sem (i32) :=
let' «x$3» ← xₐ;
let' «y$4» ← yₐ;
let' t6 ← «y$4»;
let' t5 ← test.foo.closure_13.mk t6;
let' t7 ← «x$3»;
dostep «$tmp» ← @test.apply i32 (test.foo.closure_13 i32) _ t5 t7;
let' ret ← «$tmp»;
return (ret)


