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


/- test.foo: unimplemented: mutable capturing closure -/

