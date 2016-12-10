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

structure test.Seq [class] (Self : Type₁) (T : Type₁) :=
(len : (Self → sem (u32)))
(elt_at : (Self → u32 → sem (T)))
(iter : Π {F : Type₁} [«core.ops.Fn F T» : core.ops.Fn F T unit], (Self → F → sem (unit)))

