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

namespace test

definition Point := (u8 × u8)

definition p : sem (u8 × u8) :=
let' ret ← ((((41 : nat)), ((68 : nat))));
return (ret)


end test