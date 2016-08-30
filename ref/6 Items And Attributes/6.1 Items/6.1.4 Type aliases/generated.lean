import core.generated

noncomputable theory

open [class] classical
open [class] int
open [notation] list
open [class] nat
open [notation] prod.ops
open [notation] unit

namespace test

definition Point := (u8 × u8)

definition p : (u8 × u8) :=
let' ret ← ((41 : nat), (68 : nat));
ret

end test