import .generated

open core
open option

theorem fac_correct (n : ℕ) : examples.fac n = some (nat.fact n) :=
begin
  rewrite [↑examples.fac],
  apply bind_eq_some,
  { rewrite [↑iter.I.IntoIterator.into_iter], exact rfl },
  apply bind_eq_some,
  rewrite [↑examples.fac.loop_4]
end
