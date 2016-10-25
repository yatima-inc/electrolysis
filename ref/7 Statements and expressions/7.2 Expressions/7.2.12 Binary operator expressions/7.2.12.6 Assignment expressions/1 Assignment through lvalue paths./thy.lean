import .generated

open int
open list

example : sem.terminates_with (λ s', s' = ⦃test.S, x := [2, 42]⦄) (test.foo ⦃test.S, x := [41, 42]⦄ 0) := rfl

example : ¬sem.terminates (test.foo ⦃test.S, x := [41, 42]⦄ 2) := id
