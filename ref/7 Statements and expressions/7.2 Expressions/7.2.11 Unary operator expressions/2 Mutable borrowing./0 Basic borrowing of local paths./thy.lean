import .generated

open int
open list

example : sem.terminates_with (λ i, i = 41) (test.foo ⦃test.S, x := [41, 42]⦄) := rfl
