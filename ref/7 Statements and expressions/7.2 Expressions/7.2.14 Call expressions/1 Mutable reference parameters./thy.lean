import .generated

open int

example : sem.terminates_with (λ r, r = 2) test.foo := rfl
