import .generated

open int

example : sem.terminates_with (λ r, r = 1) test.foo := rfl
example : ¬sem.terminates test.bar := id
