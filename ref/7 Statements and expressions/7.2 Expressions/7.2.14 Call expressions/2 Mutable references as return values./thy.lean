import .generated

open int
open list
open prod.ops

example (x y : i32) : sem.terminates_with (λ r, r.2 = [2, y]) (test.bar [x, y]) := rfl
