import fixedbitset.generated

open [class] nat
open prod.ops

open fixedbitset

namespace fixedbitset.FixedBitSet

eval
  do s ← with_capacity 10;
  do r ← insert s 2;
  contains r.2 2

attribute sem.bind [irreducible]

attribute bool.of_decidable [unfold 2]
attribute bool.bnot [unfold 1]

lemma decidable_eq_inl {P : Prop} (H : P) : Π(d : decidable P), d = decidable.inl H
| (decidable.inl H') := rfl
| (decidable.inr NH) := false.elim (NH H)

lemma contains_insert (s : FixedBitSet) (bit : usize) : bit < length s →
  sem.terminates_with (λ b, b = bool.tt) (do r ← insert s bit; contains r.2 bit) :=
begin
  intros,
  rewrite [↑insert, decidable_eq_inl `bit < length s` (decidable_lt bit (length s)), ▸*],
  apply sorry
end

end fixedbitset.FixedBitSet

