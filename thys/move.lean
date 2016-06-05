/- things that may or may not belong in the stdlib -/
import data.list
import data.list.sorted

open eq.ops
open list
open nat
open option

namespace nat
  open int

  definition of_int : ℤ → ℕ
  | (int.of_nat n) := n
  | _              := 0

  lemma of_int_one : of_int 1 = 1 := rfl
end nat

namespace option
  variables {A B : Type}

  protected definition all [unfold 3] {A : Type} (P : A → Prop) : option A → Prop
  | (some x) := P x
  | none     := false

  theorem ex_some_of_neq_none {x : option A} (H : x ≠ none) : ∃y, x = some y :=
  begin
    cases x with y,
    { exfalso, apply H rfl },
    { existsi y, apply rfl }
  end

  protected definition bind [unfold 4] {A B : Type} (f : A → option B) : option A → option B
  | (some x) := f x
  | none     := none

  theorem bind_some_eq_id {x : option A} : option.bind some x = x :=
  by cases x; esimp; esimp

  theorem bind_neq_none {f : A → option B} {x} (Hx : x ≠ none) (Hf : ∀x', f x' ≠ none) : option.bind f x ≠ none :=
  obtain x' H₁, from ex_some_of_neq_none Hx,
  obtain x'' H₂, from ex_some_of_neq_none (Hf x'),
  by rewrite [H₁, ▸*, H₂]; contradiction
end option

namespace list
section
  parameter {A : Type}
  variable xs : list A

  -- first without [inhabited], last without predicate
  definition first' : option A := nth xs 0
  definition last' : list A → option A
  | []      := none
  | [x]     := some x
  | (x::xs) := last' xs

  theorem last'_cons_eq_last' : Π{x : A} {xs : list A}, xs ≠ nil → last' (x::xs) = last' xs
  | x [] H       := false.elim (H rfl)
  | x (x'::xs) H := by esimp

  theorem firstn_sub : Π(n : ℕ) (xs : list A), firstn n xs ⊆ xs
  | 0 xs             := nil_sub _
  | (succ n) []      := sub.refl _
  | (succ n) (x::xs) := cons_sub_cons x (firstn_sub n xs)

  theorem dropn_nil (n : ℕ) : dropn n (nil : list A) = nil :=
  nat.cases_on n rfl (λn, rfl)

  theorem mem_of_mem_dropn (x : A) : Π(n : ℕ) (xs : list A), x ∈ dropn n xs → x ∈ xs
  | 0 xs H             := H
  | (n+1) [] H         := by contradiction
  | (succ n) (y::xs) H := by esimp at H; apply mem_cons_of_mem y (mem_of_mem_dropn n xs H)

  theorem dropn_sub_dropn_cons : Π(n : ℕ) (x : A) (xs : list A), dropn n xs ⊆ dropn n (x::xs)
  | 0 x xs              := sub_cons x xs
  | (succ n) x []       := nil_sub _
  | (succ n) x (x'::xs) := by esimp; apply dropn_sub_dropn_cons n x' xs

  theorem dropn_sub : Π(n : ℕ) (xs : list A), dropn n xs ⊆ xs
  | 0 xs             := sub.refl _
  | (succ n) []      := sub.refl _
  | (succ n) (x::xs) := by esimp; apply sub.trans (dropn_sub_dropn_cons n x xs) (dropn_sub n (x::xs))

  theorem dropn_dropn (n : ℕ) : Π (m : ℕ) (xs : list A), dropn n (dropn m xs) = dropn (#nat (n+m)) xs
  | 0 xs             := by esimp
  | (succ m) []      := by rewrite +dropn_nil
  | (succ m) (x::xs) := by rewrite [nat.add_succ, ↑dropn at {1,3}]; apply dropn_dropn m xs

  theorem last'_dropn_of_last' : Π(n : ℕ) (xs : list A) (H : n < length xs), last' (dropn n xs) = last' xs
  | 0 xs             H := rfl
  | (succ n) []      H := by rewrite length_nil at H
  | (succ n) (x::xs) H := begin
    have H' : n < length xs, from lt_of_succ_lt_succ (!length_cons ▸ H),
    have xs ≠ nil, from take Hcontr,
      by rewrite [Hcontr at H', length_nil at H']; apply not_succ_le_zero n H',
    rewrite [↑dropn, last'_cons_eq_last' this],
    apply last'_dropn_of_last' n xs H'
  end

  definition insert_at : list A → ℕ → A → list A
  | [] n y := [y]
  | xs 0 y := y::xs
  | (x::xs) (succ n) y := x::insert_at xs n y
end

namespace sorted
section
  parameter {A : Type}
  parameter [decidable_linear_order A]

  definition insert_pos : list A → A → ℕ
  | [] y      := 0
  | (x::xs) y := if y ≤ x
    then 0
    else succ (insert_pos xs y)

  theorem sorted_insert_at_insert_pos (xs : list A) (y : A) (H : sorted le xs) :
    sorted le (insert_at xs (insert_pos xs y) y) :=
  begin
    note Hsorted := locally_sorted_of_sorted H,
    clear H,
    apply sorted_of_locally_sorted,
    induction xs with x xs ih,
    { apply locally_sorted.base },
    { unfold insert_pos,
      exact decidable.rec_on _
        (suppose y ≤ x, locally_sorted.step this Hsorted)
        (suppose Hyx : ¬y ≤ x, begin
          cases xs with x' xs,
          { exact locally_sorted.step (le_of_not_ge Hyx) !locally_sorted.base },
          { cases Hsorted with _ _ _ _ Hxx' Hsorted',
            rewrite [↑ite, ↑insert_at],
            revert ih, rewrite [↑insert_pos],
            exact decidable.rec_on _
              (suppose y ≤ x', assume ih, locally_sorted.step (le_of_not_ge Hyx) (locally_sorted.step this Hsorted'))
              (suppose ¬y ≤ x', assume ih, locally_sorted.step Hxx' (ih Hsorted'))
          }
        end)
    }
  end
end
end sorted

end list

namespace partial
infixr ` ⇀ `:25 := λA B, A → option B

section
  parameters {A B : Type} {R : B → B → Prop}
  parameters (f : A ⇀ B)

  definition R' [unfold 3] : option B → option B → Prop
  | (some y) (some x) := R y x
  | _        _        := false

  private definition R'.wf (H : well_founded R) : well_founded R' :=
  begin
    apply well_founded.intro,
    intro x, cases x with x',
    { apply acc.intro,
      intro y,
      cases y; repeat contradiction },
    { induction (well_founded.apply H x') with x' _ ih,
      apply acc.intro,
      intro y HR', cases y with y',
      { contradiction },
      { apply ih _ HR' }
    }
  end

  parameter (R)
  definition inv_image (f : A ⇀ B) : A → A → Prop := inv_image R' f

  parameter {R}
  lemma inv_image.wf (H : well_founded R) : well_founded (inv_image f) :=
  inv_image.wf f (R'.wf H)
end
end partial

namespace sum
  definition inl_opt [unfold 3] {A B : Type} : A + B → option A
  | (inl a) := some a
  | (inr _) := none

  definition inr_opt [unfold 3] {A B : Type} : A + B → option B
  | (inl _) := none
  | (inr b) := some b
end sum

-- generalized nat.le_lt_antisymm
theorem le_lt_antisymm {T : Type} [order_pair T] {n m : T} (H1 : n ≤ m) (H2 : m < n) : false :=
!lt.irrefl (lt_of_le_of_lt H1 H2)

namespace classical
  theorem dite_else_false {c : Prop} {t : c → Prop} (Hdite : if H : c then t H else false) : c :=
  if H : c then H
  else false.elim (dif_neg H ▸ Hdite)
end classical

attribute dite [unfold 2]
attribute ite [unfold 2]
