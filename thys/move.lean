/- things that may or may not belong in the stdlib -/
import data.list
import data.list.sorted

open eq.ops
open list
open nat
open option

lemma generalize_with_eq {A : Type} {P : A → Prop} (x : A) (H : ∀y, x = y → P y) : P x := H x rfl

namespace nat
  open int

  definition of_int : ℤ → ℕ
  | (int.of_nat n) := n
  | _              := 0

  lemma of_int_one : of_int 1 = 1 := rfl
end nat

namespace option
  variables {A B : Type}

  protected definition any [unfold 3] (P : A → Prop) : option A → Prop
  | (some x) := P x
  | none     := false

  protected theorem any.elim {x : option A} {P : A → Prop} (H : option.any P x) : ∃y, x = some y ∧ P y :=
  begin
    cases x with y,
    { contradiction },
    { apply exists.intro y (and.intro rfl H) }
  end

  theorem ex_some_of_neq_none {x : option A} (H : x ≠ none) : ∃y, x = some y :=
  begin
    cases x with y,
    { exfalso, apply H rfl },
    { existsi y, apply rfl }
  end

  protected definition bind [unfold 3] {A B : Type} : option A → (A → option B) → option B
  | (some x) f := f x
  | none     _ := none

  theorem bind_some_eq_id {x : option A} : option.bind x some = x :=
  by cases x; esimp; esimp

  theorem bind_neq_none {f : A → option B} {x} (Hx : x ≠ none) (Hf : ∀x', f x' ≠ none) : option.bind x f ≠ none :=
  obtain x' H₁, from ex_some_of_neq_none Hx,
  obtain x'' H₂, from ex_some_of_neq_none (Hf x'),
  by rewrite [H₁, ▸*, H₂]; contradiction
end option

export [unfold] option

namespace list
section
  parameter {A : Type}
  variable xs : list A

  -- first without [inhabited], last without predicate
  definition first' [unfold 2] : option A := nth xs 0
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

  theorem dropn_dropn (n : ℕ) : Π (m : ℕ) (xs : list A), dropn n (dropn m xs) = dropn (n+m) xs
  | 0 xs             := by esimp
  | (succ m) []      := by rewrite +dropn_nil
  | (succ m) (x::xs) := by rewrite [nat.add_succ, ↑dropn at {1,3}]; apply dropn_dropn m xs

  theorem last'_dropn_of_last' : Π(n : ℕ) (xs : list A) (H : n < length xs), last' (dropn n xs) = last' xs
  | 0 xs             H := rfl
  | (succ n) []      H := by rewrite length_nil at H
  | (succ n) (x::xs) H := begin
    have H' : n < length xs, from lt_of_succ_lt_succ (!length_cons ▸ H),
    have xs ≠ nil, begin
      intro Hcontr,
      rewrite [Hcontr at H', length_nil at H'],
      apply not_succ_le_zero n H',
    end,
    rewrite [↑dropn, last'_cons_eq_last' this],
    apply last'_dropn_of_last' n xs H'
  end

  theorem nth_eq_first'_dropn : Π(n : ℕ) (xs : list A), nth xs n = first' (dropn n xs)
  | 0 xs             := rfl
  | (succ n) []      := by esimp
  | (succ n) (x::xs) := by rewrite [↑dropn, ↑nth]; apply nth_eq_first'_dropn n xs

  theorem firstn_app_dropn_eq_self : Π(n : ℕ) (xs : list A), firstn n xs ++ dropn n xs = xs
  | 0        xs      := rfl
  | (succ n) []      := rfl
  | (succ n) (x::xs) := by rewrite [↑firstn, ↑dropn, ▸*, append_cons, firstn_app_dropn_eq_self]

  theorem mem_of_nth : Π{i : ℕ} {xs : list A} {y : A}, nth xs i = some y → y ∈ xs
  | _        []      _ H := by contradiction
  | 0        (x::xs) y H := by injection H with Hxy; apply Hxy ▸ !mem_cons
  | (succ i) (x::xs) y H := by rewrite [↑nth at H]; apply mem_cons_of_mem x (mem_of_nth H)

  theorem nth_of_mem : Π{xs : list A} {y : A}, y ∈ xs → ∃i, nth xs i = some y
  | []      y H := by contradiction
  | (x::xs) y H := or.rec_on (eq_or_mem_of_mem_cons H)
    (suppose y = x, exists.intro 0 (this ▸ rfl))
    (suppose y ∈ xs,
      obtain i Hnth, from nth_of_mem this,
      exists.intro (i+1) (!nth_succ ⬝ Hnth))

  theorem lt_length_of_mem : Π{xs : list A} {i : ℕ} {y : A}, nth xs i = some y → i < length xs
  | []      i        y H := by contradiction
  | (x::xs) 0        y H := !zero_lt_succ
  | (x::xs) (succ i) y H := by unfold nth at H; apply succ_lt_succ (lt_length_of_mem H)

  definition insert_at : list A → ℕ → A → list A
  | [] n y := [y]
  | xs 0 y := y::xs
  | (x::xs) (succ n) y := x::insert_at xs n y
end

inductive prefixeq {A : Type} : list A → list A → Prop :=
  infix ` ⊑ₚ `:50 := prefixeq
| prefixeq_nil : Πys, [] ⊑ₚ ys
| prefixeq_of_cons_prefixeq : Πx {xs ys}, xs ⊑ₚ ys → x::xs ⊑ₚ x::ys

namespace prefixeq
section
  parameter {A : Type}

  infix ` ⊑ₚ `:50 := prefixeq

  protected theorem refl [refl] : Π(xs : list A), xs ⊑ₚ xs
  | []      := !prefixeq_nil
  | (x::xs) := prefixeq_of_cons_prefixeq x (refl xs)

  protected theorem trans [trans] : Π{xs ys zs : list A}, xs ⊑ₚ ys → ys ⊑ₚ zs → xs ⊑ₚ zs
  | [] ys zs _ _ := !prefixeq_nil
  | (x::xs) (x::ys) (x::zs) (prefixeq_of_cons_prefixeq x H₁) (prefixeq_of_cons_prefixeq x H₂) :=
    prefixeq_of_cons_prefixeq x (trans H₁ H₂)

  protected theorem antisymm : Π{xs ys : list A}, xs ⊑ₚ ys → ys ⊑ₚ xs → xs = ys
  | [] [] _ _ := rfl
  | (x::xs) (x::ys) (prefixeq_of_cons_prefixeq x H₁) (prefixeq_of_cons_prefixeq x H₂) :=
    antisymm H₁ H₂ ▸ rfl

  definition weak_order [instance] : weak_order (list A) := ⦃weak_order,
    le := prefixeq, le_refl := refl, le_trans := @trans, le_antisymm := @antisymm
  ⦄

  theorem nth_of_nth_prefixeq {i : ℕ} {xs ys : list A} {z : A} (Hxs : nth xs i = some z) (Hprefix : xs ⊑ₚ ys) : nth ys i = some z :=
  begin
    revert i Hxs,
    induction Hprefix with x z' xs ys Hprefix ih,
    all_goals intro i Hxs,
    { contradiction },
    { cases i with i,
      { apply Hxs },
      { apply ih i Hxs }
    }
  end

  theorem firstn_prefixeq : Π(n : ℕ) (xs : list A), firstn n xs ⊑ₚ xs
  | 0 xs             := !prefixeq_nil
  | (succ n) []      := !prefixeq_nil
  | (succ n) (x::xs) := prefixeq_of_cons_prefixeq x (firstn_prefixeq n xs)

  theorem dropn_prefixeq_dropn_of_prefixeq : Π(n : ℕ) {xs ys : list A} (H : xs ⊑ₚ ys),
    dropn n xs ⊑ₚ dropn n ys
  | 0 xs ys H := H
  | n [] ys H := by rewrite dropn_nil; apply !prefixeq_nil
  | (succ n) (x::xs) (x::ys) (prefixeq_of_cons_prefixeq x H) := by unfold dropn; apply dropn_prefixeq_dropn_of_prefixeq n H
end
end prefixeq

namespace sorted
section
  parameter {A : Type}
  parameter [decidable_linear_order A]

  definition insert_pos : list A → A → ℕ
  | [] y      := 0
  | (x::xs) y := if y ≤ x
    then 0
    else succ (insert_pos xs y)

  theorem insert_pos_le_length : Π(xs : list A) (y : A), insert_pos xs y ≤ length xs
  | [] y      := zero_le _
  | (x::xs) y := begin
    unfold insert_pos, cases (_ : decidable (y ≤ x)),
    { apply zero_le },
    { apply succ_le_succ (insert_pos_le_length xs y) }
  end

  section
    variable {xs : list A}
    variable (Hsorted : sorted le xs)

    theorem first_le {x x' : A} (Hsorted : sorted le (x::xs)) (Hx'_mem : x' ∈ x::xs) : x ≤ x' :=
    or.rec_on (eq_or_mem_of_mem_cons Hx'_mem)
      (assume H : x' = x, H ▸ le.refl x')
      (assume H : x' ∈ xs, of_mem_of_all H (sorted_extends (@le.trans _ _) Hsorted))

    include Hsorted
    theorem le_of_nth_le_nth {x₁ x₂ : A} : Π{i j : ℕ}, nth xs i = some x₁ → nth xs j = some x₂ → i ≤ j → x₁ ≤ x₂ :=
    begin
      induction Hsorted using sorted.rec with y ys Hhd_rel Hsorted ih,
      { contradiction },
      { intro i j Hi Hj Hle,
        cases i with i',
        { injection Hi with H, subst H,
          apply first_le (sorted.step Hhd_rel Hsorted) (mem_of_nth Hj) },
        { cases j with j',
          { exfalso, apply !not_succ_le_zero Hle },
          { unfold nth at Hi, unfold nth at Hj, apply ih Hi Hj (le_of_succ_le_succ Hle) }
        }
      }
    end

    theorem insert_pos_gt {y xi : A} {i : ℕ} (Hyxi : y > xi) (Hnth : nth xs i = some xi) :
      insert_pos xs y > i :=
    begin
      revert i Hnth,
      induction Hsorted using sorted.rec with x xs Hhd_rel Hsorted ih,
      { contradiction },
      { unfold insert_pos, cases (_ : decidable (y ≤ x)) with Hyx Hyx,
        { intro i Hnth, exfalso,
          exact lt.irrefl _ (
            calc x ≤ xi : first_le (sorted.step Hhd_rel Hsorted) (mem_of_nth Hnth)
               ... < y  : Hyxi
               ... ≤ x  : Hyx)
        },
        { intro i Hnth, cases i with i,
          { apply zero_lt_succ },
          { apply succ_lt_succ (ih i Hnth) }
        }
      }
    end

    theorem insert_pos_le {y xi : A} {i : ℕ} (Hyxi : y < xi) (Hnth : nth xs i = some xi) :
      insert_pos xs y ≤ i :=
    begin
      revert i Hnth,
      induction Hsorted using sorted.rec with x xs Hhd_rel Hsorted ih,
      { contradiction },
      { unfold insert_pos, cases (_ : decidable (y ≤ x)) with Hyx Hyx,
        { intros, apply zero_le },
        { intro i Hnth, cases i with i,
          { injection Hnth with Hx_eq_xi,
            exfalso, apply Hyx (le_of_lt (Hx_eq_xi⁻¹ ▸ Hyxi)) },
          { apply succ_le_succ (ih i Hnth) }
        }
      }
    end

    theorem sorted_insert_at_insert_pos (y : A) :
      sorted le (insert_at xs (insert_pos xs y) y) :=
    begin
      note Hlsorted := locally_sorted_of_sorted Hsorted,
      clear Hsorted,
      apply sorted_of_locally_sorted,
      induction xs with x xs ih,
      { apply locally_sorted.base },
      { unfold insert_pos,
        exact decidable.rec_on _
          (suppose y ≤ x, locally_sorted.step this Hlsorted)
          (suppose Hyx : ¬y ≤ x, begin
            cases xs with x' xs,
            { exact locally_sorted.step (le_of_not_ge Hyx) !locally_sorted.base },
            { cases Hlsorted with _ _ _ _ Hxx' Hlsorted',
              rewrite [↑ite, ↑insert_at],
              revert ih, rewrite [↑insert_pos],
              exact decidable.rec_on _
                (suppose y ≤ x', assume ih, locally_sorted.step (le_of_not_ge Hyx) (locally_sorted.step this Hlsorted'))
                (suppose ¬y ≤ x', assume ih, locally_sorted.step Hxx' (ih Hlsorted'))
            }
          end)
      }
    end

    theorem sorted_dropn_of_sorted : Π(n : ℕ), sorted le (dropn n xs) :=
    begin
      induction Hsorted using sorted.rec with x xs Hhd_rel Hsorted ih,
      { intro n, rewrite dropn_nil, apply sorted.base },
      { intro n, cases n,
        { apply sorted.step Hhd_rel Hsorted },
        { unfold dropn, apply ih }
      }
    end

    omit Hsorted
    theorem hd_rel_of_prefix_of_hd_rel {x : A} {ys : list A} (Hprefix : prefixeq xs ys) (Hhd_rel : hd_rel le x ys) :
      hd_rel le x xs :=
    begin
      cases Hhd_rel with y ys' Hxy,
      { cases Hprefix, apply hd_rel.base },
      { cases Hprefix,
        { apply hd_rel.base },
        { exact hd_rel.step _ Hxy }
      }
    end

    theorem sorted_of_prefix_of_sorted {ys : list A} (Hprefix : prefixeq xs ys) (Hsorted : sorted le ys) :
      sorted le xs :=
    begin
      revert xs Hprefix,
      induction Hsorted using sorted.rec with y ys Hhd_rel Hsorted ih,
      all_goals intro xs Hprefix,
      { cases Hprefix, apply sorted.base },
      { cases Hprefix with _ _ xs' _ Hprefix',
        { apply sorted.base },
        { apply sorted.step (!hd_rel_of_prefix_of_hd_rel Hprefix' Hhd_rel) (ih xs' Hprefix') }
      }
    end
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

-- H as implicit instead of instance implicit for rewriting
theorem if_pos' {c : Prop} {H : decidable c} (Hc : c) {A : Type} {t e : A} : (ite c t e) = t :=
decidable.rec
  (λ Hc : c,    eq.refl (@ite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

theorem if_neg' {c : Prop} {H : decidable c} (Hnc : ¬c) {A : Type} {t e : A} : (ite c t e) = e :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@ite c (decidable.inr Hnc) A t e))
  H
