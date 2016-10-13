/- things that may or may not belong in the stdlib -/
import algebra.interval
import algebra.order_bigops
import data.list
import data.list.sorted
import data.tuple

open eq.ops
open nat
open option

lemma generalize_with_eq {A : Type} {P : A → Prop} (x : A) (H : ∀y, x = y → P y) : P x := H x rfl

lemma not_exists_of_not {P : Prop} (Q : P → Prop) (np : ¬P) : ¬Exists Q :=
begin
  rewrite forall_iff_not_exists,
  intro p,
  exfalso, apply np p
end

namespace bool
  open decidable

  definition of_Prop [unfold 2] (P : Prop) : Π [decidable P], bool
  | (inl _) := tt
  | (inr _) := ff

  lemma of_Prop_eq_of_Prop_of_iff {P Q : Prop} (H : P ↔ Q) :
    Π[decidable P] [decidable Q], of_Prop P = of_Prop Q
  | (inl a) (inl b) := rfl
  | (inl a) (inr b) := false.elim (b (iff.mp H a))
  | (inr a) (inl b) := false.elim (a (iff.mpr H b))
  | (inr a) (inr b) := rfl

  lemma of_Prop_eq_tt_iff (P : Prop) : Π [dec : decidable P], of_Prop P = tt ↔ P
  | (inl p)  := iff.intro (take h, p) (take h, rfl)
  | (inr np) := iff.intro (by contradiction) (by contradiction)

  lemma bnot_of_Prop (P : Prop) {dec : decidable P} : bnot (of_Prop P) = of_Prop (¬ P) :=
  begin cases dec, esimp, esimp end

  lemma band_bor_distrib : Π(x y z : bool), (x || y) && z = x && z || y && z
  | x y tt := by rewrite [+band_tt]
  | x y ff := by rewrite [+band_ff]
end bool

namespace nat
  open int

  definition of_int [unfold 1] : ℤ → ℕ
  | (int.of_nat n) := n
  | _              := 0

  definition div_ceil (n m : ℕ) : ℕ := n / m + (if n % m > 0 then 1 else 0)

  lemma mul_ne_zero : Π{a b : ℕ}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
  | a 0 ha hb := false.elim (hb rfl)
  | a (succ b) ha hb := take contr,
    ha (eq_zero_of_add_eq_zero_left contr)

  lemma sub_eq_sub_min (a b : ℕ) : a - b = a - min a b :=
  if h : a ≥ b then by rewrite [min_eq_right h]
  else by rewrite [sub_eq_zero_of_le (le_of_not_ge h), min_eq_left (le_of_not_ge h), nat.sub_self]

  lemma sub_add_min_cancel (a b : ℕ) : a - b + min a b = a :=
  by rewrite [sub_eq_sub_min, nat.sub_add_cancel !min_le_left]
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

  definition unwrap [unfold 2] : Π{x : option A}, x ≠ none → A
  | (some x) H := x
  | none     H := false.rec A (H rfl)

  theorem ex_some_of_neq_none {x : option A} (H : x ≠ none) : ∃y, x = some y :=
  begin
    cases x with y,
    { exfalso, apply H rfl },
    { existsi y, apply rfl }
  end

  protected definition map [unfold 4] (f : A → B) : option A → option B
  | (some x) := some (f x)
  | none     := none

  protected definition bind [unfold 3] : option A → (A → option B) → option B
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
  variable {A : Type}
  variable xs : list A

  -- first without [inhabited], last without predicate
  definition first' [unfold 2] : option A := nth xs 0
  definition last' : list A → option A
  | []      := none
  | (x::xs) := some (last (x::xs) !cons_ne_nil)

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

  theorem lt_length_of_nth : Π{i : ℕ} {xs : list A} {y : A}, nth xs i = some y → i < length xs
  | _        []      _ H := by contradiction
  | 0        (x::xs) y H := !zero_lt_succ
  | (succ i) (x::xs) y H := succ_lt_succ (lt_length_of_nth (!nth_succ ▸ H))

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

  lemma ne_nil_of_mem {xs : list A} {x : A} (H : x ∈ xs) : xs ≠ nil :=
  suppose xs = nil, this ▸ H

  lemma ex_mem_of_ne_nil : Π{xs : list A}, xs ≠ nil → Σx : A, x ∈ xs
  | []      H := false.rec _ (H rfl)
  | (x::xs) _ := sigma.mk x (mem_cons x xs)

  lemma ne_nil_of_product_ne_nil_left {xs ys : list A} (H : product xs ys ≠ nil) : xs ≠ nil :=
  match ex_mem_of_ne_nil H with
  | sigma.mk (x, y) Hmem := ne_nil_of_mem (mem_of_mem_product_left Hmem)
  end

  lemma product_ne_nil_of_ne_nil {xs ys : list A} (Hxs : xs ≠ nil) (Hys : ys ≠ nil) :
    product xs ys ≠ nil :=
  obtain x Hx, from ex_mem_of_ne_nil Hxs,
  obtain y Hy, from ex_mem_of_ne_nil Hys,
  ne_nil_of_mem (mem_product Hx Hy)

  definition update : list A → ℕ → A → option (list A)
  | []      _       _ := none
  | (x::xs) 0       y := some (y::xs)
  | (x::xs) (n + 1) y := option.map (λxs', x::xs') (update xs n y) 

  theorem update_eq_some (b : A) : ∀ {l : list A} {n : nat}, n < length l →
    Σ l', update l n b = some l'
  | []     n        h := absurd h !not_lt_zero
  | (a::l) 0        h := ⟨b::l, rfl⟩
  | (a::l) (succ n) h :=
    have n < length l, from lt_of_succ_lt_succ h,
    obtain l' Hl', from update_eq_some this,
    ⟨a::l', by rewrite [↑update, Hl']⟩

  theorem length_update {b : A} : ∀ {l l' : list A} {n : nat}, update l n b = some l' →
    length l' = length l
  | []     l' n H := by contradiction
  | (a::l) l' 0 H := begin
    injection H with l'_eq,
    rewrite [-l'_eq]
  end
  | (a::l) l' (succ n) H := begin
    unfold update at H,
    note rec := λ l', @length_update l l' n,
    revert H rec,
    cases update l n b with l'',
    { contradiction },
    { esimp,
      intro H rec, injection H with l'_eq,
      cases l' with a' l',
      { contradiction },
      { simp }
    }
  end

  theorem nth_update {b : A} : ∀ {l l' : list A} (i : ℕ) {n : nat}, update l n b = some l' →
    nth l' i = (if n = i then some b else nth l i) :=
  begin
    intro l, induction l with a l ih,
    { contradiction },
    { intro l' i n H,
      cases n with n,
      { injection H with l'_eq,
        rewrite [-l'_eq],
        cases i with i; repeat esimp
      },
      { unfold update at H,
        note ih' := λ l' i, @ih l' i n,
        revert H ih',
        cases update l n b with l'',
        { contradiction },
        { esimp,
          intro H rec, injection H with l'_eq,
          cases l' with a' l',
          { contradiction },
          { cases i with i,
            { injection l'_eq with a_eq,
              rewrite [if_neg (show succ n ≠ 0, by contradiction)],
              simp },
            { rewrite [+nth_succ, if_congr (iff.intro eq_of_succ_eq_succ (congr_arg succ)) rfl rfl],
              apply rec,
              injection l'_eq,
              rewrite [`l'' = l'`] }
          }
        }
      }
    }
  end

  definition drop_while (P : A → Prop) [decidable_pred P] : list A → list A
  | []    := []
  | (x::xs) := if P x then drop_while xs else x::xs

  lemma drop_while_cons (P : A → Prop) [decidable_pred P] (x : A) (xs : list A) :
    drop_while P (x::xs) = if P x then drop_while P xs else x::xs := 
  rfl

  lemma map₂_self {B : Type} (f : A → A → B) : Π(xs : list A), map₂ f xs xs = map (λ x, f x x) xs
  | []      := rfl
  | (x::xs) := by rewrite [map_cons, ↑map₂, map₂_self]

  lemma dropn_append {A : Type} : Π{n : ℕ} {xs ys : list A} (h : length xs ≥ n),
    dropn n (xs ++ ys) = dropn n xs ++ ys
  | 0 xs ys h := rfl
  | (succ n) [] ys h := false.elim (not_le_of_gt !zero_lt_succ h)
  | (succ n) (x::xs) ys h := by rewrite [append_cons, ↑dropn, dropn_append (le_of_succ_le_succ h)]

  lemma dropn_replicate {A : Type} : Π(n m : ℕ) (a : A),
    dropn n (replicate m a) = replicate (m-n) a
  | 0 m a := rfl
  | n 0 a := by rewrite [nat.zero_sub, ↑replicate, dropn_nil]
  | (succ n) (succ m) a := by rewrite [↑replicate at {1}, ↑dropn at {1}, dropn_replicate,
    succ_sub_succ]

  lemma replicate_succ_right {A : Type} : Π(n : ℕ) (x : A),
    replicate (succ n) x = replicate n x ++ [x]
  | 0 x := rfl
  | (succ n) x := by rewrite [↑replicate at {1}, replicate_succ_right at {1}]
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

  theorem nth_of_nth_prefixeq {i : ℕ} {xs ys : list A} {z : A} (Hxs : nth xs i = some z)
    (Hprefix : xs ⊑ₚ ys) : nth ys i = some z :=
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

  theorem mem_of_mem_prefixeq {xs ys : list A} {z : A} (Hxs : z ∈ xs) (Hprefix : xs ⊑ₚ ys) :
    z ∈ ys :=
  obtain i Hi, from nth_of_mem Hxs,
  mem_of_nth (nth_of_nth_prefixeq Hi Hprefix)

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

theorem dif_pos' {c : Prop} {H : decidable c} (Hc : c) {A : Type} {t : c → A} {e} :
  (dite c t e) = t Hc :=
decidable.rec
  (λ Hc : c,    eq.refl (@dite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

lemma ite_prop {A : Type} {c : Prop} [decidable c] {t e : A} {p : A → Prop}
  (ht : c → p t) (he : ¬c → p e) :
  p (ite c t e) :=
if h : c then by rewrite [if_pos h]; apply ht h
else by rewrite [if_neg h]; apply he h

namespace nat

lemma le_pred_of_lt {a b : ℕ} (h : a < b) : a ≤ b - 1 :=
begin
  cases b,
  { apply le_of_lt h },
  { apply le_of_succ_le_succ h }
end

section
  open interval
  open set

  section
    open finset

    lemma not_finite_of_no_upper_bound {s : set ℕ} (Hno_ub : ∀x, ∃y, y ≥ x ∧ y ∈ s) : ¬finite s :=
    suppose finite s,
    obtain s' `s = to_set s'`, from this,
    let x := Max₀ s' + 1 in
    obtain y `y ≥ x` `y ∈ s`, from Hno_ub x,
    have y ∈ s', from `s = to_set s'` ▸ `y ∈ s`,
    have y ≤ Max₀ s', from le_Max₀ this,
    show false, from not_le_of_gt (lt_of_succ_le `y ≥ x`) this
  end

  -- integral (floored) logarithm
  noncomputable definition log (b x : ℕ) := Max₀ {y | b^y ≤ x}

  parameter {b : ℕ}
  variable  {x : ℕ}
  premise (Hx : x ≥ 1)

  attribute Max₀ log [reducible]

  -- why did i prove this
  lemma log_base_zero_eq_zero (x : ℕ) : log 0 x = 0 :=
  begin
    have ¬finite {y | 0^y ≤ x}, begin
      apply not_finite_of_no_upper_bound,
      intro x, existsi succ x,
      split,
      exact le_succ _,
      whnf, rewrite [zero_pow (zero_lt_succ x)], apply zero_le
    end,
    esimp [log, Max₀, set.Max],
    rewrite [to_finset_of_not_finite this]
  end

  lemma log_zero_eq_zero : log b 0 = 0 :=
  begin
    cases eq_zero_or_pos b,
    { rewrite [`b = 0`], apply log_base_zero_eq_zero },
    { have {y | b^y ≤ 0} = ∅, from eq_empty_of_forall_not_mem (take y,
        suppose b^y ≤ 0,
        have b^y = 0, from eq_zero_of_le_zero this,
        have b^y > 0, from pow_pos_of_pos y `b > 0`,
        show false, from ne_of_gt this `b^y = 0`),
      rewrite [↑log, this, ↑Max₀, ↑set.Max, to_finset_empty] }
  end

  hypothesis (Hb : b > 1)
  include Hb

  private definition fin : finite {y | b^y ≤ x} :=
  finite_subset (show {y | b^y ≤ x} ⊆ '[0, x], from
    take y, suppose b^y ≤ x,
    and.intro !nat.zero_le (le.trans (le_pow_self Hb y) this)
  )

  private definition nonempty : {y | b^y ≤ x} ≠ ∅ :=
  ne_empty_of_mem (show b^0 ≤ x, from Hx)

  lemma log_le {a : ℕ} (H : ∀ y, b ^ y ≤ x → y ≤ a)
  : log b x ≤ a :=
  let Hx := Hx in
  begin
    apply Max_le,
    apply fin,
    apply nonempty Hx,
    apply H
  end

  lemma log_one_eq_zero : log b 1 = 0 :=
  eq_zero_of_le_zero (log_le !le.refl (take y,
    suppose b^y ≤ 1,
    show y ≤ 0, begin
      cases y,
      { apply le.refl },
      { exfalso, apply nat.lt_irrefl _ (lt_of_le_of_lt this (pow_gt_one Hb !zero_lt_succ)) }
    end))

  lemma log.rec : log b (b * x) = log b x + 1 :=
  have finite {y | b^y ≤ x}, from fin,
  have finite {y | b^y ≤ b * x}, from fin,
  have Hx' : b * x ≥ 1, from nat.mul_le_mul (le_of_lt Hb) Hx,
  have log b x + 1 = Max y ∈ {y | b^y ≤ x}, y + 1, from eq.symm (Max_add_right _ _ (nonempty Hx)),
  begin
    rewrite this,
    apply eq_of_le_of_ge,
    { apply Max_le _ (nonempty Hx'),
      intro y Hy, cases y with y',
      { apply nat.zero_le },
      { apply le_Max, apply le_of_mul_le_mul_left Hy (lt_of_succ_lt Hb) }
    },
    { apply Max_le _ (nonempty Hx),
      intro y Hy,
      apply le_Max, apply mul_le_mul_left b Hy
    }
  end

  lemma log_pow : log b (b^x) = x :=
  begin
    induction x with x ih,
    { apply log_one_eq_zero },
    { have b^x ≥ 1, from pow_ge_one _ (le_of_lt Hb),
      rewrite [pow_succ, log.rec this, ih] }
  end

  lemma nondecreasing_log : nondecreasing (log b) :=
  take x x',
  assume H : x ≤ x',
  have finite {y | b^y ≤ x'}, from fin,
  begin
    cases x,
    { rewrite log_zero_eq_zero, apply zero_le },
    { apply log_le !one_le_succ,
      intro y Hy,
      apply le_Max, apply le.trans Hy H }
  end

  notation `log₂` := log 2

end
end nat

lemma nondecreasing_pow {A : Type} [linear_ordered_semiring A] {b : A} (hb : b ≥ 1) :
  nondecreasing (pow_nat b) :=
begin
  intro x,
  induction x with x ih, all_goals intro x' h,
  { krewrite [pow_zero], apply !pow_ge_one hb },
  { cases x',
    { exfalso, apply lt_le_antisymm !zero_lt_succ h },
    { rewrite [+pow_succ],
      apply mul_le_mul_of_nonneg_left (ih (le_of_succ_le_succ h)) (le.trans zero_le_one hb) }
  }
end

lemma strictly_increasing_pow {A : Type} [linear_ordered_semiring A] {b : A} (hb : b > 1) :
  strictly_increasing (pow_nat b) :=
begin
  intro x,
  induction x with x ih, all_goals intro x' h,
  { krewrite [pow_zero], apply !pow_gt_one hb h },
  { cases x',
    { exfalso, apply lt_le_antisymm !zero_lt_succ h },
    { rewrite [+pow_succ],
      apply mul_lt_mul_of_pos_left (ih (le_of_succ_le_succ h)) (lt.trans zero_lt_one hb) }
  }
end

lemma nat.self_sub_half_sub_one_le_half (n : ℕ) : n - n / 2 - 1 ≤ n / 2 :=
begin
  rewrite [eq_div_mul_add_mod n 2 at {1}, -one_add_one_eq_two at {2}, left_distrib, +mul_one,
    nat.add_assoc, nat.add_sub_cancel_left],
  transitivity n / 2 + 1 - 1,
  { apply nat.sub_le_sub_right,
    apply add_le_add_left,
    apply le_of_lt_succ (mod_lt _ dec_trivial) },
  { rewrite [nat.add_sub_assoc (le_of_eq rfl)] }
end

namespace finset
  open list

  lemma to_finset_ne_empty {A : Type} [decidable_eq A] {xs : list A} (H : xs ≠ []) :
    to_finset xs ≠ ∅ :=
  obtain x Hmem, from list.ex_mem_of_ne_nil H,
  suppose to_finset xs = ∅,
  this ▸ mem_to_finset Hmem

  lemma mem_of_mem_to_finset {A : Type} [decidable_eq A] {xs : list A} {x : A} (H : x ∈ to_finset xs)
    : x ∈ xs := mem_of_mem_erase_dup H
end finset

namespace set
  open prod
  open filter

  definition prod {A B : Type} (a : set A) (b : set B) : set (A × B) :=
  {p | pr1 p ∈ a ∧ pr2 p ∈ b}

  namespace prod
  section
    variables {A B : Type}

    notation a `*` b := prod a b

    lemma univ : @univ A * @univ B = univ :=
    eq_of_subset_of_subset
    (take x H, !mem_univ)
    (take x H, and.intro !mem_univ !mem_univ)

    lemma subseteq {a₁ a₂ : set A} {b₁ b₂ : set B} (Ha : a₁ ⊆ a₂) (Hb : b₁ ⊆ b₂) :
      a₁ * b₁ ⊆ a₂ * b₂ :=
    take x Hx,
    obtain Hx₁ Hx₂, from Hx,
    and.intro (Ha Hx₁) (Hb Hx₂)

    lemma subset_inter (a₁ a₂ : set A) (b₁ b₂ : set B) :
      (a₁ ∩ a₂) * (b₁ ∩ b₂) ⊆ (a₁ * b₁) ∩ (a₂ * b₂) :=
    take x H,
    obtain Ha Hb₁ Hb₂, from H,
    obtain Ha₁ Ha₂, from Ha,
    and.intro (and.intro Ha₁ Hb₁) (and.intro Ha₂ Hb₂)
  end
  end prod

  namespace prod_filter
  section
    parameters {A B : Type} (Fa : filter A) (Fb : filter B)
    
    definition sets := {p | ∃₀a ∈ Fa, ∃₀b ∈ Fb, prod a b ⊆ p}
  end
  end prod_filter

  definition prod_filter {A B : Type} (Fa : filter A) (Fb : filter B) : filter (A × B) := ⦃filter,
    sets := prod_filter.sets Fa Fb,
    univ_mem_sets := bounded_exists.intro (univ_mem_sets Fa) (
      bounded_exists.intro (univ_mem_sets Fb) (subset_univ _)
    ),
    inter_closed := take a b Ha Hb,
    obtain a₁ Ha₁ b₁ Hb₁ H₁, from Ha,
    obtain a₂ Ha₂ b₂ Hb₂ H₂, from Hb,
    bounded_exists.intro (inter_closed Fa Ha₁ Ha₂) (
      bounded_exists.intro (inter_closed Fb Hb₁ Hb₂) (subset_inter
        (take x H,
         obtain Ha Hb, from H,
         H₁ (and.intro (and.left Ha) (and.left Hb)))
        (take x H,
         obtain Ha Hb, from H,
         H₂ (and.intro (and.right Ha) (and.right Hb))))
    ),
    is_mono := take p₁ p₂ `p₁ ⊆ p₂` Hp₁,
    obtain a Ha b Hb Hp₁, from Hp₁,
    bounded_exists.intro Ha (bounded_exists.intro Hb (subset.trans Hp₁ `p₁ ⊆ p₂`))
  ⦄
end set

namespace tuple
section
  open subtype
  parameters {A B C : Type}


  definition length [reducible] {n} (xs : tuple A n) : ℕ := n

  notation [ x ] := x :: nil

  lemma map₂_cons {n : ℕ} (f : A → B → C) (x : A) (y : B): Π(xs : tuple A n) (ys : tuple B n),
    map₂ f (x::xs) (y::ys) = f x y :: map₂ f xs ys
  | (tag lxs hxs) (tag lys hys) := by esimp

  lemma replicate_succ (n : ℕ) (x : A) : replicate (nat.succ n) x = x :: replicate n x := rfl

  lemma replicate_succ_right (n : ℕ) (x : A) : replicate (nat.succ n) x = replicate n x ++ [x] :=
  subtype.tag_eq !list.replicate_succ_right
end
end tuple

lemma exists_true_Prop_iff {p : Prop} (h : p) (q : p → Prop) : Exists q ↔ q h :=
iff.intro (take h, obtain h' hh', from h, hh') !exists.intro
