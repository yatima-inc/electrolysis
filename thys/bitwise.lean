import move

open bool
open eq.ops
open list
open nat
open option

attribute bool.has_decidable_eq [unfold 1 2]

lemma bool.band_bor_self : Π(x y : bool), (x || y) && y = y
| ff y := by rewrite [bool.ff_bor, bool.band_self]
| tt y := by rewrite [bool.tt_bor, bool.tt_band]

namespace nat
  lemma mod_2_eq_0_of_ne_1 {n : ℕ} (h : n % 2 ≠ 1) : n % 2 = 0 :=
    match nat.lt_trichotomy (n % 2) 1 with
    | or.inl lt := nat.eq_zero_of_le_zero (nat.le_of_lt_succ lt)
    | or.inr (or.inl eq) := by contradiction
    | or.inr (or.inr gt) :=
      have n % 2 ≤ 1, from nat.le_of_lt_succ (nat.mod_lt n (show 2 > 0, from dec_trivial)),
      false.elim (nat.lt_le_antisymm gt this)
  end

  definition bits := list bool

  namespace bits
    definition of_nat : ℕ → bits :=
    well_founded.fix (λ n rec,
    if H : n = 0 then []
    else (if n % 2 = 1 then tt else ff) :: rec (n / 2) (div_lt_of_ne_zero H))

    definition to_nat : bits → ℕ
    /-| [] := 0
    | (x::xs) := (if x = tt then 1 else 0) + 2 * to_nat xs-/
    := list.rec 0 (λ x xs rec, (if x = tt then 1 else 0) + 2 * rec)

    definition norm (xs : bits) := last' xs ≠ some ff

    definition normalize : bits → bits
    | []       := []
    | (tt::xs) := tt::normalize xs
    | (ff::xs) := match normalize xs with
      | []  := []
      | xs' := ff::xs'
      end

    definition and (xs ys : bits) : bits := map₂ band xs ys

    definition or : bits → bits → bits
    | xs []           := xs
    | [] ys           := ys
    | (x::xs) (y::ys) := (x || y) :: or xs ys

    lemma to_nat_ne_zero_of_msb_set : Π{xs : list bool}, last' xs = some tt → to_nat xs ≠ 0
    | []          h := by contradiction
    | [tt]        h := dec_trivial
    | [ff]        h := by injection h; contradiction
    | (x::x'::xs) h :=
      have to_nat (x'::xs) ≠ 0, from to_nat_ne_zero_of_msb_set (last'_cons_eq_last' dec_trivial ▸ h),
      have 2 * to_nat (x'::xs) ≠ 0, from nat.mul_ne_zero dec_trivial this,
      take contr,
      this (nat.eq_zero_of_add_eq_zero_left contr)

    lemma to_nat_of_nat (n : ℕ) : to_nat (of_nat n) = n :=
    begin
      rewrite [↑to_nat, ↑of_nat],
      induction well_founded.apply nat.lt.wf n with n _ ih,
      rewrite well_founded.fix_eq,
      cases (_ : decidable (n = 0)),
      { rewrite [▸*, `n = 0`] },
      {
        esimp,
        rewrite [ih (n / 2) (nat.div_lt_of_ne_zero `n ≠ 0`)],
        cases (_ : decidable (n % 2 = 1)) with hodd heven,
        { rewrite [▸*, nat.eq_div_mul_add_mod n 2 at {2}, hodd, add.comm, mul.comm] },
        { rewrite [▸*, nat.eq_div_mul_add_mod n 2 at {2}, add.comm, mul.comm, mod_2_eq_0_of_ne_1 heven] }
      },
    end

    lemma norm_singleton_elim : Π{x : bool}, norm [x] → x = tt
    | ff := begin
      rewrite [↑norm, ↑last', last_singleton],
      intro h, exfalso, exact h rfl
    end
    | tt := take h, rfl

    lemma norm_of_norm_cons {x : bool} : Π{xs : list bool}, norm (x::xs) → norm xs
    | []      h := by contradiction
    | (x::xs) h := by exact h

    lemma norm_tt_cons_of_norm : Π{xs : list bool}, norm xs → norm (tt::xs)
    | []      h := begin
      rewrite [↑norm, ↑last', last_singleton],
      intro h, injection h, contradiction
    end
    | (x::xs) h := by exact h

    lemma norm_of_nat (n : ℕ) : norm (of_nat n) :=
    begin
      rewrite [↑of_nat],
      induction well_founded.apply nat.lt.wf n with n _ ih,
      rewrite well_founded.fix_eq,
      cases (_ : decidable (n = 0)) with _ pos,
      { rewrite [↑norm, ↑last'], contradiction },
      {
        note ih := ih (n / 2) (nat.div_lt_of_ne_zero `n ≠ 0`),
        cases (_ : decidable (n % 2 = 1)) with odd heven,
        { apply norm_tt_cons_of_norm ih },
        { have n / 2 ≠ 0, from take contr,
            have n = 0, by rewrite [nat.eq_div_mul_add_mod n 2, contr, mod_2_eq_0_of_ne_1 heven],
            pos this,
          revert ih, rewrite [▸*, well_founded.fix_eq, dif_neg this],
          apply id
        }
      },
    end

    lemma of_nat_to_nat : Π{xs : list bool}, norm xs → of_nat (to_nat xs) = xs
    | []       h := rfl
    | (tt::xs) h := begin
      rewrite [↑to_nat, ▸*],
      have ∀x, of_nat (1 + 2 * x) = tt :: of_nat x,
      begin
        intro x,
        rewrite [↑of_nat, well_founded.fix_eq,
          dif_neg (show 1 + 2 * x ≠ 0, from nat.ne_zero_of_pos (nat.add_pos_left dec_trivial _)),
          if_pos (show (1 + 2 * x) % 2 = 1, by rewrite [nat.add_mul_mod_self_left]),
          nat.add_mul_div_self_left _ _ (show 2 > 0, from dec_trivial),
          (show (1:ℕ) / 2 = 0, from rfl),
          zero_add
        ],
      end,
      rewrite this,
      have last' xs ≠ some ff, begin
        cases xs,
        { contradiction },
        { exact h }
      end,
      rewrite [of_nat_to_nat this],
    end
    | (ff::xs) h := begin
      let x := to_nat xs,
      have last' (ff::xs) = some tt, begin
        eapply generalize_with_eq (last' (ff::xs)), intro lsb lsb_eq,
        cases lsb with lsb,
        { contradiction },
        { cases lsb,
          { rewrite [↑norm at h, lsb_eq at h], exfalso, exact h rfl },
          exact rfl
        }
      end,
      rewrite [↑of_nat, well_founded.fix_eq, ↓of_nat,
        dif_neg (to_nat_ne_zero_of_msb_set this),
        ↑to_nat,
        if_neg (show (0 + 2 * x) % 2 ≠ 1, by rewrite [nat.add_mul_mod_self_left]; apply dec_trivial),
        nat.add_mul_div_self_left _ _ (show 2 > 0, from dec_trivial),
        (show (0:ℕ) / 2 = 0, from rfl),
        zero_add,
        of_nat_to_nat (norm_of_norm_cons h)
      ]
    end

    lemma or_nil : Π(ys : list bool), or nil ys = ys
    | []      := rfl
    | (y::ys) := rfl

    lemma or_norm : Π{xs ys : list bool}, norm xs → norm ys → norm (or xs ys)
    | [] ys h₁ h₂ := begin
      rewrite [↑or, ▸*],
      induction ys; apply h₂; apply h₂
    end
    | xs [] h₁ h₂ := begin
      rewrite [↑or, ▸*],
      induction xs; apply h₁; apply h₁
    end
    | (x::xs) (y::ys) h₁ h₂ := begin
      rewrite [↑or, ▸*],
      note ih := or_norm (norm_of_norm_cons h₁) (norm_of_norm_cons h₂),
      cases xs,
      { rewrite [norm_singleton_elim h₁, bool.tt_bor],
        apply norm_tt_cons_of_norm ih },
      { cases ys,
        { rewrite [norm_singleton_elim h₂, bool.bor_tt],
          apply norm_tt_cons_of_norm ih },
        { rewrite [↑or], apply ih }
      }
    end
  end bits

  definition bitand (x y : nat) : nat :=
  bits.to_nat (bits.and (bits.of_nat x) (bits.of_nat y))

  local infix && := bitand

  definition bitor (x y : nat) : nat :=
  bits.to_nat (bits.or (bits.of_nat x) (bits.of_nat y))

  local infix || := bitor

  lemma bitand_bitor_self (x y : ℕ) : (x || y) && y = y :=
  have Π(xs ys : list bool), bits.and (bits.or xs ys) ys = ys,
  begin
    intro xs,
    induction xs with x xs ih, all_goals intro ys,
    { rewrite [bits.or_nil, ↑bits.and, map₂_self, map_id' bool.band_self] },
    { 
      cases ys with y ys,
      { rewrite [▸*, ↑bits.and, map₂_nil2] },
      { rewrite [↑bits.or, ↑bits.and, ↑map₂, bool.band_bor_self, ↓bits.and, ih] }
    }
  end,
  by rewrite [↑bitand, ↑bitor,
    bits.of_nat_to_nat (bits.or_norm (bits.norm_of_nat x) (bits.norm_of_nat y)),
    this, bits.to_nat_of_nat]
end nat
