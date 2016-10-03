import move

open bool
open eq.ops
open list
open nat
open option

attribute bool.has_decidable_eq [unfold 1 2]

lemma nat.mod_2_eq_0_of_ne_1 {n : ℕ} (h : n % 2 ≠ 1) : n % 2 = 0 :=
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
  := list.rec 0 (λ x xs rec, (if x = tt then 1 else 0) + 2 * rec) -- HACK

  definition norm [class] (xs : bits) := last' xs ≠ some ff

  definition normalize : bits → bits
  | []       := []
  | (tt::xs) := tt::normalize xs
  | (ff::xs) := match normalize xs with
    | []  := []
    | xs' := ff::xs'
    end

  definition and (xs ys : bits) : bits := normalize (map₂ band xs ys)

  infix && := and

  definition or' : bits → bits → bits
  | xs []           := xs
  | [] ys           := ys
  | (x::xs) (y::ys) := (x || y) :: or' xs ys
  definition or (xs ys : bits) : bits := normalize (or' xs ys)

  infix || := or

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
      { rewrite [▸*, nat.eq_div_mul_add_mod n 2 at {2}, add.comm, mul.comm,
          nat.mod_2_eq_0_of_ne_1 heven] }
    },
  end

  lemma norm_nil [instance] : norm nil := option.no_confusion

  lemma norm_singleton_elim : Π{x : bool}, norm [x] → x = tt
  | ff := begin
    rewrite [↑norm, ↑last', last_singleton],
    intro h, exfalso, exact h rfl
  end
  | tt := take h, rfl

  lemma norm_of_norm_cons [instance] {x : bool} : Π{xs : list bool} [norm (x::xs)], norm xs
  | []      h := by contradiction
  | (x::xs) h := by exact h

  lemma norm_tt_cons_of_norm [instance] : Π{xs : list bool} [norm xs], norm (tt::xs)
  | []      h := begin
    rewrite [↑norm, ↑last', last_singleton],
    intro h, injection h, contradiction
  end
  | (x::xs) h := by exact h

  lemma norm_of_nat [instance] (n : ℕ) : norm (of_nat n) :=
  begin
    rewrite [↑of_nat],
    induction well_founded.apply nat.lt.wf n with n _ ih,
    rewrite well_founded.fix_eq,
    cases (_ : decidable (n = 0)) with _ pos,
    { rewrite [↑norm, ↑last'], contradiction },
    {
      note ih := ih (n / 2) (nat.div_lt_of_ne_zero `n ≠ 0`),
      cases (_ : decidable (n % 2 = 1)) with odd heven,
      { apply norm_tt_cons_of_norm },
      { have n / 2 ≠ 0, from take contr,
          have n = 0, by rewrite [nat.eq_div_mul_add_mod n 2, contr, nat.mod_2_eq_0_of_ne_1 heven],
          pos this,
        revert ih, rewrite [▸*, well_founded.fix_eq, dif_neg this],
        apply id
      }
    },
  end

  lemma of_nat_to_nat : Π(xs : list bool) [norm xs], of_nat (to_nat xs) = xs
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
    have norm xs, begin
      cases xs,
      { contradiction },
      { exact h }
    end,
    rewrite [of_nat_to_nat xs],
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
      of_nat_to_nat xs
    ]
  end

  lemma normalize_idem : Π(xs : list bool),
    normalize (normalize xs) = normalize xs
  | [] := rfl
  | (ff::xs) := begin
    rewrite [↑normalize at {1,3}],
    apply generalize_with_eq (normalize xs), intro nxs nxs_eq,
    cases nxs,
    { esimp },
    { rewrite [↑normalize, -nxs_eq, normalize_idem, nxs_eq] }
  end
  | (tt::xs) := by rewrite [↑normalize, normalize_idem]

  lemma normalize_cons_normalize : Π(x : bool) (xs : list bool),
    normalize (x::normalize xs) = normalize (x::xs)
  | x [] := rfl
  | ff (x'::xs) := by rewrite [↑normalize at {2,3}, normalize_idem]
  | tt (x'::xs) := by rewrite [↑normalize at {2,3}, normalize_idem]

  lemma normalize_norm [instance] : Π(xs : bits), norm (normalize xs)
  | [] := by rewrite [↑normalize]; exact norm_nil
  | (ff::xs) := begin
    rewrite [↑normalize],
    eapply generalize_with_eq (normalize xs), intro nxs nxs_eq,
    cases nxs,
    { apply norm_nil },
    apply sorry
    --{ rewrite [▸*, ↑norm, ↑last', last'_cons_eq_last'] }
  end
  | (tt::xs) := sorry

  lemma and_nil1 : Π(ys : list bool), nil && ys = nil
  | []      := rfl
  | (y::ys) := rfl

  lemma and_nil2 : Π(xs : list bool), xs && nil = nil
  | []      := rfl
  | (x::xs) := rfl

  lemma and_cons (x y : bool) (xs ys : bits) : (x::xs) && (y::ys) = normalize ((x && y)::xs && ys) :=
  by rewrite [↑and, ↑map₂ at {1}, normalize_cons_normalize]

  lemma or_nil1 : Π(ys : list bool), nil || ys = normalize ys
  | []      := rfl
  | (y::ys) := rfl

  lemma or_nil2 : Π(xs : list bool), xs || nil = normalize xs
  | []      := rfl
  | (x::xs) := rfl

  lemma or_cons (x y : bool) (xs ys : bits) : (x::xs) || (y::ys) = normalize ((x || y)::(xs || ys)) :=
  by rewrite [↑or, ↑or' at {1}, normalize_cons_normalize]

  /-lemma or_norm [instance] : Π(xs ys : list bool) [norm xs] [norm ys], norm (xs || ys)
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
    note ih := or_norm xs ys,
    cases xs,
    { rewrite [norm_singleton_elim h₁, bool.tt_bor],
      apply norm_tt_cons_of_norm },
    { cases ys,
      { rewrite [norm_singleton_elim h₂, bool.bor_tt],
        apply norm_tt_cons_of_norm },
      { rewrite [↑or], apply ih }
    }
  end-/

  -- HACK
  lemma and_def (xs ys : bits) : xs && ys = normalize (map₂ band xs ys) := rfl

  lemma normalize_and (xs ys : bits) : normalize (xs && ys) = xs && ys := normalize_idem _

  lemma and_normalize1 : Π(xs ys : bits), normalize xs && ys = xs && ys
  | [] ys := rfl
  | (ff::xs) ys := begin
    rewrite [↑and, ↑normalize at {1}],
    apply generalize_with_eq (normalize xs), intro nxs nxs_eq,
    cases nxs,
    { cases ys,
      { esimp },
      { rewrite [▸*, map₂_nil1, ↑map₂, ff_band, ↑normalize at {2}, -and_def,
          -and_normalize1, nxs_eq, and_nil1] }
    },
    { cases ys,
      { esimp },
      { rewrite [▸*, ↑map₂, ff_band, ↑normalize, -nxs_eq, -and_def, and_normalize1] }
    }
  end
  | (tt::xs) [] := rfl
  | (tt::xs) (ff::ys) := by rewrite [↑normalize, ↑and, ↑map₂, tt_band, ↑normalize at {2,3},
    -and_def, and_normalize1]
  | (tt::xs) (tt::ys) := by rewrite [↑normalize, ↑and, ↑map₂, tt_band, ↑normalize at {2,3},
    -and_def, and_normalize1]

  lemma or_normalize1 : Π(xs ys : bits), normalize xs || ys = xs || ys := sorry
  lemma or_normalize2 : Π(xs ys : bits), xs || normalize ys = xs || ys := sorry

  lemma and_or_distrib : Π(xs ys zs : list bool), (xs || ys) && zs = xs && zs || ys && zs :=
  begin
    intro xs,
    induction xs with x xs ih, all_goals intro ys zs,
    { rewrite [and_nil1, +or_nil1, normalize_and, and_normalize1] },
    { cases ys with y ys,
      { rewrite [and_nil1, +or_nil2, normalize_and, and_normalize1] },
      { cases zs with z zs,
        { rewrite [+and_nil2] },
        { rewrite [↑or at {1}, ↑or', and_normalize1, +and_cons, or_normalize1, or_normalize2,
            or_cons, band_bor_distrib, -ih, -and_normalize1] }
      }
    }
  end
end bits

namespace nat.bitwise
  definition and (x y : nat) : nat :=
  bits.to_nat (bits.and (bits.of_nat x) (bits.of_nat y))

  infix && := and

  definition or (x y : nat) : nat :=
  bits.to_nat (bits.or (bits.of_nat x) (bits.of_nat y))

  infix || := or

  open [notation] bits

  lemma and_or_distrib (x y z : ℕ) : (x || y) && z = x && z || y && z :=
  sorry -- by rewrite [↑and, ↑or, bits.of_nat_to_nat]

  lemma and_or_self (x y : ℕ) : (x || y) && y = y :=
  sorry
end nat.bitwise
