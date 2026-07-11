import Mathlib

open Finset

lemma claim2 {n : ℕ} [NeZero n] {a b : ZMod n} : a = b ↔ a.val ≡ b.val [MOD n] := by
  refine ⟨?_, ?_⟩
  · rintro rfl; rfl
  intro h
  rw [← ZMod.natCast_zmod_val a]
  rw [← ZMod.natCast_zmod_val b]
  unfold Nat.ModEq at h
  rw [← ZMod.val_natCast] at h
  rw [← ZMod.val_natCast] at h
  simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at h
  rw [h]

lemma claim3 {n : ℕ} [NeZero n] (a : ZMod n) (k : ℕ) : (a ^ k).val ≡ a.val ^ k [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [ZMod.natCast_val, dvd_refl, ZMod.cast_pow, ZMod.cast_id', id_eq, Nat.cast_pow]

lemma claim1 {p : ℕ} [NeZero p] (h : Nat.Prime p) :
    #{n : ZMod (p^2) | n^2+1 = 0} ≤ if p % 4 = 1 then 2 else 0 := by
  split; case isTrue hp =>
    let S : Finset (ZMod (p^2)) := {n : ZMod (p^2) | n^2+1 = 0}; change #S ≤ 2
    by_cases ex : S = ∅
    · rw[ex]; simp only [card_empty, zero_le]
    obtain ⟨n, nh⟩ := nonempty_def.mp (nonempty_iff_ne_empty.mpr ex)
    suffices S = {n, -n} by rw[this]; exact card_le_two
    ext a; refine ⟨?_, by grind⟩
    intro ah; unfold S at ah nh
    simp only [mem_filter, mem_univ, true_and] at ah nh
    rw[←nh] at ah

    --my code
    /-replace ah : (a - n)*(a + n) = 0 := by grind only
    apply (ZMod.val_eq_zero _).mpr at ah
    rw[ZMod.val_mul, ZMod.val_add] at ah
    sorry-/

    --ruben's code
    replace ah : a ^ 2 = n ^ 2 := by grind only
    have : Fact (1 < p ^ 2) := ⟨one_lt_pow' h.one_lt two_ne_zero⟩
    rw [claim2] at ah
    replace ah := ((claim3 a 2).symm.trans ah).trans (claim3 n 2)
    rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd] at ah
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_pow] at ah
    rw [sq_sub_sq] at ah
    by_cases hdvd : (p : ℤ) ∣ (n.val - a.val)
    · by_cases! hdvd2 : ¬ (p : ℤ) ∣ (n.val + a.val)
      · have := Prime.pow_dvd_of_dvd_mul_left (Nat.prime_iff_prime_int.mp h) 2 hdvd2 ah
        obtain rfl : n = a := by
          rw [← Int.modEq_iff_dvd, ← Nat.cast_pow, Int.natCast_modEq_iff, ← claim2] at this
          rw [this]
        simp
      have : (p : ℤ) ∣ 2 * n.val := by
        convert hdvd2.add hdvd using 1
        ring
      rw [(Nat.prime_iff_prime_int.mp h).dvd_mul] at this
      cases this with
      | inl h2 =>
        rw [(Nat.prime_iff_prime_int.mp h).dvd_prime_iff_associated Int.prime_two,
          Int.associated_iff_natAbs] at h2
        simp only [Int.natAbs_natCast, Int.reduceAbs] at h2
        subst h2
        simp at hp
      | inr h2 =>
        have : (1 : ZMod (p ^ 2)) = 0 := calc
          (1 : ZMod (p ^ 2)) = 0 + 1 := (zero_add _).symm
          _ = n ^ 2 + 1 := by
            congr
            rw [eq_comm, claim2]
            simp only [ZMod.val_zero]
            refine .trans (claim3 _ _) ?_
            rw [@Nat.modEq_zero_iff_dvd]
            apply pow_dvd_pow_of_dvd
            rwa [Int.natCast_dvd_natCast] at h2
          _ = 0 := nh
        simp at this
    · have := Prime.pow_dvd_of_dvd_mul_right (Nat.prime_iff_prime_int.mp h) 2 hdvd ah
      obtain rfl : n = - a := by
        rw [← add_eq_zero_iff_eq_neg, claim2]
        simp only [ZMod.val_add, ZMod.val_zero]
        grw [Nat.mod_modEq]
        rw [Nat.modEq_zero_iff_dvd]
        norm_cast at this
      simp
  case isFalse hp =>
    simp only [Nat.le_zero_eq, card_eq_zero, filter_eq_empty_iff, mem_univ, forall_const]
    intro n; by_contra c
    have nun : IsUnit n := IsUnit.of_mul_eq_one_right (-n) (by grind only)
    have : orderOf nun.unit = 4 := by
      refine (orderOf_eq_iff (by simp)).mpr ⟨?_, ?_⟩
      · apply Units.ext
        simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]
        grind only
      · intro m hm h_pos; interval_cases m
        · simp only [pow_one, ne_eq]
          by_contra no
          replace no := Units.val_eq_one.mpr no; simp only [IsUnit.unit_spec] at no
          subst no; simp only [one_pow, one_add_one_eq_two] at c
          replace c := (ZMod.natCast_eq_zero_iff 2 (p^2)).mp c
          replace c : p^2 ≤ 2 := Nat.le_of_dvd (by norm_num) c
          have := Nat.pow_le_pow_left (Nat.Prime.two_le h) 2
          lia
        · intro htwo
          sorry
        · sorry
    replace := this ▸ orderOf_dvd_natCard nun.unit
    rw[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient (p^2)] at this
    rw[Nat.totient_prime_pow h (n := 2) (by grind)] at this
    simp only [Nat.add_one_sub_one, pow_one] at this
    rcases (show p%4 = 0 ∨ p%4 = 2 ∨ p%4 = 3 by lia) with c1 | c2 | c3
    · have : 4 ∣ p := by grind
      rcases ((Nat.dvd_prime h).mp this) with h4 | h4
      · contradiction
      · subst h4; contradiction
    · have : Even p := by grind only [= Nat.even_iff]
      have : p = 2 := (Nat.Prime.even_iff h).mp this
      subst this; contradiction
    · have m1 : (p * (p-1)) ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr this
      have m3 : (p * (p - 1)) ≡ 3 * (3 - 1) [MOD 4] := by
        have m2 : p ≡ 3 [MOD 4] := Nat.modEq_modulus_add_iff.mp c3
        apply Nat.ModEq.mul m2
        refine Nat.ModEq.sub_right ?_ ?_ m2 <;> exact NeZero.one_le
      have := Nat.ModEq.trans (Nat.ModEq.symm m1) m3
      contradiction
