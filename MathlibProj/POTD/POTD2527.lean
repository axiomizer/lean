import Init.Data.Int.Gcd
import Mathlib.Data.Set.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Multiplicity
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Sign.Basic

theorem POTD_2527 : {k : ℤ | k > 0 ∧ k < 2024 ∧ (∀ n : ℤ, Int.gcd (4*n+1) (k*n+1) = 1)} =
    {2,3,5,6,8,12,20,36,68,132,260,516,1028} := by
  have : ∀ k : ℤ, (∀ n : ℤ, (4*n+1).gcd (k*n+1) = 1) ↔ (∃ r : ℕ, k-4 = 2^r ∨ k-4 = -2^r) := by
    have gcd_simp: ∀ k n : ℤ, (4*n+1).gcd (k*n+1) = (4*n+1).gcd (k-4) := by
      intro k n
      rw[←Int.gcd_add_mul_right_right (4*n+1) (k*n+1) (-1)]
      rw[show (k*n+1) + (-1)*(4*n+1) = n*(k-4) by lia]
      rw[Int.gcd_mul_right_right_of_gcd_eq_one (by simp)]
    intro k; constructor
    · intro hgcd
      replace hgcd : ∀ n : ℤ, (4*n+1).gcd (k-4) = 1 := by
        intro n; specialize hgcd n
        rw[gcd_simp k n] at hgcd; assumption
      replace hgcd : ∀ p : ℤ, Prime p → Odd p → ¬ p ∣ (k-4) := by
        intro p pha phb phc
        suffices ∃ n : ℤ, p ∣ (4*n+1) by
          obtain ⟨n, nh⟩ := this
          have := Int.dvd_coe_gcd nh phc
          rw[hgcd n] at this
          apply Int.ofNat_dvd_right.mp at this
          simp only [Nat.dvd_one] at this
          have : p = 1 ∨ p = -1 := by exact Int.natAbs_eq_natAbs_iff.mp this
          rcases this with po | pno
          · subst po; have := Int.prime_iff_natAbs_prime.mp pha; contradiction
          · subst pno; have := Int.prime_iff_natAbs_prime.mp pha; contradiction
        rcases (show p%4 = 1 ∨ p%4 = 3 by grind only [= Int.odd_iff]) with pm | pm
        · obtain ⟨s, sh⟩ : 4 ∣ (p-1) := Int.dvd_self_sub_of_emod_eq pm
          exists s; exists 1; lia
        · obtain ⟨s, sh⟩ := Int.dvd_self_sub_of_emod_eq pm
          exists (3*s+2); exists 3; lia
      exists multiplicity 2 (k-4)
      obtain ⟨s, sh⟩ := pow_multiplicity_dvd 2 (k-4)
      by_cases sz : s = 0
      · subst s; simp only [mul_zero] at sh; rw[sh] at hgcd
        simp only [dvd_zero, not_true_eq_false, imp_false, Int.not_odd_iff_even] at hgcd
        specialize hgcd 3 Int.prime_three; contradiction
      by_cases so : s.natAbs = 1
      · grind only
      obtain ⟨p, pha, ⟨r, rh⟩⟩ := Int.exists_prime_and_dvd so
      by_cases ptwo : p.natAbs = 2
      · exfalso
        have := Int.abs_eq_natAbs p ▸ sign_mul_abs p
        have : 2 ^ (multiplicity 2 (k-4) + 1) ∣ (k-4) := by
          exists ((SignType.sign p) * r); grind only
        have finmul : FiniteMultiplicity 2 (k-4) := by
          refine Int.finiteMultiplicity_iff.mpr ⟨?_, ?_⟩
          · exact Nat.add_one_add_one_ne_one
          · by_contra c; simp[c] at sh; contradiction
        replace := (FiniteMultiplicity.pow_dvd_iff_le_multiplicity finmul).mp this
        have : 1 ≤ 0 := Nat.add_le_add_iff_left.mp this
        contradiction
      have : Odd p := by
        apply Int.natAbs_odd.mp
        apply Nat.Prime.odd_of_ne_two (Int.prime_iff_natAbs_prime.mp pha)
        exact ptwo
      specialize hgcd p pha this
      suffices p ∣ k-4 by contradiction
      exists 2 ^ multiplicity 2 (k - 4) * r
      grind only
    · intro ⟨r, rh⟩ n
      rw[gcd_simp, Int.gcd_comm]
      have : (k - 4).gcd (4 * n + 1) = (2^r : ℤ).gcd (4 * n + 1) := by
        rcases rh with rh | rh <;> rw[rh]; simp
      rw[this]
      apply Int.gcd_pow_left_of_gcd_eq_one
      rw[show 4*n = 2*(2*n) by lia]
      simp only [dvd_mul_right, Int.gcd_add_left_right_of_dvd, Int.gcd_one]
  replace : {k : ℤ | k > 0 ∧ k < 2024 ∧ (∀ n : ℤ, Int.gcd (4*n+1) (k*n+1) = 1)} =
      {k : ℤ | k > 0 ∧ k < 2024 ∧ (∃ r : ℕ, k-4 = 2^r ∨ k-4 = -2^r)} := by
    apply Set.ext; intro x; constructor
    · intro ⟨xha, xhb, xhc⟩; exact ⟨xha, xhb, (this x).mp xhc⟩
    · intro ⟨xha, xhb, xhc⟩; exact ⟨xha, xhb, (this x).mpr xhc⟩
  rw[this]
  apply Set.ext; intro x; constructor
  · intro ⟨xha, xhb, xhc⟩; obtain ⟨r, rh⟩ := xhc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases rh with rh | rh
    · have : r < 11 := by
        by_contra c; have := calc 2^11
          _ ≤ 2^r := Nat.pow_le_pow_right (by simp) (not_lt.mp c)
          _ < 2^11 := by lia
        contradiction
      interval_cases r <;> grind
    · have : r < 2 := by
        by_contra c; have := calc 2^2
          _ ≤ 2^r :=  Nat.pow_le_pow_right (by simp) (not_lt.mp c)
          _ < 2^2 := by lia
        contradiction
      interval_cases r <;> grind
  · intro xh; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at xh
    simp only [gt_iff_lt, Set.mem_setOf_eq]
    rcases xh with c|c|c|c|c|c|c|c|c|c|c|c|c
    <;> refine ⟨by grind, by grind, ?_⟩
    · exists 1; right; rw[c]; simp
    · exists 0; right; rw[c]; simp
    · exists 0; left; rw[c]; simp
    · exists 1; left; rw[c]; simp
    · exists 2; left; rw[c]; simp
    · exists 3; left; rw[c]; simp
    · exists 4; left; rw[c]; simp
    · exists 5; left; rw[c]; simp
    · exists 6; left; rw[c]; simp
    · exists 7; left; rw[c]; simp
    · exists 8; left; rw[c]; simp
    · exists 9; left; rw[c]; simp
    · exists 10; left; rw[c]; simp
