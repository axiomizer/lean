import Mathlib

lemma l1 (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, i^3 = n^2 * (n+1)^2 / 4 := by
  induction n with | zero | succ n ih
  · simp
  · exact calc ∑ i ∈ Finset.Icc 1 (n+1), i^3
      _ = ∑ i ∈ insert (n+1) (Finset.Icc 1 n), i^3 := by
        have : insert (n+1) (Finset.Icc 1 n) = Finset.Icc 1 (n+1) := by
          refine Finset.insert_Icc_right_eq_Icc_succ ?_
          simp
        rw[congrFun (congrArg Finset.sum this) fun i ↦ i^3]
      _ = (n+1)^3 + ∑ i ∈ Finset.Icc 1 n, i^3 := by
        have : n+1 ∉ Finset.Icc 1 n := by rw[Finset.mem_Icc]; simp
        exact Finset.sum_insert this
      _ = (n+1)^3 + n^2 * (n+1)^2 / 4 := by rw[ih]
      _ = 4 * (n+1)^3 / 4 + n^2 * (n+1)^2 / 4 := by grind
      _ = (4 * (n+1)^3 + n^2 * (n+1)^2) / 4 := by
        symm
        refine Nat.add_div_of_dvd_left ?_
        by_cases c : Odd n
        · let ⟨k, kh⟩ := c; clear c; subst kh
          exists (2*k+1)^2 * (k+1)^2
          linarith
        · simp at c; let ⟨k, kh⟩ := c; clear c; subst kh
          exists k^2 * (2*k+1)^2
          linarith
      _ = (n+1)^2 * (n+1+1)^2 / 4 := by
        suffices (4 * (n+1)^3 + n^2 * (n+1)^2) = (n+1)^2 * (n+1+1)^2
          from congrFun (congrArg HDiv.hDiv this) 4
        linarith

theorem nt1 : Maximal (fun n ↦ n+3 ∣ ∑ i ∈ Finset.Icc 1 n, i^3) 15 := by
  simp[l1]
  and_intros <;> simp
  intro y yh
  suffices y ≤ 15 from fun _ ↦ this
  by_cases par : Odd y
  · let ⟨j, jh⟩ := par; clear par; subst jh
    have : (2*j+1)^2 * (2*j+1+1)^2 / 4 = (2*j+1)^2 * (j+1)^2 := by grind
    rw[this] at yh; clear this
    have : Odd j := by
      have : Even ((2*j+1)^2 * (j+1)^2) := by
        have : 2 ∣ 2*j+4 := by exists (j+2)
        replace := Nat.dvd_trans this yh
        grind
      grind
    let ⟨k, kh⟩ := this; clear this; subst kh
    let ⟨m, mh⟩ := yh; clear yh
    have : (2*k+3 : ℤ) ∣ (k+6 : ℤ) := by
      refine Dvd.intro (m-16*k*(k+1)^2 - 9*k-4 : ℤ) ?_
      linarith
    replace : 2*k+3 ∈ (k+6).divisors := by
      refine Nat.mem_divisors.mpr ⟨?_, ?_⟩
      · exact Int.ofNat_dvd.mp this
      · simp
    replace : 2*k+3 ≤ k+6 := Nat.divisor_le this
    linarith
  · simp at par; let ⟨j, jh⟩ := par; clear par; subst jh
    have : (j+j)^2 * (j+j+1)^2 / 4 = j^2 * (2*j+1)^2 := by grind
    rw[this] at yh; clear this
    let ⟨k, kh⟩ := yh; clear yh
    have : (2*j+3 : ℤ) ∣ (9 : ℤ) := by
      refine Dvd.intro (k - 2*j^3 + j^2 - 2*j + 3) ?_
      linarith
    replace : 2*j+3 ∈ (9 : ℕ).divisors := by
      refine Nat.mem_divisors.mpr ⟨?_, ?_⟩
      · exact Int.ofNat_dvd.mp this
      · simp
    replace : 2*j+3 ≤ 9 := Nat.divisor_le this
    linarith
