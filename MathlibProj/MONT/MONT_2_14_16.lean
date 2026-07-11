import Mathlib.NumberTheory.Padics.PadicVal.Basic

lemma unique_v2_max (a b : ℕ) (ha : 0 < a) (hb : a ≤ b) :
    ∃! n : ℕ, MaximalFor (fun x : ℕ ↦ x ∈ Finset.Icc a b) (padicValNat 2) n := by
  let img := Finset.image (padicValNat 2) (Finset.Icc a b)
  have := Finset.max'_mem img (Finset.image_nonempty.mpr (Finset.nonempty_Icc.mpr hb))
  obtain ⟨n, nh⟩ := Finset.mem_image.mp this; clear this
  have nmax : ∀ x ∈ Finset.Icc a b, padicValNat 2 x ≤ padicValNat 2 n := by
    intro x xh;
    have := Finset.mem_image_of_mem (padicValNat 2) xh
    replace := Finset.le_max' img (padicValNat 2 x) this
    exact nh.2 ▸ this
  exists n; constructor
  · simp only
    refine ⟨nh.1, ?_⟩
    intro j jh _
    exact nmax j jh
  · intro y; simp only; intro ⟨yha, yhb⟩;
    specialize yhb nh.1
    have : padicValNat 2 n = padicValNat 2 y := by
      have := nmax y yha
      exact le_antisymm (yhb this) this
    by_contra c
    obtain ⟨k1, kh1⟩ := exists_eq_mul_right_of_dvd (pow_padicValNat_dvd (p := 2) (n := n))
    obtain ⟨k2, kh2⟩ := exists_eq_mul_right_of_dvd (pow_padicValNat_dvd (p := 2) (n := y))
    suffices ∃ x, 2 ∣ x ∧ 2 ^ (padicValNat 2 n) * x ∈ Finset.Icc a b by
      obtain ⟨x, ⟨d, dh⟩, xhb⟩ := this
      have xhc := Finset.mem_image_of_mem (padicValNat 2) xhb
      have := calc padicValNat 2 n + 1
        _ ≤ padicValNat 2 (2 ^ padicValNat 2 n * x) := by
          suffices suf : 2^(padicValNat 2 n + 1) ∣ 2 ^ padicValNat 2 n * x by
            refine (padicValNat_dvd_iff_le ?_).mp suf
            grind only [= Finset.mem_Icc]
          exists d; rw[dh, ←mul_assoc, Nat.pow_add_one 2 (padicValNat 2 n)]
        _ ≤ padicValNat 2 n := nmax (2 ^ (padicValNat 2 n) * x) xhb
      grind only
    replace c : k1 ≠ k2 := by grind only
    let kmin := min k1 k2
    by_cases tdk1 : 2 ∣ kmin
    · exists kmin; refine ⟨tdk1, ?_⟩
      grind only [= Finset.nonempty_def, = min_def]
    exists kmin + 1; refine ⟨by grind only, ?_⟩
    simp only [Finset.mem_Icc]; and_intros
    · grind only [= Finset.mem_Icc, = Finset.nonempty_def, usr Nat.pow_pos, = min_def]
    · rcases Nat.lt_or_gt_of_ne c with c | c
      · exact calc 2 ^ padicValNat 2 n * (kmin + 1)
          _ = 2 ^ padicValNat 2 n * (k1 + 1) := by rw[show kmin = k1 from min_eq_left_of_lt c]
          _ ≤ 2 ^ padicValNat 2 n * k2 := Nat.mul_le_mul_left (2 ^ padicValNat 2 n) c
          _ = y := by rw[this, ←kh2]
          _ ≤ b := by simp only [Finset.mem_Icc] at yha; exact yha.2
      · exact calc 2 ^ padicValNat 2 n * (kmin + 1)
          _ = 2 ^ padicValNat 2 n * (k2 + 1) := by rw[show kmin = k2 from min_eq_right_of_lt c]
          _ ≤ 2 ^ padicValNat 2 n * k1 := Nat.mul_le_mul_left (2 ^ padicValNat 2 n) c
          _ = n := by symm; exact kh1
          _ ≤ b := by simp only [Finset.mem_Icc] at nh; exact nh.1.2
