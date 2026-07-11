import Mathlib

lemma const {b : ℤ → ℤ} (bound : ∀ k, k > 0 → 0 < b k) (noninc : ∀ k, k > 1 → b k ≤ b (k - 1)) :
    ∃ N l, ∀ k, k ≥ N → b k = l := by
  replace noninc (j k : ℤ) : j > 0 → k > j → b j ≥ b k := by
    induction k using Int.inductionOn' (b := j) with | zero | pred k kh ih | succ k kh ih
    · intro _ c
      have : ¬ j > j := Eq.not_gt rfl
      contradiction
    · intro _ c; exfalso; grind
    · intro jh1 jh2
      have : k+1 > 1 := by grind
      have := noninc (k+1) this; simp at this
      suffices suff : b j ≥ b k from by grind
      by_cases kj : k = j
      · rw[kj]
      replace kj : j < k := by
        replace kj : j ≠ k := by symm; assumption
        exact Std.lt_of_le_of_ne kh kj
      specialize ih jh1 kj; assumption
  by_contra cont; simp at cont
  have (M : ℤ) : (∃ k, k > 0 ∧ b k = M) → False := by
    induction M using Int.strongRec (m := 0) with | lt M ih | ge M Mh ih
    · intro ⟨c, ⟨ch1, ch2⟩⟩
      have := calc
        0 < b c := bound c ch1
        _ < 0   := ch2 ▸ ih
      contradiction
    · intro ⟨k, ⟨kh1, kh2⟩⟩
      let ⟨k2, k2h1, k2h2⟩ := cont k M
      replace k2h1 : k < k2 := by
        by_cases cas : k = k2
        · rw[←cas] at k2h2
          contradiction
        exact Std.lt_of_le_of_ne k2h1 cas
      have := noninc k k2 kh1 k2h1
      rw[kh2] at this
      replace : M > b k2 := Std.lt_of_le_of_ne this k2h2
      specialize ih (b k2) this ⟨k2, ?_⟩
      · and_intros
        · exact Int.lt_trans kh1 k2h1
        · rfl
      assumption
  exact this (b 1) ⟨1, ⟨Int.one_pos, rfl⟩⟩

theorem USAMO_2007_1 (n : ℤ) (hn : n > 0) (a : ℤ → ℤ) (ha₁ : a 1 = n)
    (ha₂ : ∀ k, k > 1 → 0 ≤ a k ∧ a k ≤ k - 1 ∧ k ∣ ∑ i ∈ Finset.Icc 1 k, a i) :
    ∃ N l, ∀ k, k > N → a k = l := by
  have ha₃ : ∀ k : ℤ, k > 0 → 0 ≤ a k ∧ k ∣ ∑ i ∈ Finset.Icc 1 k, a i := by
    intro k kh
    by_cases ko : k = 1
    · simp[ko, ha₁]; grind
    replace ko : k > 1 := by grind
    let t := ha₂ k ko; exact ⟨t.left, t.right.right⟩
  replace ha₂ : ∀ k, k > 1 → a k ≤ k - 1 := by
    intro k kh; exact (ha₂ k kh).right.left
  let b := fun k : ℤ => (∑ i ∈ Finset.Icc 1 k, a i) / k
  have hb : ∀ k, k > 0 → k * b k = ∑ i ∈ Finset.Icc 1 k, a i := by
    intro k kh; unfold b
    let ⟨_, ⟨j, jh⟩⟩ := ha₃ k kh
    rw[jh]; simp; by_cases c : k = 0
    · right; assumption
    · left; simp[c]

  have b_bound : ∀ k, k > 0 → 0 < b k := by
    intro k kh; unfold b
    suffices suff : 0 < (∑ i ∈ Finset.Icc 1 k, a i) from by
      let ⟨_, ⟨j, jh⟩⟩ := ha₃ k kh
      rw[jh] at suff
      exact calc
        0 < j := Int.pos_of_mul_pos_right suff kh
        _ = (∑ i ∈ Finset.Icc 1 k, a i) / k := by
          rw[jh]
          refine Int.eq_ediv_of_mul_eq_right ?_ rfl
          exact Ne.symm (Int.ne_of_lt kh)
    refine Finset.sum_pos' ?_ ?_
    · intro i ih; simp at ih
      exact (ha₃ i ih.left).left
    · exists 1
      and_intros
      · exact Finset.left_mem_Icc.mpr kh
      · simp[ha₁, hn]

  have fineq (k : ℤ) (h : k > 0) :
      ∑ i ∈ Finset.Icc 1 k, a i = a k + (∑ i ∈ Finset.Icc 1 (k-1), a i) := by
    exact calc ∑ i ∈ Finset.Icc 1 k, a i
      _ = ∑ i ∈ insert k (Finset.Icc 1 (k-1)), a i := by
        have : insert k (Finset.Icc 1 (k-1)) = Finset.Icc 1 k := by
          exact Finset.insert_Icc_sub_one_right_eq_Icc h
        exact congrFun (congrArg Finset.sum (id (Eq.symm this))) fun i ↦ a i
      _ = a k + (∑ i ∈ Finset.Icc 1 (k-1), a i) := by
          have : k ∉ Finset.Icc 1 (k-1) := by rw[Finset.mem_Icc]; simp
          exact Finset.sum_insert this

  have b_noninc : ∀ k, k > 1 → b k ≤ b (k - 1) := by
    intro k kh
    have kh₂ : k > 0 := by grind
    have := calc (k-1) * b k
      _ < k * b k := by
        suffices suff : k - 1 < k from by
          refine Int.mul_lt_mul_of_pos_right suff ?_
          refine b_bound k ?_
          grind
        simp
      _ = ∑ i ∈ Finset.Icc 1 k, a i := hb k kh₂
      _ = a k + (∑ i ∈ Finset.Icc 1 (k-1), a i) := fineq k kh₂
      _ = (k-1) * b (k-1) + a k := by
        nth_rewrite 2 [add_comm]
        have : k-1 > 0 := by grind
        rw[hb (k-1) this]
      _ ≤ (k-1) * b (k-1) + (k - 1) := by simp[Int.add_le_add_left (ha₂ k kh)]
      _ = (k-1) * (b (k-1) + 1) := by linarith
    replace : b k < b (k-1) + 1 := by
      refine (Int.mul_lt_mul_left ?_).mp this
      simp[kh]
    exact (Int.add_le_add_iff_right 1).mp this

  let ⟨N, l, ch⟩ := const b_bound b_noninc
  exists (if N ≥ 1 then N else 1), l; intro k kh
  have : k > 1 := by
    by_cases c : N ≥ 1 <;> simp[c] at kh <;> grind
  have kh₁ : k > 0 := by grind
  have kh₂ : k - 1 > 0 := by grind
  exact calc a k
    _ = (∑ i ∈ Finset.Icc 1 k, a i) - (∑ i ∈ Finset.Icc 1 (k-1), a i) := by
      simp[fineq k kh₁]
    _ = k * b k - (k-1) * b (k-1) := by
      rw[hb k kh₁, hb (k-1) kh₂]
    _ = k * l - (k-1) * l := by
      have kh₁ : k ≥ N := by
        by_cases c : N ≥ 1 <;> simp[c] at kh <;> grind
      have kh₂ : k - 1 ≥ N := by
        by_cases c : N ≥ 1 <;> simp[c] at kh <;> grind
      rw[ch k kh₁, ch (k-1) kh₂]
    _ = l := by linarith
