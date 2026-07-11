import Mathlib.RingTheory.Coprime.Basic

lemma claim1 (n : ℤ) (a b : ℕ) (h : n ≥ 2 ∧ a > 0) (hd : n ^ a - 1 ∣ n ^ b - 1) : a ∣ b := by
  have oln : 1 < n := by grind
  induction b using Nat.strong_induction_on; case h b ih;
  by_cases bz : b = 0
  · subst bz; simp
  have : n^b-1 > 0 := by
    suffices n^b > n^0 by grind
    exact Int.pow_lt_pow_of_lt oln (by grind)
  replace := Int.le_of_dvd this hd
  replace : a ≤ b := by
    by_contra _; have := calc n^b
      _ < n^a := by apply Int.pow_lt_pow_of_lt oln; grind
      _ ≤ n^b := by grind
    grind
  have := calc n^a-1
    _ ∣ (n^b-1)-n^(b-a)*(n^a-1) := Int.dvd_sub hd (by apply Int.dvd_mul_left)
    _ = n^(b-a)-1 := by grind[Int.pow_add, show b-a+a = b by grind]
  specialize ih (b-a) (by grind) this
  replace := Nat.dvd_add_self_right.mpr ih
  convert this; grind

theorem POTD_2510 (k l : ℕ) (n m : ℤ) (ha : n ≥ 2 ∧ m > 0 ∧ k > 0 ∧ l > 0)
    (hb : n ^ k + m * n ^ l + 1 ∣ n ^ (k + l) - 1) :
    (m = 1 ∧ l = 2*k) ∨ (l ∣ k ∧ m * (n^l - 1) = n^(k-l) - 1) := by
  by_cases 2*k ≤ l
  · have star := calc n^k+m*n^l+1
      _ ∣ n^k*(n^k+m*n^l+1)-m*(n^(k+l)-1) := by
        refine Int.dvd_sub ?_ ?_ <;> apply Int.dvd_mul_of_dvd_right
        · apply Int.dvd_refl
        · assumption
      _ = n^(2*k)+n^k+m := by grind only [Int.pow_add n k k]
    apply Int.le_of_dvd at star; case bpos =>
      refine Int.add_pos ?_ ha.right.left
      refine Int.add_pos ?_ ?_ <;> apply Int.pow_pos (by grind)
    replace := calc n^(2*k)*(m-1)
      _ ≤ n^(2*k)*(m*n^(l-2*k)-1) := by
        refine Int.mul_le_mul_of_nonneg_left ?_ ?_
        · apply Int.sub_le_sub_right ?_
          nth_rewrite 1 [show m = m*1 by simp]
          refine Int.mul_le_mul_of_nonneg_left ?_ (by grind)
          apply Int.pow_pos (by grind)
        · exact Int.pow_nonneg (by grind)
      _ = m*n^l-n^(2*k) := by grind only [pow_add n (l-2*k) (2*k)]
      _ ≤ m-1 := by lia
    replace : m = 1 := by
      by_contra _; nth_rewrite 2 [show m-1 = 1*(m-1) by simp] at this
      replace := Int.le_of_mul_le_mul_right this (by grind)
      have : n^(2*k) > n^0 := by refine Int.pow_lt_pow_of_lt ?_ ?_ <;> grind
      grind
    subst this; left; simp only [true_and]
    by_contra _;
    simp only [one_mul, add_le_add_iff_right] at star
    suffices n^l > n^(2*k) from by grind
    apply Int.pow_lt_pow_of_lt (by grind)
    grind
  by_cases l > k
  · have := calc n^k+m*n^l+1
      _ ∣ (n^(k+l)-1)+(n^k+m*n^l+1) := Int.dvd_add hb (Int.dvd_refl _)
      _ = n^k*(n^l+1+m*n^(l-k)) := by
        have : n^l = n^(l-k)*n^k := by rw[←Int.pow_add]; grind;; grind
    apply IsCoprime.dvd_of_dvd_mul_left at this; case H1 =>
      obtain ⟨j, hj⟩ : n^k ∣ n^k+m*n^l := by
        refine Int.dvd_add (Int.dvd_refl (n^k)) ?_
        refine Int.dvd_mul_of_dvd_right ?_
        exact pow_dvd_pow n (by grind)
      rw[hj]; exact IsCoprime.mul_add_left_left_iff.mpr isCoprime_one_left
    apply Int.le_of_dvd at this; case bpos =>
      refine Int.add_pos ?_ ?_
      · refine Int.add_pos ?_ Int.one_pos
        apply Int.pow_pos (by grind)
      · refine Int.mul_pos ha.right.left ?_
        apply Int.pow_pos (by grind)
    replace : (n^(2*k-l)+(m-1)*n^k)*n^(l-k) ≤ m*n^(l-k) := by
      rw[right_distrib, mul_assoc, ←pow_add, ←pow_add]; grind
    apply Int.le_of_mul_le_mul_right at this
    specialize this (Int.pow_pos (by grind))
    replace := calc
      1 ≥ n^(2*k-l) + (m-1) * (n^k-1) := by lia
      _ ≥ n^(2*k-l) := by
        refine Int.le_add_of_nonneg_right ?_
        refine Int.mul_nonneg (by grind) ?_
        suffices 0 < n^k from by grind
        apply Int.pow_pos (by grind)
      _ > n^0 := by apply Int.pow_lt_pow_of_lt ?_ ?_ <;> grind
      _ = 1 := by simp
    contradiction
  suffices m*(n^l-1)=n^(k-l)-1 by
    right; refine ⟨?_, this⟩
    replace := claim1 _ _ _ ⟨ha.1, ha.2.2.2⟩ (Dvd.intro_left m this)
    replace := Nat.dvd_add this (Nat.dvd_refl l)
    convert this; grind
  apply le_antisymm
  · have := calc n^k+m*n^l+1
      _ ∣ (n^(k+l)-1)+(n^k+m*n^l+1) := Int.dvd_add hb (Int.dvd_refl _)
      _ = n^l*(n^(k-l)+n^k+m) := by
        have : n^k = n^(k-l)*n^l := by rw[←Int.pow_add]; grind;; grind
    apply IsCoprime.dvd_of_dvd_mul_left at this; case H1 =>
      obtain ⟨j, hj⟩ : n^l ∣ n^k+m*n^l := by
        refine Int.dvd_add (pow_dvd_pow n (by grind)) ?_
        apply Int.dvd_mul_of_dvd_right; apply Int.dvd_refl
      rw[hj]; exact IsCoprime.mul_add_left_left_iff.mpr isCoprime_one_left
    apply Int.le_of_dvd at this; case bpos =>
      refine Int.add_pos ?_ (by grind)
      refine Int.add_pos ?_ ?_ <;> exact Int.pow_pos (by grind)
    lia
  · have := calc n^k+m*n^l+1
      _ ∣ n^l*(n^k+m*n^l+1)-(n^(k+l)-1) := by
        refine Int.dvd_sub ?_ (by assumption)
        apply Int.dvd_mul_of_dvd_right; apply Int.dvd_refl
      _ = m*n^l*n^l+n^l+1 := by lia
    apply Int.le_of_dvd at this; case bpos =>
      iterate 2 apply Int.add_pos;; iterate 2 apply Int.mul_pos
      case ha.ha.ha.ha | hb => grind
      iterate 3 exact Int.pow_pos (by grind)
    rw[show n^k = n^(k-l)*n^l by symm; exact pow_sub_mul_pow n (by grind)] at this
    replace : n^l*(n^(k-l) + m) ≤ n^l*(m*n^l+1) := by lia
    apply Int.le_of_mul_le_mul_left at this
    specialize this (Int.pow_pos (by grind))
    lia
