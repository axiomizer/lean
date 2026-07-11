import Mathlib

lemma l₁ (a : PNat → PNat) (h : ∀ n : PNat, ∃ k : ℤ, k^n.val = ∏ i ∈ Finset.Icc 1 n, a i) :
    ∀ n : PNat, ∃ k : ℕ, k ≠ 0 ∧ k^n.val = ∏ i ∈ Finset.Icc 1 n, a i := by
  intro n
  let ⟨kInt, khInt⟩ := h n
  have kIntPowPos : 0 < kInt^n.val := by
    have : (∏ i ∈ Finset.Icc 1 n, a i).val > 0 := by apply PNat.pos
    have := Int.natCast_pos.mpr this
    exact khInt ▸ this
  let k := kInt.natAbs
  have knz : k ≠ 0 := by
    by_contra kz
    have := (Int.natAbs_eq_zero.mp kz) ▸ kIntPowPos
    simp at this
  have finnick : ((k^n.val : ℕ) : ℤ) = (k^n.val : ℤ) := Int.natCast_pow k ↑n
  apply Or.elim (em (kInt ≤ 0))
  · intro klez
    apply Or.elim (em (Even n.val))
    · intro heven
      have := calc (k^n.val : ℤ)
        _ = (-kInt)^n.val             := by rw[Int.ofNat_natAbs_of_nonpos klez]
        _ = kInt^n.val                := Even.neg_pow heven kInt
      have := finnick ▸ khInt ▸ this
      exact ⟨k, ⟨knz, Int.ofNat.inj this⟩⟩
    · intro hodd
      simp at hodd
      have : kInt^n.val ≤ 0 := (Odd.pow_nonpos_iff hodd).mpr klez
      have := (Int.not_lt_of_ge this) kIntPowPos
      contradiction
  · intro kgz
    simp at kgz
    have : (k^n.val : ℤ) = kInt^n.val := by rw[Int.natAbs_of_nonneg (Int.le_of_lt kgz)]
    have := finnick ▸ khInt ▸ this
    exact ⟨k, ⟨knz, Int.ofNat.inj this⟩⟩

lemma valuationBound (p n : ℕ) (h₁ : Fact (Nat.Prime p)) (h₂ : n ≤ 2025) :
    padicValNat p n ≤ 10 := by
  apply Or.elim (em (n = 0))
  · intro nz
    exact calc padicValNat p n
      _ = padicValNat p 0 := congrArg (padicValNat p) nz
      _ = 0               := padicValNat.zero
      _ ≤ 10              := Nat.zero_le 10
  · intro nnz
    let v := padicValNat p n
    by_contra vgt
    simp at vgt
    have : p^v ∣ n := pow_padicValNat_dvd
    have : p^v ∈ n.divisors := Nat.mem_divisors.mpr ⟨this, nnz⟩
    have ineq := Nat.divisor_le this
    have pineq : p ≥ 2 := Nat.Prime.two_le h₁.out
    have := calc 2^11
      _ ≤ p^11 := Nat.pow_le_pow_left pineq 11
      _ ≤ p^v  := Nat.pow_le_pow_of_le pineq vgt
      _ ≤ n    := ineq
      _ ≤ 2025 := h₂
    simp at this

lemma valBound₂ (p : ℕ) (n : PNat) (a : PNat → PNat)
    (h₁ : ∀ n : PNat, (a n).val ≤ 2025) (h₂ : Fact (Nat.Prime p)) :
    padicValNat p (∏ i ∈ Finset.Icc 1 n, (a i).val) ≤ n.val * 10 := by
  have induct (n : ℕ) :
      letI nP : PNat := ⟨n+1, Nat.zero_lt_succ n⟩
      padicValNat p (∏ i ∈ Finset.Icc 1 nP, (a i).val) ≤ (n+1) * 10 := by
    induction n
    case zero => simp; exact valuationBound p (a 1).val h₂ (h₁ 1)
    case succ n ih =>
      let np1 : PNat := ⟨n+1, Nat.zero_lt_succ n⟩
      let np2 : PNat := ⟨n+2, Nat.zero_lt_succ (n + 1)⟩
      have s₁ : np2 ∉ Finset.Icc 1 np1 := by
        simp
        suffices suff : n+1 < n+2 from (PNat.coe_lt_coe np1 np2).mp suff
        simp
      have s₂ : insert np2 (Finset.Icc 1 np1) = Finset.Icc 1 np2 := by
        ext a
        apply Iff.intro
        · intro ain; simp at ain; simp
          apply Or.elim ain
          · intro ain₁; exact le_of_eq ain₁
          · intro ain₂
            suffices a.val ≤ np2.val from this
            exact calc a.val
              _ ≤ n+1     := ain₂
              _ ≤ n+2     := by simp
              _ = np2.val := rfl
        · intro aout
          simp at aout; simp
          apply Or.elim (em (a = np2))
          · intro aout₁; exact Or.inl aout₁
          · intro aout₂
            apply Or.inr
            suffices a.val ≤ np1.val from this
            have : a < np2 := Std.lt_of_le_of_ne aout aout₂
            exact Nat.le_sub_one_of_lt this
      have : ∏ i ∈ insert np2 (Finset.Icc 1 np1), (a i).val =
        (a np2) * (∏ i ∈ Finset.Icc 1 np1, (a i).val) := Finset.prod_insert s₁
      rw[s₂] at this
      have := congrArg (padicValNat p) this
      rw[this]
      have : padicValNat p (↑(a np2) * ∏ i ∈ Finset.Icc 1 np1, ↑(a i)) =
          (padicValNat p ↑(a np2)) + (padicValNat p (∏ i ∈ Finset.Icc 1 np1, ↑(a i))) := by
        refine padicValNat.mul ?_ ?_
        · exact PNat.ne_zero (a np2)
        · refine Finset.prod_ne_zero_iff.mpr ?_
          intro a1 _
          exact PNat.ne_zero (a a1)
      rw[this]
      suffices padicValNat p ↑(a np2) + ((n + 1) * 10) ≤ (n + 1 + 1) * 10 by
        exact add_le_of_add_le_left this ih
      rw[Nat.add_mul (n+1) 1 10]
      rw[Nat.add_comm ((n+1)*10) (1*10)]
      simp
      exact valuationBound p (a np2).val h₂ (h₁ np2)
  have ii := induct (n.val - 1)
  have m1p1 : n.val - 1 + 1 = n.val := PNat.natPred_add_one n
  simp[m1p1] at ii
  suffices suff : ∏ i ∈ Finset.Icc 1 ⟨↑n, n.property⟩, (a i).val =
      ∏ i ∈ Finset.Icc 1 n, (a i).val by rw[suff] at ii; exact ii
  exact rfl

theorem POTD2411 (a : PNat → PNat)
    (h₁ : ∀ n : PNat, (a n).val ≤ 2025)
    (h₂ : ∀ n : PNat, ∃ k : ℤ, k^n.val = ∏ i ∈ Finset.Icc 1 n, a i) :
    ∃ c N : PNat, ∀ n : PNat, n.val ≥ N.val → a n = c := by
  have t₂ := l₁ a h₂; clear h₂
  let N : ℕ := 11
  let NP : PNat := ⟨N, Nat.zero_lt_succ 10⟩
  let ⟨k, kh⟩ := t₂ ⟨N-1, Nat.zero_lt_succ 9⟩

  have step (npnm1 : PNat) :
      letI npn : PNat := ⟨npnm1.val + 1, Nat.zero_lt_succ npnm1.val⟩
      (a npn) * (∏ i ∈ Finset.Icc 1 npnm1, a i) = ∏ i ∈ Finset.Icc 1 npn, a i := by
    let npn : PNat := ⟨npnm1.val + 1, Nat.zero_lt_succ npnm1.val⟩
    have s₁ : npn ∉ Finset.Icc 1 npnm1 := by
      simp
      refine (PNat.coe_lt_coe npnm1 npn).mp ?_
      have : npn.val = npnm1.val + 1 := rfl
      rw[this]
      simp
    have s₂ : insert npn (Finset.Icc 1 npnm1) = Finset.Icc 1 npn := by
      ext a
      apply Iff.intro
      · intro ain; simp at ain; simp
        apply Or.elim ain
        · intro ain₁; exact le_of_eq ain₁
        · intro ain₂
          suffices a.val ≤ npn.val from this
          exact calc a.val
            _ ≤ npnm1.val := ain₂
            _ ≤ npn.val   := Nat.le_succ npnm1.val
      · intro aout
        simp at aout; simp
        apply Or.elim (em (a = npn))
        · intro aout₁; exact Or.inl aout₁
        · intro aout₂
          apply Or.inr
          suffices a.val ≤ npnm1.val from this
          have : a < npn := Std.lt_of_le_of_ne aout aout₂
          exact Nat.le_sub_one_of_lt this
    have : ∏ i ∈ insert npn (Finset.Icc 1 npnm1), a i =
      (a npn) * (∏ i ∈ Finset.Icc 1 npnm1, a i) := Finset.prod_insert s₁
    rw[s₂] at this
    exact Eq.symm this

  have constValInProd (p : ℕ) (hprime : Fact (Nat.Prime p)) :
      ∃ r : ℕ, ∀ n : ℕ,
      letI gr : 0 < N+n-1 := by simp; refine Nat.lt_add_right n ?_; exact Nat.one_lt_succ_succ 9
      padicValNat p (∏ i ∈ Finset.Icc 1 ⟨N+n-1, gr⟩, a i) = (N+n-1) * r := by
    let r := padicValNat p k; exists r
    have : padicValNat p (k^(N-1)) = (N-1) * r := padicValNat.pow (N-1) kh.left
    intro n; induction n
    case zero => exact (congrArg (padicValNat p) kh.right) ▸ this
    case succ n ih =>
      clear this; simp
      let npn : PNat := ⟨N+n, Nat.pos_of_neZero (N + n)⟩
      have : 0 < N+n-1 := by
        refine Nat.sub_pos_of_lt ?_
        refine Nat.lt_add_right n ?_
        exact Nat.one_lt_succ_succ 9
      let npnm1 : PNat := ⟨N+n-1, this⟩

      have stepy := step npnm1
      have : ⟨npnm1.val + 1, Nat.zero_lt_succ npnm1.val⟩ = npn := PNat.natPred_inj.mp rfl
      rw[this] at stepy

      have := calc (a npn).val * (∏ i ∈ Finset.Icc 1 npnm1, a i).val
        _ = ((a npn) * (∏ i ∈ Finset.Icc 1 npnm1, a i)).val := rfl
        _ = (∏ i ∈ Finset.Icc 1 npn, a i).val               := congrArg PNat.val stepy
        _ = ∏ i ∈ Finset.Icc 1 npn, (a i).val               := by rw[Finset.PNat.coe_prod]
      have := congrArg (padicValNat p) this
      have line₃ : (padicValNat p (a npn).val) +
          padicValNat p (∏ i ∈ Finset.Icc 1 npnm1, a i).val =
          padicValNat p (∏ i ∈ Finset.Icc 1 npn, (a i).val) := by
        have split : padicValNat p ((a npn).val * (∏ i ∈ Finset.Icc 1 npnm1, a i).val) =
            (padicValNat p (a npn).val) + padicValNat p (∏ i ∈ Finset.Icc 1 npnm1, a i).val := by
          refine padicValNat.mul ?_ ?_ <;> apply PNat.ne_zero
        exact split ▸ this
      rw[Finset.PNat.coe_prod, ih] at line₃
      let ⟨k₂, k₂h⟩ := t₂ npn
      let s := padicValNat p k₂
      have : padicValNat p (∏ i ∈ Finset.Icc 1 npn, (a i).val) = (N+n) * s := by
        rw[←Finset.PNat.coe_prod, ←k₂h.right]
        rw[padicValNat.pow npn.val k₂h.left]
        rfl
      rw[this] at line₃; rw[this]; simp
      clear this stepy k₂h; clear this; clear this
      have sgeqr : s ≥ r := by
        by_contra sr; simp at sr
        suffices ineq : (N+n-1)*r > (N+n)*(r-1) by
          have := calc padicValNat p (a npn).val + (N+n-1)*r
            _ ≥ (N+n-1)*r   := by simp
            _ > (N+n)*(r-1) := ineq
            _ ≥ (N+n)*s     := Nat.mul_le_mul_left (N + n) (Nat.le_sub_one_of_lt sr)
          have := Ne.symm (Nat.ne_of_lt this)
          exact this line₃
        rw[Nat.mul_sub, Nat.sub_mul]; simp
        suffices suff : (N + n) * r + r < (N + n) * r + (N + n) by
          have thing : (N+n) ≤ (N+n)*r := by
            have : 0 < r := by exact Nat.zero_lt_of_lt sr
            exact Nat.le_mul_of_pos_right (N + n) this
          have : (N + n) * r + r - (N+n) < (N+n)*r := by
            refine Nat.sub_lt_right_of_lt_add ?_ suff
            suffices N+n ≤ (N+n)*r from Nat.le_add_right_of_le this
            exact thing
          have thing₂ : (N + n) * r + r - (N + n) = (N + n) * r - (N + n) + r :=
            Nat.sub_add_comm thing
          rw[thing₂] at this
          exact Nat.lt_sub_of_add_lt this
        simp
        suffices r < N from Nat.lt_add_right n this
        have := valBound₂ p npnm1 a h₁ hprime
        rw[ih] at this
        have : r ≤ 10 := Nat.le_of_mul_le_mul_left this npnm1.property
        exact Nat.lt_succ_of_le this
      have sleqr : s ≤ r := by
        by_contra sr; simp at sr
        suffices suff : padicValNat p (a npn).val + (N+n-1)*r < (N+n) * (r+1) by
          have := Nat.mul_le_mul_left (N + n) sr
          have := Nat.lt_of_lt_of_le suff this
          have := Nat.ne_of_lt this
          exact this line₃
        suffices suff : 10 + (N+n-1)*r < (N+n) * (r+1) by
          have := valuationBound p (a npn) hprime (h₁ npn)
          exact add_lt_of_add_lt_right suff this
        simp[Nat.sub_mul, Nat.mul_add]
        rw[Nat.add_comm]
        have : (N + n) * r - r + 10 = (N + n) * r + 10 - r := by
          refine Eq.symm (Nat.sub_add_comm ?_)
          refine Nat.le_mul_of_pos_left r ?_
          exact Nat.pos_of_neZero (N + n)
        rw[this]
        suffices (N + n) * r + 10 < (N + n) * r + (N + n) + r by
          refine Nat.sub_lt_of_lt ?_
          simp
          refine Nat.lt_add_right n ?_
          exact Nat.lt_add_one 10
        simp[Nat.add_assoc]
        refine Nat.lt_add_right (n + r) ?_
        exact Nat.lt_add_one 10
      exact Nat.le_antisymm sleqr sgeqr
  have constVal (p : ℕ) (hprime : Fact (Nat.Prime p)) : ∃ r : ℕ, ∀ n : ℕ,
      letI npn : PNat := ⟨N+n, Nat.pos_of_neZero (N + n)⟩
      padicValNat p (a npn) = r := by
    let ⟨r, rh⟩ := constValInProd p hprime
    exists r; intro n
    let npn : PNat := ⟨N+n, Nat.pos_of_neZero (N + n)⟩
    have : 0 < N+n-1 := by
      refine Nat.sub_pos_of_lt ?_
      refine Nat.lt_add_right n ?_
      exact Nat.one_lt_succ_succ 9
    let npnm1 : PNat := ⟨N+n-1, this⟩
    have stepy := step npnm1
    have : ⟨npnm1.val + 1, Nat.zero_lt_succ npnm1.val⟩ = npn := PNat.natPred_inj.mp rfl
    rw[this] at stepy
    have := calc (a npn).val * (∏ i ∈ Finset.Icc 1 npnm1, a i).val
      _ = ((a npn) * (∏ i ∈ Finset.Icc 1 npnm1, a i)).val := rfl
      _ = (∏ i ∈ Finset.Icc 1 npn, a i).val               := congrArg PNat.val stepy
      _ = ∏ i ∈ Finset.Icc 1 npn, (a i).val               := by rw[Finset.PNat.coe_prod]
    have := congrArg (padicValNat p) this
    have line₃ : (padicValNat p (a npn).val) +
        padicValNat p (∏ i ∈ Finset.Icc 1 npnm1, a i).val =
        padicValNat p (∏ i ∈ Finset.Icc 1 npn, (a i).val) := by
      have split : padicValNat p ((a npn).val * (∏ i ∈ Finset.Icc 1 npnm1, a i).val) =
          (padicValNat p (a npn).val) + padicValNat p (∏ i ∈ Finset.Icc 1 npnm1, a i).val := by
        refine padicValNat.mul ?_ ?_ <;> apply PNat.ne_zero
      exact split ▸ this
    rw[Finset.PNat.coe_prod] at line₃
    have := rh n
    rw[this] at line₃
    have := rh (n+1)
    simp at this
    rw[this] at line₃
    simp[Nat.sub_mul (N+n) 1 r] at line₃
    have : r ≤ (N+n)*r := by
      suffices 1 ≤ N+n from Nat.le_mul_of_pos_left r this
      exact NeZero.one_le
    rw[←Nat.add_sub_assoc this] at line₃
    have : r ≤ padicValNat p (a npn) + (N+n)*r := Nat.le_add_left_of_le this
    have eqr := (Nat.sub_eq_iff_eq_add' this).mp line₃
    simp at eqr
    exact eqr
  have const : ∃ c : ℕ, ∀ n : ℕ,
      letI npn : PNat := ⟨N+n, Nat.pos_of_neZero (N + n)⟩
      a npn = c := by
    exists (a NP); intro n
    let npn : PNat := ⟨N+n, Nat.pos_of_neZero (N + n)⟩
    have peq : ∀ p : ℕ, Nat.Prime p → padicValNat p (a npn) = padicValNat p (a NP) := by
      intro p pp
      have : Fact (Nat.Prime p) := by exact { out := pp }
      let ⟨r, rh⟩ := constVal p this
      exact (rh 0) ▸ (rh n)
    have ha : (a npn).val ≠ 0 := PNat.ne_zero (a npn)
    have hb : (a NP).val ≠ 0 := PNat.ne_zero (a NP)
    exact (Nat.eq_iff_prime_padicValNat_eq (a npn).val (a NP).val ha hb).mpr peq
  let ⟨c, ch⟩ := const
  have : 0 < c := by
    have := ch 0
    rw[←this]
    simp[PNat.pos]
  exists ⟨c, this⟩; exists ⟨N, Nat.zero_lt_succ 10⟩
  intro n nh
  have := ch (n - N)
  suffices (a n).val = c from PNat.eq this
  rw[←this]
  refine PNat.coe_inj.mpr ?_
  refine congrArg a ?_
  have : N + (n.val - N) = n.val := Nat.add_sub_of_le nh
  exact PNat.eq (Eq.symm this)
