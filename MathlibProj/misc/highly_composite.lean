import Mathlib.Data.Int.Init
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open ArithmeticFunction.sigma

def highly_composite (n : ℕ) := ∀ m, m < n → σ 0 n > σ 0 m
def sigmul : (σ 0).IsMultiplicative := ArithmeticFunction.isMultiplicative_sigma

example : ¬ highly_composite 5 := by
  by_contra c
  replace c := c 4 (Nat.lt_add_one 4)
  have : σ 0 4 = 3 := rfl; rw[this] at c
  have : σ 0 5 = 2 := rfl; rw[this] at c
  have : 0 > 1 := by exact Nat.lt_of_add_lt_add_left c
  exact Nat.not_succ_le_zero 1 this

example : highly_composite 6 := by
  intro m mh
  have : σ 0 6 = 4 := rfl
  rw[this]
  cases m with | zero | succ m
  · simp
  cases m with | zero | succ m
  · simp
  cases m with | zero | succ m
  · have : σ 0 2 = 2 := rfl
    simp[this]
  cases m with | zero | succ m
  · have : σ 0 3 = 2 := rfl
    simp[this]
  cases m with | zero | succ m
  · have : σ 0 4 = 3 := rfl
    simp[this]
  cases m with | zero | succ m
  · have : σ 0 5 = 2 := rfl
    simp[this]
  contradiction

lemma p_cop {n p k : ℕ} (hp : Nat.Prime p) (nnz : n ≠ 0)
    (kh : n = p ^ (padicValNat p n) * k) : p.Coprime k := by
  have := (fact_iff.mpr hp)
  by_cases ch : p ∣ k
  · by_contra
    let ⟨j, jh⟩ := ch
    rw[jh, ←mul_assoc] at kh
    have : p ^ (padicValNat p n + 1) ∣ n := ⟨j, kh⟩
    have := (padicValNat_dvd_iff_le nnz).mp this
    simp at this
  · exact (Nat.Prime.coprime_iff_not_dvd hp).mpr ch

lemma pq_split {n p q : ℕ} (nnz : n ≠ 0) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    ∃ k, n = p ^ (padicValNat p n) * q ^ (padicValNat q n) * k ∧ p.Coprime k ∧ q.Coprime k := by
  have h1 : p ^ padicValNat p n ∣ n := pow_padicValNat_dvd
  have h2 : q ^ padicValNat q n ∣ n := pow_padicValNat_dvd
  have h3 := Nat.coprime_pow_primes (padicValNat p n) (padicValNat q n) hp hq hpq
  let ⟨k, kh⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd h3 h1 h2
  exists k; refine ⟨kh, ?_, ?_⟩
  · have : p.Coprime (q ^ padicValNat q n * k) := by
      refine p_cop hp nnz ?_
      nth_rewrite 1 [kh]; linarith
    exact Nat.Coprime.coprime_mul_left_right this
  · have : q.Coprime (p ^ padicValNat p n * k) := by
      refine p_cop hq nnz ?_
      nth_rewrite 1 [kh]; linarith
    exact Nat.Coprime.coprime_mul_left_right this

lemma pow_2_5 {n p : ℕ} (hpa : Nat.Prime p) (hpb : p > 3) (hpc : p ∣ n)
    (h : highly_composite n) : 4 ∣ n := by
  have := (fact_iff.mpr hpa)
  let ν₂ := padicValNat 2 n; let νp := padicValNat p n
  by_cases nnz : n = 0
  · simp[nnz]
  let ⟨j, jha, jhb, jhc⟩ := pq_split nnz Nat.prime_two hpa (by grind)
  have νpo : 1 ≤ νp := one_le_padicValNat_of_dvd nnz hpc
  specialize h (2^(ν₂+2) * p^(νp-1) * j) ?_
  · exact calc 2 ^ (ν₂ + 2) * p ^ (νp - 1) * j
      _ = 2^ν₂ * p ^ (νp - 1) * j * 2^2 := by rw[Nat.pow_add 2 ν₂ 2]; linarith
      _ < 2^ν₂ * p ^ (νp - 1) * j * p^1 := by
        refine Nat.mul_lt_mul_of_pos_left ?_ ?_
        · have : p ≠ 4 := by by_contra c; rw[c] at hpa; contradiction
          grind
        · simp; and_intros
          · refine Nat.pow_pos ?_
            exact Nat.zero_lt_of_lt hpb
          · by_contra c; simp at c; simp[c] at jha; contradiction
      _ = 2^ν₂ * p^(νp - 1 + 1) * j := by rw[Nat.pow_add p (νp-1) 1]; linarith
      _ = n := by
        rw[jha, Nat.sub_add_cancel νpo]
  have : Nat.Coprime (2 ^ (ν₂ + 2) * p ^ (νp - 1)) j := by
    refine Nat.Coprime.mul_left ?_ ?_
    · exact Nat.gcd_pow_left_of_gcd_eq_one jhb
    · exact Nat.gcd_pow_left_of_gcd_eq_one jhc
  rw[ArithmeticFunction.IsMultiplicative.map_mul_of_coprime sigmul this] at h
  have cop_2p : Nat.Coprime 2 p := by
    refine Odd.coprime_two_left ?_
    exact Nat.Prime.odd_of_ne_two hpa (by grind)
  replace : Nat.Coprime (2^(ν₂+2)) (p^(νp-1)) := Nat.pow_gcd_pow_of_gcd_eq_one cop_2p
  rw[ArithmeticFunction.IsMultiplicative.map_mul_of_coprime sigmul this] at h
  rw[ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two] at h
  rw[ArithmeticFunction.sigma_zero_apply_prime_pow hpa, Nat.sub_add_cancel νpo, jha] at h
  replace : Nat.Coprime (2^ν₂ * p^νp) j := by
    refine Nat.Coprime.mul_left ?_ ?_
    · exact Nat.gcd_pow_left_of_gcd_eq_one jhb
    · exact Nat.gcd_pow_left_of_gcd_eq_one jhc
  rw[ArithmeticFunction.IsMultiplicative.map_mul_of_coprime sigmul this] at h
  replace : Nat.Coprime (2^ν₂) (p^νp) := Nat.pow_gcd_pow_of_gcd_eq_one cop_2p
  rw[ArithmeticFunction.IsMultiplicative.map_mul_of_coprime sigmul this] at h
  rw[ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two] at h
  rw[ArithmeticFunction.sigma_zero_apply_prime_pow hpa] at h
  replace h : (ν₂ + 1) * (νp + 1) > (ν₂ + 2 + 1) * νp := Nat.lt_of_mul_lt_mul_right h
  replace h : ν₂ ≥ 2 * νp := by linarith
  replace h : ν₂ ≥ 2 := le_of_mul_le_of_one_le_left h νpo
  replace h : 2^2 ∣ n := (padicValNat_dvd_iff_le nnz).mpr h
  exact h

lemma dec_pow {n p q k : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h1 : p ≤ q) (h2 : q ^ k ∣ n) (h3 : highly_composite n) : p^k ∣ n := by
  let νp := padicValNat p n; let νq := padicValNat q n
  by_cases nnz : n = 0
  · simp[nnz]
  by_cases pnq : p = q
  · simp[pnq, h2]
  let ⟨j, jha, jhb, jhc⟩ := pq_split nnz hp hq pnq
  by_cases νpq : νp < νq
  · exfalso
    specialize h3 (p ^ νq * q ^ νp * j) ?_
    · rw[jha]
      refine Nat.mul_lt_mul_of_pos_right ?_ ?_
      · have := Nat.pow_sub_mul_pow p (Nat.le_of_succ_le νpq)
        rw[←this]
        replace := Nat.pow_sub_mul_pow q (Nat.le_of_succ_le νpq)
        rw[←this]
        suffices p^(νq-νp) < q^(νq-νp) from by
          replace : p^νp * q^νp * p^(νq-νp) < p^νp * q^νp * q^(νq-νp) := by
            refine Nat.mul_lt_mul_of_pos_left this ?_
            refine Nat.mul_pos ?_ ?_ <;> grind
          grind
        refine Nat.pow_lt_pow_left ?_ ?_ <;> grind
      · grind
    have := calc σ 0 n
      _ = (σ 0) (p ^ νp * q ^ νq) * (σ 0 j) := by
        rw[jha]
        refine ArithmeticFunction.IsMultiplicative.map_mul_of_coprime sigmul ?_
        · have cop1 : (p ^ νp).Coprime j := Nat.gcd_pow_left_of_gcd_eq_one jhb
          have cop2 : (q ^ νq).Coprime j := Nat.gcd_pow_left_of_gcd_eq_one jhc
          exact Nat.Coprime.mul_left cop1 cop2
      _ = (σ 0) (p ^ νp) * (σ 0) (q ^ νq) * (σ 0 j) := by
        suffices (σ 0) (p ^ νp * q ^ νq) = (σ 0) (p ^ νp) * (σ 0) (q ^ νq) from by grind
        refine ArithmeticFunction.IsMultiplicative.map_mul_of_coprime sigmul ?_
        · exact Nat.coprime_pow_primes νp νq hp hq pnq
      _ = (νp+1) * (νq+1) * (σ 0 j) := by
        rw[ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        rw[ArithmeticFunction.sigma_zero_apply_prime_pow hq]
      _ = (σ 0) (p ^ νq) * (σ 0) (q ^ νp) * (σ 0 j) := by
        rw[ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        rw[ArithmeticFunction.sigma_zero_apply_prime_pow hq]
        nth_rewrite 2 [mul_comm]; rfl
      _ = (σ 0) (p ^ νq * q ^ νp) * (σ 0 j) := by
        suffices (σ 0) (p ^ νq) * (σ 0) (q ^ νp) = (σ 0) (p ^ νq * q ^ νp) from by grind
        symm
        refine ArithmeticFunction.IsMultiplicative.map_mul_of_coprime sigmul ?_
        · exact Nat.coprime_pow_primes νq νp hp hq pnq
      _ = (σ 0) (p ^ νq * q ^ νp * j) := by
        symm
        refine ArithmeticFunction.IsMultiplicative.map_mul_of_coprime sigmul ?_
        · have cop1 : (p ^ νq).Coprime j := Nat.gcd_pow_left_of_gcd_eq_one jhb
          have cop2 : (q ^ νp).Coprime j := Nat.gcd_pow_left_of_gcd_eq_one jhc
          exact Nat.Coprime.mul_left cop1 cop2
      _ < σ 0 n := h3
    simp at this
  have := (fact_iff.mpr hp); have := (fact_iff.mpr hq);
  refine (padicValNat_dvd_iff_le nnz).mpr ?_
  simp at νpq; refine Nat.le_trans ?_ νpq
  exact (padicValNat_dvd_iff_le nnz).mp h2

theorem divisible_by_12 {n : ℕ} (h1 : n ≥ 12) (h2 : highly_composite n) : 12 ∣ n := by
  let ν₂ := padicValNat 2 n; let ν₃ := padicValNat 3 n
  have nnz := Nat.ne_zero_of_lt h1
  let ⟨k, kha, khb, khc⟩ := pq_split nnz Nat.prime_two Nat.prime_three (by simp)
  by_cases keo : k > 1
  · let ⟨r, rha, rhb⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by grind)
    have rbig : r > 4 := by
      cases r with | zero | succ r
      · contradiction
      cases r with | zero | succ r
      · contradiction
      cases r with | zero | succ r
      · simp at khb
        have : ¬ Odd k := by grind
        contradiction
      cases r with | zero | succ r
      · have := Nat.dvd_gcd (show 3 ∣ 3 by simp) rhb
        replace : 3 ∣ 1 := by grind
        contradiction
      cases r with | zero | succ r
      · contradiction
      simp
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 4 3 by rfl) ?_ ?_
    · refine pow_2_5 rha ?_ ?_ h2
      · grind
      · refine Nat.dvd_trans rhb ?_
        exists (2^ν₂ * 3^ν₃)
        linarith
    · rw[show 3=3^1 by simp]
      refine dec_pow Nat.prime_three rha (by grind) ?_ h2
      simp; refine Nat.dvd_trans rhb ?_
      exists (2^ν₂ * 3^ν₃)
      rw[kha]; linarith
  simp[show k = 1 by grind] at kha; clear khb khc keo
  by_cases hν₃ : ν₃ = 0
  · change padicValNat 3 n = 0 at hν₃
    simp[hν₃] at kha; clear hν₃
    have := calc 2^3
      _ < 12   := by simp
      _ ≤ 2^ν₂ := kha ▸ h1
    replace : 3 < ν₂ := (Nat.pow_lt_pow_iff_right (show 1 < 2 by simp)).mp this
    specialize h2 (2^(ν₂-2) * 3) ?_
    · exact calc 2^(ν₂-2) * 3
        _ < 2^(ν₂-2) * 2^2 := by
          refine Nat.mul_lt_mul_of_pos_left (by simp) ?_
          exact Nat.two_pow_pos (ν₂ - 2)
        _ = 2^(ν₂-2+2) := by rw[Nat.pow_add]
        _ = 2^ν₂ := by
          have : ν₂-2+2 = ν₂ := Nat.sub_add_cancel (Nat.le_of_add_left_le this)
          rw[this]
        _ = n := by rw[kha]
    have : Nat.Coprime (2^(ν₂-2)) 3 := Nat.gcd_pow_left_of_gcd_eq_one rfl
    rw[ArithmeticFunction.IsMultiplicative.map_mul_of_coprime sigmul this] at h2
    rw[kha, show 3 = 3^1 by simp] at h2
    rw[ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two] at h2
    rw[ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two] at h2
    rw[ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_three] at h2
    replace h2 : 3 < 3 := by grind
    contradiction
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 3 4 by rfl) ?_ ?_
  · rw[show 3 = 3^1 by simp]
    exact (padicValNat_dvd_iff_le nnz).mpr (by grind)
  rw[show 4 = 2^2 by simp]
  by_cases ν₃no : padicValNat 3 n = 1
  · simp[ν₃no] at kha
    rw[kha] at h1
    replace h1 : 2^2 ≤ 2 ^ padicValNat 2 n := by grind
    replace h1 := (Nat.pow_le_pow_iff_right (by simp)).mp h1
    exact (padicValNat_dvd_iff_le nnz).mpr h1
  replace hν₃ : ν₃ ≥ 2 := by grind
  clear ν₃no
  have : 3^2 ∣ n := (padicValNat_dvd_iff_le nnz).mpr hν₃
  exact dec_pow Nat.prime_two Nat.prime_three (by simp) this h2
