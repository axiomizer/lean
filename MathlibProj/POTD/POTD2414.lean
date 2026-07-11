import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open ArithmeticFunction.omega ArithmeticFunction.sigma

inductive Reachable : ℕ → ℕ → Prop
| τ {n}         : Reachable n (σ 0 n)
| σ {n}         : Reachable n (σ 1 n)
| φ {n}         : Reachable n n.totient
| rfl {n}       : Reachable n n
| trans {a b c} : Reachable a b → Reachable b c → Reachable a c

lemma padic_split {a p} (anz : a ≠ 0) (hp : Nat.Prime p) :
    ∃ k, a = p ^ (padicValNat p a) * k ∧ (p ^ (padicValNat p a)).Coprime k ∧ p.Coprime k := by
  have := (fact_iff.mpr hp)
  have : p ^ (padicValNat p a) ∣ a := pow_padicValNat_dvd
  let ⟨k, kh⟩ := this; exists k
  have : p.Coprime k := by
    by_cases ch : p ∣ k
    · by_contra
      let ⟨j, jh⟩ := ch
      rw[jh, ←mul_assoc] at kh
      have : p ^ (padicValNat p a + 1) ∣ a := ⟨j, kh⟩
      have := (padicValNat_dvd_iff_le anz).mp this
      simp at this
    · exact (Nat.Prime.coprime_iff_not_dvd hp).mpr ch
  exact ⟨kh, Nat.gcd_pow_left_of_gcd_eq_one this, this⟩

lemma tot₀ {p a} (hp : Nat.Prime p ∧ p ∣ a) : p - 1 ∣ a.totient := by
  by_cases anz : a = 0
  · rw[anz]; simp
  let ⟨k, prod, cop, _⟩ := padic_split anz hp.left
  rw[prod]; clear prod
  rw[Nat.totient_mul cop]; clear cop
  have : 0 < padicValNat p a := by
    by_contra ν0; simp at ν0
    cases ν0
    · case inl p1;
      rw[p1] at hp; simp at hp; contradiction
    case inr pp; cases pp
    · case inr az; exact anz az
    case inr.inr pndiv;
    exact pndiv hp.right
  rw[Nat.totient_prime_pow hp.left this]
  exists p ^ (padicValNat p a - 1) * k.totient
  nth_rewrite 2 [mul_comm]; rw[mul_assoc]

lemma tot₁ {p a x} (hp : Nat.Prime p) (hx : p ^ x ∣ a) : p ^ (x - 1) ∣ a.totient := by
  have := (fact_iff.mpr hp) --Fact
  by_cases anz : a = 0
  · simp[anz]
  by_cases xnz : x = 0
  · simp[xnz]
  by_cases νnz : padicValNat p a = 0
  · simp at νnz
    rcases νnz with c1 | c2 | c3
    · rw[c1] at hp; contradiction
    · contradiction
    · have : p^1 ∣ p^x := by
        refine Nat.pow_dvd_pow p ?_
        exact Nat.one_le_iff_ne_zero.mpr xnz
      have : p^1 ∣ a := Nat.dvd_trans this hx
      simp at this; contradiction
  let ⟨k, kha, khb, _⟩ := padic_split anz hp
  have tot_split := Nat.totient_mul khb
  rw[←kha] at tot_split; clear kha khb
  have := Nat.totient_prime_pow hp (Nat.zero_lt_of_ne_zero νnz)
  rw[this] at tot_split; clear this
  suffices suff : p^(x-1) ∣ p ^ (padicValNat p a - 1) by
    let ⟨j, jh⟩ := suff
    rw[jh] at tot_split
    exists j * (p - 1) * k.totient
    rw[tot_split, mul_assoc, mul_assoc]
    nth_rewrite 2 [←mul_assoc]; rfl
  suffices suff : x ≤ padicValNat p a from Nat.pow_dvd_pow p (Nat.sub_le_sub_right suff 1)
  exact (padicValNat_dvd_iff_le anz).mp hx

lemma tot₄ {a x p j} (h : 2 ^ x ∣ a) (hp : Nat.Prime p ∧ p ∣ a) (hj : p = 2 * j + 1) :
    2^x * j ∣ a.totient := by
  by_cases anz : a = 0
  · simp[anz]
  let ⟨u, uha, uhb, uhc⟩ := padic_split anz Nat.prime_two
  by_cases unz : u = 0
  · rw[unz] at uha; simp at uha; contradiction
  have toth := Nat.totient_mul uhb
  rw[←uha] at toth
  have : 2*j ∣ u.totient := by
    have hpa : p ∣ u := by
      have hpb := uha ▸ hp.right
      have : Nat.Coprime p (2 ^ padicValNat 2 a) := by
        refine Nat.Coprime.pow_right (padicValNat 2 a) ?_
        refine Nat.coprime_two_right.mpr ?_
        exists j
      exact Nat.Coprime.dvd_of_dvd_mul_left this hpb
    have := tot₀ ⟨hp.left, hpa⟩
    rw[hj] at this; simp at this; exact this
  let ⟨v, vh⟩ := this
  rw[vh] at toth; clear vh this
  by_cases xnz : x = 0
  · simp[xnz]
    have : (2^padicValNat 2 a).totient * (2 * j * v) =
        j * ((2 ^ padicValNat 2 a).totient * 2 * v) := by linarith
    rw[this] at toth
    exists ((2 ^ padicValNat 2 a).totient * 2 * v)
  have : 2^(x-1) ∣ (2 ^ padicValNat 2 a).totient := by
    have : (2^x).Coprime u :=Nat.gcd_pow_left_of_gcd_eq_one uhc
    have : 2^x ∣ 2 ^ padicValNat 2 a := Nat.Coprime.dvd_of_dvd_mul_right this (uha ▸ h)
    exact tot₁ Nat.prime_two this
  let ⟨w, wh⟩ := this; clear this
  rw[wh] at toth; clear wh
  have : 2 ^ (x - 1) * w * (2 * j * v) = 2^(x-1) * 2 * j * (w * v) := by linarith;
  rw[this] at toth; clear this
  rw[pow_sub_one_mul xnz 2] at toth
  exists (w * v)

lemma reduce_νp {a p x} (hp : Nat.Prime p ∧ p ^ x ∣ a) (xnz : x ≠ 0) (anz : a ≠ 0) :
    ∃ b, Reachable a b ∧ padicValNat p b = x := by
  have := (fact_iff.mpr hp.left) --Fact
  have ind (y : ℕ) : a < p^x + y → ∃ b, Reachable a b ∧ padicValNat p b = x := by
    induction y generalizing a
    · intro al; exfalso
      have : p^x ∈ a.divisors := Nat.mem_divisors.mpr ⟨hp.right, anz⟩ --duplicated code
      have pxlea := Nat.divisor_le this; clear this                   --duplicated code
      exact (Nat.not_lt.mpr pxlea) al
    · case succ y ih; intro al
      have : p^x ∈ a.divisors := Nat.mem_divisors.mpr ⟨hp.right, anz⟩ --duplicated code
      have pxlea := Nat.divisor_le this; clear this                   --duplicated code
      by_cases divtot : p^x ∣ a.totient
      · have prem₁ : a.totient ≠ 0 := by simp; exact anz
        have prem₂ : a.totient < p ^ x + y := by
          have : 1 < a := by calc
            1 < p   := Nat.Prime.one_lt hp.left
            _ ≤ p^x := by
              suffices suff : p^1 ≤ p^x by simp at suff; exact suff
              refine Nat.pow_le_pow_right ?_ ?_
              · exact Nat.zero_lt_of_ne_zero (Nat.Prime.ne_zero hp.left)
              · exact Nat.one_le_iff_ne_zero.mpr xnz
            _ ≤ a   := pxlea
          have := Nat.totient_lt a this
          exact Nat.lt_of_lt_of_le this (Nat.le_of_lt_succ al)
        let ⟨b, bh⟩ := ih ⟨hp.left, divtot⟩ prem₁ prem₂; clear ih divtot prem₁ prem₂
        exists b; constructor
        · exact .trans .φ bh.left
        · exact bh.right
      exists a; clear ih xnz pxlea al
      constructor
      · exact .rfl
      let ⟨k, kh⟩ := hp.right
      have nz : p^x ≠ 0 ∧ k ≠ 0 := by
        constructor
        · by_contra pxz
          rw[pxz] at kh; simp at kh
          exact anz kh
        · by_contra pkz
          rw[pkz] at kh; simp at kh
          exact anz kh
      rw[kh, padicValNat.mul nz.left nz.right]; simp
      right; right; by_contra pdivk
      let ⟨j, jh⟩ := pdivk
      have ppo : p ^ (x+1) ∣ a := by
        rw[jh] at kh
        exists j
        rw[kh]
        rw[Nat.pow_add]; simp; rw[mul_assoc]
      have := tot₁ hp.left ppo
      contradiction
  have : a < p^x + (a + 1) := Nat.lt_add_left (p^x) (lt_add_one a)
  exact ind (a+1) this

lemma sigma1_of {a p} (hp : Nat.Prime p ∧ padicValNat p a = 1) :
    ∃ b, b ≠ 0 ∧ Reachable a b ∧ p+1 ∣ b := by
  have anz : a ≠ 0 := by
    by_contra az
    rw[az] at hp
    simp at hp
  exists σ 1 a; and_intros
  · simp; assumption
  · exact .σ
  · let ⟨k, kh⟩ := padic_split anz hp.left
    rw[hp.right] at kh; simp at kh
    have : σ 1 a = (σ 1 p) * (σ 1 k) := by
      rw[kh.left]
      exact ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        ArithmeticFunction.isMultiplicative_sigma kh.right
    rw[this]
    have : σ 1 p = p + 1 := by
      have : (σ 1) (p ^ 1) = ∑ j ∈ Finset.range (1 + 1), p ^ (j * 1) :=
        ArithmeticFunction.sigma_apply_prime_pow hp.left
      simp at this; exact this
    rw[this]; simp

lemma p_form {r a p} (hp : Nat.Prime p ∧ p ∣ a) (anz : a ≠ 0)
    (hk : ∃ k, p = 2 ^ r * k + 2 ^ r - 1) : ∃ b, b ≠ 0 ∧ Reachable a b ∧ 2^r ∣ b := by
  have : p^1 ∣ a := by simp; exact hp.right
  let ⟨s, sh⟩ := reduce_νp ⟨hp.left, this⟩ Nat.one_ne_zero anz; clear this
  let ⟨b, bha, bhb, bhc⟩ := sigma1_of ⟨hp.left, sh.right⟩
  exists b; refine ⟨bha, .trans sh.left bhb, ?_⟩
  let ⟨k, hk₂⟩ := hk; clear hk
  suffices 2^r ∣ p+1 from Nat.dvd_trans this bhc
  rw[hk₂]
  exists k + 1
  have : 0 < 2^r * k + 2^r := Nat.pos_of_neZero (2 ^ r * k + 2 ^ r)
  rw[Nat.sub_add_cancel this, mul_add]; simp

lemma large_pp (r : ℕ) : ∃ m, ∀ a p pp,
    a ≠ 0 → Nat.Prime p ∧ p^pp ∣ a ∧ pp > m → ∃ b, b ≠ 0 ∧ Reachable a b ∧ 2^r ∣ b := by
  exists 2^r - 1
  intro a p pp anz ⟨ph1, ph2, ph3⟩
  by_cases rnz : 2^r - 1 = 0
  · have : 2^r ≤ 1 := Nat.le_of_sub_eq_zero rnz
    have : 2^r = 0 ∨ 2^r = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp this
    rcases this with r0 | r1
    · have : 2 = 0 := eq_zero_of_pow_eq_zero r0
      contradiction
    exists a; simp[r1]; exact ⟨anz, .rfl⟩
  have : p ^ (2^r - 1) ∣ a := by
    have := Nat.pow_dvd_pow p (Nat.le_of_succ_le ph3)
    exact Nat.dvd_trans this ph2
  let ⟨b, bh1, bh2⟩ := reduce_νp ⟨ph1, this⟩ rnz anz; clear this
  by_cases bnz : b = 0
  · have := bnz ▸ bh2; simp at this
    exfalso; exact rnz (Eq.symm this)
  exists (σ 0 b)
  and_intros
  · simp; assumption
  · exact .trans bh1 .τ
  let ⟨k, kha, khb, _⟩ := padic_split bnz ph1
  have : (σ 0 b) = (σ 0 (p ^ padicValNat p b)) * (σ 0 k) := by
    nth_rewrite 1 [kha]
    exact ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_sigma khb
  rw[this, bh2]; clear this kha khb
  exists (σ 0 k)
  simp; left
  rw[ArithmeticFunction.sigma_zero_apply_prime_pow ph1]
  refine Nat.sub_add_cancel ?_
  by_contra cont;
  have : 2^r = 0 := by exact Nat.eq_zero_of_not_pos cont
  rw[this] at rnz; contradiction

lemma omega_helper {a : ℕ} (h : a.Coprime 2) : 2^(ω a) ∣ a.totient := by
  suffices ∀ om, om = ω a → 2^om ∣ a.totient from this (ω a) rfl
  intro om; induction om generalizing a
  · simp
  case succ om ih; intro oh
  by_cases anz : a = 0
  · rw[anz] at oh; simp at oh
  by_cases ano : a = 1
  · rw[ano] at oh; simp at oh
  let ⟨p, pha, phb⟩ := Nat.exists_prime_and_dvd ano
  have := (fact_iff.mpr pha) --Fact
  have pvnnz : padicValNat p a ≠ 0 := (dvd_iff_padicValNat_ne_zero anz).mp phb
  let ⟨k, kha, khb, _⟩ := padic_split anz pha
  have da : 2 ∣ (p ^ padicValNat p a).totient := by
    let ⟨j, jh⟩ := Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_left phb h)
    exact calc
      2 ∣ 2 * j                         := Nat.dvd_mul_right 2 j
      _ = p - 1                         := Eq.symm (Nat.sub_eq_of_eq_add jh)
      _ ∣ (p ^ padicValNat p a).totient := tot₀ ⟨pha, (dvd_pow_self p pvnnz)⟩
  have db : 2^om ∣ k.totient := by
    specialize ih (?_ : k.Coprime 2) ?_
    · have : k ∣ a := by rw[←mul_comm] at kha; exact ⟨p ^ padicValNat p a, kha⟩
      exact Nat.Coprime.coprime_dvd_left this h
    · have omh := ArithmeticFunction.cardDistinctFactors_mul khb
      rw[←kha, ←oh] at omh
      have : IsPrimePow (p ^ (padicValNat p a)) := by
        refine ⟨p, padicValNat p a, ?_, ?_, ?_⟩
        · exact Nat.prime_iff.mp pha
        · exact Nat.zero_lt_of_ne_zero pvnnz
        · rfl
      rw[ArithmeticFunction.cardDistinctFactors_eq_one_iff.mpr this] at omh
      nth_rewrite 2 [add_comm] at omh
      exact Nat.succ_inj.mp omh
    exact ih
  exact calc 2 ^ (om + 1)
    _ = 2^om * 2                                  := rfl
    _ ∣ (p ^ padicValNat p a).totient * k.totient := by rw[mul_comm]; exact Nat.mul_dvd_mul da db
    _ = (p ^ padicValNat p a * k).totient         := by symm; exact Nat.totient_mul khb
    _ = a.totient := by rw[←kha]

lemma distinct_ps (r : ℕ) : ∃ m, ∀ a, ω a > m → ∃ b, b ≠ 0 ∧ Reachable a b ∧ 2^r ∣ b := by
  exists (r + 1); intro a ah
  by_cases anz : a = 0
  · simp[anz] at ah
  exists a.totient; and_intros
  · simp; assumption
  · exact .φ

  let ⟨k, kha, khb, khc⟩ := padic_split anz Nat.prime_two

  have omha := omega_helper (Nat.coprime_comm.mp khc)
  have omhb := ArithmeticFunction.cardDistinctFactors_mul khb
  rw[←kha] at omhb
  have omhc : ω (2 ^ padicValNat 2 a) ≤ 1 := by
    by_cases pvnnz : padicValNat 2 a = 0
    · simp[pvnnz]
    have : IsPrimePow (2 ^ padicValNat 2 a) := by
      refine ⟨2, padicValNat 2 a, ?_, ?_, ?_⟩
      · exact Nat.prime_iff.mp Nat.prime_two
      · exact Nat.zero_lt_of_ne_zero pvnnz
      · rfl
    have := ArithmeticFunction.cardDistinctFactors_eq_one_iff.mpr this
    exact Nat.le_of_eq this

  have l1 : r ≤ ω a - 1 := Nat.le_of_succ_le (Nat.lt_sub_of_add_lt ah)
  have l2 : ω a - 1 ≤ ω k := by
    refine Nat.sub_le_of_le_add ?_;
    rw[omhb, add_comm]; simp; exact omhc
  exact calc 2^r
    _ ∣ 2 ^ (ω a - 1)                             := Nat.pow_dvd_pow 2 l1
    _ ∣ 2 ^ (ω k)                                 := Nat.pow_dvd_pow 2 l2
    _ ∣ k.totient                                 := omha
    _ ∣ (2 ^ padicValNat 2 a).totient * k.totient := by simp
    _ = a.totient                                 := by
        nth_rewrite 2 [kha]; rw[Nat.totient_mul khb]

lemma large_p m₁ ppmax dpmax : ∃ m₂, ∀ a,
    a > m₂ → (∀ p pp, Nat.Prime p ∧ p^pp ∣ a → pp ≤ ppmax) → ω a ≤ dpmax →
    ∃ p, Nat.Prime p ∧ p ∣ a ∧ p > m₁ := by
  by_cases m1nz : m₁ = 0
  · rw[m1nz]; exists 1; intro a ah _ _
    let ⟨p, ph⟩ := Nat.exists_prime_and_dvd (Ne.symm (Nat.ne_of_lt ah))
    exact ⟨p, ⟨ph.left, ph.right, Nat.Prime.pos ph.left⟩⟩
  have zlmo := Nat.zero_lt_of_ne_zero m1nz; clear m1nz
  exists m₁^(dpmax * ppmax) + 1; intro a ah ph oh
  by_contra pha; simp at pha

  have oneterm {c : ℕ} : c ∣ a → IsPrimePow c → c ≤ m₁^ppmax := by
    intro cha chb
    let ⟨p, k, pka, pkb, pkc⟩ := chb
    have kl := ph p k ⟨Prime.nat_prime pka, pkc ▸ cha⟩
    have pda := calc
      p ∣ p^k := dvd_pow_self p (Nat.ne_zero_of_lt pkb)
      _ ∣ a   := pkc ▸ cha
    have ple := pha p (Prime.nat_prime pka) pda
    exact calc
      c = p^k      := Eq.symm pkc
      _ ≤ m₁^k     := Nat.pow_le_pow_left ple k
      _ ≤ m₁^ppmax := Nat.pow_le_pow_right zlmo kl

  have ind (om : ℕ) : ∀ b, b ∣ a → ω b = om + 1 → b ≤ m₁^((om + 1) * ppmax) := by
    induction om
    · intro b bha bhb; simp at bhb; simp
      rw[ArithmeticFunction.cardDistinctFactors_eq_one_iff] at bhb
      exact oneterm bha bhb
    case succ om ih; intro b bha bhb
    by_cases bnz : b = 0
    · rw[bnz]; simp
    by_cases bno : b = 1
    · rw[bno] at bhb; simp at bhb;

    let ⟨p, ph⟩ := Nat.exists_prime_and_dvd bno
    have := (fact_iff.mpr ph.left)
    have ppbnz : padicValNat p b ≠ 0 := (dvd_iff_padicValNat_ne_zero bnz).mp ph.right

    let ⟨k, kha, khb, _⟩ := padic_split bnz ph.left
    have omk := ArithmeticFunction.cardDistinctFactors_mul khb
    rw[←kha, bhb] at omk
    have : ω (p ^ padicValNat p b) = 1 :=
      ArithmeticFunction.cardDistinctFactors_apply_prime_pow ph.left ppbnz
    rw[this] at omk
    specialize ih k ?_ ?_
    · exact calc
        k ∣ p ^ padicValNat p b * k := Nat.dvd_mul_left k (p ^ padicValNat p b)
        _ = b                       := Eq.symm kha
        _ ∣ a                       := bha
    · suffices suff : ω k + 1 = om + 1 + 1 from Nat.succ_inj.mp suff
      rw[omk, add_comm]

    suffices suff : p ^ padicValNat p b ≤ m₁^ppmax from calc b
      _ = p ^ padicValNat p b * k              := kha
      _ = k * p ^ padicValNat p b              := by rw[mul_comm]
      _ ≤ k * m₁^ppmax                         := Nat.mul_le_mul_left k suff
      _ ≤ (m₁ ^ ((om + 1) * ppmax)) * m₁^ppmax := Nat.mul_le_mul_right (m₁ ^ ppmax) ih
      _ = m₁ ^ ((om + 1) * ppmax + ppmax)      := by rw[Nat.pow_add]
      _ ≤ m₁ ^ ((om + 1 + 1) * ppmax)          := by simp[add_mul, add_comm]
    refine oneterm ?_ ?_
    · exact calc p ^ padicValNat p b
        _ ∣ p ^ padicValNat p b * k := Nat.dvd_mul_right (p ^ padicValNat p b) k
        _ = b                       := by symm; exact kha
        _ ∣ a                       := bha
    · exists p, padicValNat p b
      exact ⟨Nat.Prime.prime ph.left, Nat.zero_lt_of_ne_zero ppbnz, rfl⟩

  have omeq : ω a - 1 + 1 = ω a := by
    refine Nat.sub_add_cancel ?_
    refine Nat.one_le_iff_ne_zero.mpr ?_
    simp; exact Nat.lt_of_add_left_lt ah
  have := ind (ω a - 1) a; specialize this ?_ (Eq.symm omeq)
  · simp
  rw[omeq] at this
  have := calc
    a ≤ m₁ ^ (ω a * ppmax)       := this
    _ ≤ m₁ ^ (dpmax * ppmax)     := Nat.pow_le_pow_right zlmo (Nat.mul_le_mul_right ppmax oh)
    _ < m₁ ^ (dpmax * ppmax) + 1 := by simp
    _ < a                        := ah
  exact (lt_self_iff_false a).mp this

lemma bound_trichotomy (r m₁ : ℕ) : ∃ m₂, ∀ a, a > m₂ →
    (∃ b, b ≠ 0 ∧ Reachable a b ∧ 2^r ∣ b) ∨ (∃ p, Nat.Prime p ∧ p ∣ a ∧ p > m₁) := by
  let ⟨ma, mah⟩ := large_pp r
  let ⟨mb, mbh⟩ := distinct_ps r
  let ⟨mc, mch⟩ := large_p m₁ ma mb
  exists mc; intro a abig
  by_cases anz : a = 0
  · rw[anz] at abig; contradiction
  by_cases h_large_p : ∀ p pp : ℕ, Nat.Prime p ∧ p ^ pp ∣ a → pp ≤ ma
  case neg =>
    have : ∃ p pp : ℕ, Nat.Prime p ∧ p^pp ∣ a ∧ pp > ma := by
      simp at h_large_p; simp; exact h_large_p
    let ⟨p, pp, pph⟩ := this
    left; exact mah a p pp anz pph
  clear mah
  by_cases h_distinct_ps : ω a ≤ mb
  case neg =>
    simp at h_distinct_ps
    left; exact mbh a h_distinct_ps
  clear mbh
  let ⟨p, pbig⟩ := mch a abig h_large_p h_distinct_ps; clear mch abig h_large_p h_distinct_ps
  right; exists p

lemma find_composite (m₁ r : ℕ) : ∃ m₂, ∀ a x p,
    a ≠ 0 → 2^x ∣ a → Nat.Prime p → p ∣ a → p > m₂ → (¬ ∃ k, p = 2^r * k + 2^r - 1) →
    ∃ b j, b = 2^x * j ∧ Reachable a b ∧ b > m₁ ∧ j > 1 ∧ ¬ Nat.Prime j := by
  induction r
  · exists 0; intro _ _ _ _ _ _ _ _ p_form; simp at p_form
  case succ r ih; let ⟨m₂, mh⟩ := ih; clear ih
  exists (2*m₂ + 1) + (m₁ + 1) + 3; intro a x p anz txda pha phb phc phd
  have : Odd p := by
    have : p > 2 := Nat.lt_of_add_left_lt phc
    have : p ≠ 2 := by symm; exact Nat.ne_of_lt this
    exact Nat.Prime.odd_of_ne_two pha this
  let ⟨j, pj⟩ := this; clear this
  have atotnz : a.totient ≠ 0 := by simp; assumption
  have toth := tot₄ txda ⟨pha, phb⟩ pj
  by_cases jh : Nat.Prime j
  · specialize mh a.totient x j atotnz ?_ jh ?_ ?_ ?_
    · exact dvd_of_mul_right_dvd toth
    · exact dvd_of_mul_left_dvd toth
    · have := pj ▸ Nat.lt_of_add_right_lt (Nat.lt_of_add_right_lt phc)
      simp at this; assumption
    · by_contra ek
      let ⟨k, hek⟩ := ek; clear ek
      rw[hek] at pj; rw[pj] at phd; clear pj hek
      specialize phd ?_
      · exists k
        simp[Nat.mul_sub_left_distrib, Nat.mul_add, ←Nat.mul_assoc 2 (2^r) k, Nat.pow_succ']
        symm; rw[Nat.pred_eq_succ_iff]; symm
        refine Nat.sub_add_cancel ?_
        suffices 2 ≤ 2 * 2^r by exact Nat.le_add_left_of_le this
        simp; exact Nat.one_le_two_pow
      assumption
    let ⟨b, j, bha, bhb, bhc, bhd, bhe⟩ := mh; exists b, j
    exact ⟨bha, .trans .φ bhb, bhc, bhd, bhe⟩
  · clear mh
    let ⟨u, uh⟩ := toth
    have jha : 1 < j := by
      suffices j ≠ 0 ∧ j ≠ 1 from Nat.one_lt_iff_ne_zero_and_ne_one.mpr this
      and_intros
      · by_contra jz
        rw[jz] at pj; rw[pj] at pha; simp at pha; contradiction
      · by_contra jo
        rw[jo] at pj
        have : p > 3 := Nat.lt_of_add_left_lt phc
        rw[pj] at this; contradiction
    exists a.totient, (j * u); and_intros
    · rw[mul_assoc] at uh; exact uh
    · exact .φ
    · have phe : p > m₁ + 1 := Nat.lt_of_add_left_lt (Nat.lt_of_add_right_lt phc)
      have : p-1 ∣ a.totient := tot₀ ⟨pha, phb⟩
      have := Nat.mem_divisors.mpr ⟨this, atotnz⟩
      have : p-1 ≤ a.totient := Nat.divisor_le this
      exact Nat.lt_of_lt_of_le (Nat.lt_sub_of_add_lt phe) this
    · by_cases unz : u = 0
      · rw[unz] at uh
        simp at uh; contradiction
      have ug := Nat.zero_lt_of_ne_zero unz
      exact calc j * u
        _ > 1 * u := Nat.mul_lt_mul_of_pos_right jha ug
        _ ≥ 1 := Nat.le_mul_of_pos_right 1 ug
    · rw[Nat.prime_def]; simp; intro _
      rw[Nat.prime_def] at jh; simp at jh
      let ⟨w, wh⟩ := jh jha; exists w
      and_intros
      · exact Nat.dvd_mul_right_of_dvd wh.left u
      · exact wh.right.left
      · have : w ∈ j.divisors := by
          refine Nat.mem_divisors.mpr ⟨?_, ?_⟩
          · exact wh.left
          · exact Nat.ne_zero_of_lt jha
        have : w ≤ j := Nat.divisor_le this
        have wha : w < j := Nat.lt_of_le_of_ne this wh.right.right
        have : j ≤ j * u := by
          refine Nat.le_mul_of_pos_right j ?_
          by_cases unz : u = 0
          · rw[unz] at uh; simp at uh
            contradiction
          exact Nat.zero_lt_of_ne_zero unz
        have : w < j * u := Nat.lt_of_lt_of_le wha this
        exact Nat.ne_of_lt this

lemma distinct_q {m b x q q₂} :
    b ≠ 0 → Nat.Prime q → q > m + 1 → Nat.Prime q₂ → q ≠ q₂ → q₂ ≠ 2 → 2^x * q * q₂ ∣ b →
    ∃ c, Reachable b c ∧ 2^(x+1) ∣ c ∧ c > m := by
  intro bha qha qhb q2ha q2hb q2hc bhb;
  have ha : 2^x ∣ b := by refine dvd_trans ?_ bhb; exists q * q₂; linarith
  have hb : q ∣ b := by refine dvd_trans ?_ bhb; exists 2^x * q₂; linarith
  have hc : q₂ ∣ b := by refine dvd_trans ?_ bhb; exists 2^x * q; linarith
  by_cases qparity : Even q
  · exists b; and_intros
    · exact .rfl
    · let ⟨k, kh⟩ := even_iff_two_dvd.mp qparity
      have : 2^(x+1) = 2^x * 2 := rfl
      rw[this]; rw[kh] at bhb
      refine dvd_trans ?_ bhb; exists k * q₂; linarith
    · exact calc
        b ≥ q := Nat.divisor_le (Nat.mem_divisors.mpr ⟨hb, bha⟩)
        _ > m := Nat.lt_of_succ_lt qhb

  exists b.totient
  by_cases bhc : b.totient = 0
  · simp at bhc; contradiction

  and_intros
  · exact .φ
  case neg.refine_2.refine_2 =>
    have := tot₀ ⟨qha, hb⟩
    have : q - 1 ∈ b.totient.divisors := Nat.mem_divisors.mpr ⟨this, bhc⟩
    have : q - 1 ≤ b.totient := Nat.divisor_le this
    exact calc
      m < q - 1     := Nat.lt_sub_of_add_lt qhb
      _ ≤ b.totient := this

  let ⟨k, kha, khb, _⟩ := padic_split bha Nat.prime_two
  by_cases knz : k = 0
  · rw[knz] at kha; simp at kha; contradiction
  let ⟨j, jha, jhb, _⟩ := padic_split knz qha
  suffices suff : 2^(x-1) ∣ (2 ^ padicValNat 2 b).totient ∧
      2 ∣ (q ^ padicValNat q k).totient ∧ 2 ∣ j.totient by
    let ⟨⟨sa, sah⟩, ⟨sb, sbh⟩, ⟨sc, sch⟩⟩ := suff; clear suff
    have := Nat.totient_mul jhb
    rw[←jha] at this; clear jha jhb
    rw[sbh, sch] at this; clear sbh sch
    have := this ▸ Nat.totient_mul khb
    rw[←kha] at this; clear kha khb
    rw[sah] at this; clear sah
    rw[this]
    by_cases xnz : x = 0
    · simp[xnz]; exists 2 * sa * sb * sc; linarith
    exists sa * sb * sc
    have : 2^(x+1) = 2^(x-1) * 2 * 2 := calc 2^(x+1)
      _ = 2^x * 2         := rfl
      _ = 2^(x-1+1) * 2   := by rw [←Nat.succ_pred_eq_of_ne_zero xnz]; rfl
      _ = 2^(x-1) * 2 * 2 := rfl
    rw[this]; linarith

  have odd_primes_give_twos {a p} (ha : Nat.Prime p) (hb : Odd p) (hc : p ∣ a) :
      2 ∣ a.totient := by
    let ⟨u, uh⟩ := hb
    exact calc
      2 ∣ 2 * u      := by simp
      _ = p - 1     := Eq.symm (Nat.sub_eq_of_eq_add uh)
      _ ∣ a.totient := tot₀ ⟨ha, hc⟩
  have qs_div_k {p : ℕ} (ha : p ∣ b) (hb : Odd p) : p ∣ k := by
    have : p.Coprime (2 ^ padicValNat 2 b) := by
      refine Nat.Coprime.pow_right (padicValNat 2 b) ?_
      exact Nat.coprime_two_right.mpr hb
    exact Nat.Coprime.dvd_of_dvd_mul_left this (kha ▸ ha)

  and_intros
  · have ctk : Nat.Coprime 2 k := by
      by_contra cont; simp at cont
      let ⟨s, sh⟩ := even_iff_two_dvd.mp cont
      have := sh ▸ kha
      have : 2^(padicValNat 2 b + 1) ∣ b := by rw[←mul_assoc] at this; exists s
      have := (padicValNat_dvd_iff_le bha).mp this
      simp at this
    have : (2^x).Coprime k := Nat.gcd_pow_left_of_gcd_eq_one ctk; clear ctk
    have := Nat.Coprime.dvd_of_dvd_mul_right this (kha ▸ ha)
    exact tot₁ Nat.prime_two this
  · simp at qparity
    have qdiv : q ∣ q ^ padicValNat q k := by
      refine dvd_pow_self q ?_
      simp; refine ⟨?_, knz, qs_div_k hb qparity⟩
      by_contra cc; rw[cc] at qha; contradiction
    exact odd_primes_give_twos qha qparity qdiv
  · have oddq2 := Nat.Prime.odd_of_ne_two q2ha q2hc
    have : q₂ ∣ j := by
      have := qs_div_k hc oddq2
      suffices suff : q₂.Coprime (q ^ padicValNat q k) from
        Nat.Coprime.dvd_of_dvd_mul_left suff (jha ▸ this)
      suffices q₂.Coprime q from Nat.gcd_pow_right_of_gcd_eq_one this
      exact (Nat.coprime_primes q2ha qha).mpr (Ne.symm q2hb)
    exact odd_primes_give_twos q2ha oddq2 this

lemma q_square {m x q b} : b ≠ 0 → Nat.Prime q → q > 3 → q > m + 1 → 2^x * q^2 ∣ b →
    ∃ c, Reachable b c ∧ 2^(x+1) ∣ c ∧ c > m := by
  intro bnz qha qhb qhc bh
  have := (fact_iff.mpr qha)

  have : q ≠ 2 := by exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_add_left_lt qhb))
  have qodd := Nat.Prime.odd_of_ne_two qha this; clear this
  let ⟨i, iha⟩ := qodd
  by_cases inz : i = 0
  · rw[inz] at iha; rw[iha] at qha; simp at qha; contradiction
  have btota : 2^x * i ∣ b.totient := by
    have := calc
      q ∣ q^2 := by simp
      _ ∣ b   := dvd_of_mul_left_dvd bh
    exact tot₄ (dvd_of_mul_right_dvd bh) ⟨qha, this⟩ iha
  have btotb : q ∣ b.totient := by
    let ⟨k, kha, khb, _⟩ := padic_split bnz qha
    have toth := Nat.totient_mul khb
    rw[←kha] at toth; clear kha khb
    have νh : 1 < padicValNat q b := by
      have : q^2 ∣ b := dvd_of_mul_left_dvd bh
      exact (padicValNat_dvd_iff_le bnz).mp this
    rw[Nat.totient_prime_pow qha (Nat.zero_lt_of_lt νh)] at toth
    exact calc
      q = q^1                       := by simp
      _ ∣ q ^ (padicValNat q b - 1) := Nat.pow_dvd_pow q (Nat.le_sub_one_of_lt νh)
      _ ∣ b.totient                 := by exists (q - 1) * k.totient; linarith[toth]

  have qcopi : q.Coprime i :=
    have : i < q := calc
      i = 1 * i     := by simp
      _ ≤ 2 * i     := by refine Nat.mul_le_mul_right i ?_; simp
      _ < 2 * i + 1 := lt_add_one (2 * i)
      _ = q         := by symm; exact iha
    Nat.coprime_of_lt_prime inz this qha
  have btotc : 2^x * i * q ∣ b.totient := by
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ btota btotb
    refine Nat.coprime_mul_iff_left.mpr ?_
    and_intros
    · refine Nat.Coprime.pow_left x ?_
      exact Nat.coprime_two_left.mpr qodd
    · exact Nat.coprime_comm.mp qcopi
  clear btota btotb

  by_cases ihb : 2 ∣ i
  · exists b.totient; and_intros
    · exact .φ
    · let ⟨j, jh⟩ := ihb
      rw[jh] at btotc
      exact calc 2^(x+1)
        _ ∣ 2^(x+1) * (j * q) := by simp
        _ = 2^x * 2 * (j * q) := rfl
        _ = 2^x * (2 * j) * q := by linarith
        _ ∣ b.totient         := btotc
    · calc
      m < q             := Nat.lt_of_succ_lt qhc
      _ ≤ 2 ^ x * i * q := by
          refine Nat.le_mul_of_pos_left q ?_
          simp; exact Nat.zero_lt_of_ne_zero inz
      _ ≤ b.totient     := by
          have : 2 ^ x * i * q ∈ b.totient.divisors := by
            refine Nat.mem_divisors.mpr ⟨btotc, ?_⟩
            simp; exact bnz
          exact Nat.divisor_le this

  by_cases ino : i = 1
  · rw[ino] at iha; rw[iha] at qhb; simp at qhb

  let ⟨q₂, q₂h⟩ := Nat.exists_prime_and_dvd ino
  have : ∃ c, Reachable b.totient c ∧ 2^(x+1) ∣ c ∧ c > m := by
    by_cases btotnz : b.totient = 0
    · simp at btotnz; contradiction
    refine distinct_q btotnz qha qhc q₂h.left ?_ ?_ ?_
    · have := calc q₂
        _ ≤ i       := Nat.divisor_le (Nat.mem_divisors.mpr ⟨q₂h.right, inz⟩)
        _ < 2*i + 1 := by linarith
        _ = q       := by rw[iha]
      exact Ne.symm (Nat.ne_of_lt this)
    · by_contra tdi; have := tdi ▸ q₂h.right; contradiction
    · let ⟨j, jh⟩ := q₂h.right
      exact calc 2^x * q * q₂
        _ ∣ 2^x * q * q₂ * j   := by simp
        _ = 2^x * (q₂ * j) * q := by linarith
        _ = 2^x * i * q        := by rw[jh]
        _ ∣ b.totient          := btotc
  let ⟨c, cha, chb⟩ := this
  exists c; exact ⟨.trans .φ cha, chb.left, chb.right⟩

lemma j_cases {q x j} (hqa : Nat.Prime q ∧ q > 2 ∧ q ∣ 2 ^ x * j) (hj : j > 1 ∧ ¬Nat.Prime j) :
    2 ∣ j ∨ q^2 ∣ j ∨ (q ∣ j ∧ ∃ q₂, Nat.Prime q₂ ∧ q₂ ≠ 2 ∧ q₂ ∣ j ∧ q ≠ q₂) := by
  have : q.Coprime (2^x) := by
    refine Nat.Coprime.pow_right x ?_
    refine Nat.coprime_two_right.mpr ?_
    have : q ≠ 2 := by exact Ne.symm (Nat.ne_of_lt hqa.right.left)
    exact Nat.Prime.odd_of_ne_two hqa.left this
  have qdj : q ∣ j := Nat.Coprime.dvd_of_dvd_mul_left this hqa.right.right
  let ⟨u, uh⟩ := qdj
  by_cases uno : u = 1
  · have := uno ▸ uh ▸ hj.right
    simp at this
    exfalso; exact this hqa.left
  let ⟨q₂, q₂h⟩ := Nat.exists_prime_and_dvd uno
  rw[mul_comm] at uh
  have q₂dj := Nat.dvd_trans q₂h.right ⟨q, uh⟩
  by_cases qtnt : q₂ = 2
  · left; exact qtnt ▸ q₂dj
  by_cases qeq : q₂ = q
  · right; left
    let ⟨v, vh⟩ := q₂h.right
    have := qeq ▸ vh ▸ uh
    rw[this, mul_comm, ←mul_assoc, ←Nat.pow_two]
    exists v;
  right; right; constructor
  · exact qdj
  · exists q₂
    change q₂ ≠ q at qeq; symm at qeq
    exact ⟨q₂h.left, qtnt, q₂dj, qeq⟩

lemma obtain_pow_two_rec (r y : ℕ) : ∃ m, ∀ a x,
    2^x ∣ a → x+y ≥ r → a > m → ∃ b, b ≠ 0 ∧ Reachable a b ∧ 2^r ∣ b := by
  induction y
  · exists 0; intro a x diva xbig abig; exists a
    by_cases anz : a = 0
    · rw[anz] at abig; contradiction
    exact ⟨anz, .rfl, Nat.pow_dvd_of_le_of_pow_dvd xbig diva⟩
  case succ y ih;

  let ⟨ma, mah⟩ := ih; clear ih
  let ⟨mb, mbh⟩ := bound_trichotomy r (max (ma + 1) 3)
  let ⟨mc, mch⟩ := find_composite (max ma mb) r
  let ⟨md, mdh⟩ := bound_trichotomy r mc

  exists md; intro a x tdiva expbig abig
  rw[add_comm y 1, ←add_assoc] at expbig
  rcases mdh a abig with case1 | ⟨p, pha, phb, phc⟩
  · exact case1
  clear mdh
  by_cases anz : a = 0
  · rw[anz] at abig; contradiction
  clear abig

  by_cases h_p_form : (∃ k : ℕ, p = 2^r * k + 2^r - 1)
  · exact p_form ⟨pha, phb⟩ anz h_p_form
  let ⟨b, j, bha, bhb, bhc, jha, jhb⟩ := mch a x p anz tdiva pha phb phc h_p_form
  clear mch tdiva pha phb phc h_p_form
  have bnz : b ≠ 0 := by
    by_contra bz;
    have := bz ▸ bhc
    contradiction

  rcases mbh b (Nat.max_lt.mp bhc).right with ⟨c, cha, chb, chc⟩ | ⟨q, qha, qhb, qhc⟩
  · exists c; exact ⟨cha, .trans bhb chb, chc⟩
  clear mbh

  have qg3 : q > 3 := (Nat.max_lt.mp qhc).right
  have qg2 : q > 2 := Nat.lt_of_add_left_lt qg3
  rcases j_cases ⟨qha, qg2, bha ▸ qhb⟩ ⟨jha, jhb⟩
      with ⟨v, vh⟩ | ⟨v, vh⟩ | ⟨qd, ⟨q₂, q₂ha, q₂hb, q₂hc, q₂hd⟩⟩
  · have := vh ▸ bha
    rw[←mul_assoc] at this
    have xpodiv : 2^(x+1) ∣ b := by exists v
    let ⟨c, cha, chb, chc⟩ := mah b (x+1) xpodiv expbig (Nat.max_lt.mp bhc).left
    exists c; exact ⟨cha, .trans bhb chb, chc⟩
  · have : 2^x * q^2 ∣ b := by
      have := vh ▸ bha
      rw[←mul_assoc] at this
      exists v
    let ⟨c, cha, chb, chc⟩ := q_square bnz qha qg3 (Nat.max_lt.mp qhc).left this
    let ⟨d, dha, dhb, dhc⟩ := mah c (x+1) chb expbig chc    --duplicated code
    exists d; exact ⟨dha, .trans (.trans bhb cha) dhb, dhc⟩ --duplicated code
  · have : 2^x * q * q₂ ∣ b := by
      have : q * q₂ ∣ j := by
        let ⟨u, uh⟩ := qd;
        rw[uh] at q₂hc
        have : q₂.Coprime q := (Nat.coprime_primes q₂ha qha).mpr (Ne.symm q₂hd)
        let ⟨v, vh⟩ := Nat.Coprime.dvd_of_dvd_mul_left this q₂hc
        rw[vh, ←mul_assoc] at uh
        exists v
      let ⟨v, vh⟩ := this
      have := vh ▸ bha
      rw[←mul_assoc, ←mul_assoc] at this
      exists v
    let ⟨c, cha, chb, chc⟩ := distinct_q bnz qha (Nat.max_lt.mp qhc).left q₂ha q₂hd q₂hb this
    let ⟨d, dha, dhb, dhc⟩ := mah c (x+1) chb expbig chc    --duplicated code
    exists d; exact ⟨dha, .trans (.trans bhb cha) dhb, dhc⟩ --duplicated code

lemma obtain_pow_two (r : ℕ) : ∃ m, ∀ a, a > m → Reachable a (2^r) := by
  let ⟨m, mh⟩ := obtain_pow_two_rec r r
  exists m; intro a abig
  have ⟨b, bha, bhb, bhc⟩ := mh a 0 ?_ ?_ ?_
  case refine_1 | refine_2 => simp
  case refine_3 => assumption

  have nondecr {a y o : ℕ} (ah : a = 2^y * o) (oha : Odd o) (ohb : o ≠ 1) :
      2^y ∣ a.totient := by
    have : ∃ p, Nat.Prime p ∧ Odd p ∧ p ∣ a := by
      let ⟨p, pha, phb⟩ := Nat.exists_prime_and_dvd ohb
      exists p; refine ⟨pha, ?_, ?_⟩
      · by_contra cont; simp at cont
        have : 2 ∣ p := even_iff_two_dvd.mp cont
        have : 2 ∣ o := Nat.dvd_trans this phb
        have : ¬ 2 ∣ o := Odd.not_two_dvd_nat oha
        contradiction
      · have : o ∣ a := by exists 2^y; rw[mul_comm] at ah; exact ah
        exact Nat.dvd_trans phb this
    let ⟨p, pha, ⟨j, hj⟩, phb⟩ := this
    have aha : 2^y ∣ a := by exists o
    exact calc 2^y
      _ ∣ 2^y * j   := by simp
      _ ∣ a.totient := tot₄ aha ⟨pha, phb⟩ hj

  have ind (o : ℕ) : ∀ a y, a > 0 → a = 2^y * o → Odd o → y ≥ r →
      ∃ z, Reachable a (2^z) ∧ z ≥ r := by
    induction o using Nat.strong_induction_on
    case h o ih; intro a y aha ahb oha yh
    by_cases ohb : o = 1
    · exists y; simp[ohb, ahb]; exact ⟨.rfl, yh⟩
    by_cases ano : a = 1
    · simp[ano] at ahb; symm at ahb
      have := Nat.eq_one_of_mul_eq_one_right ahb; simp at this
      rw[this] at yh; simp at yh
      exists 0; simp[yh, ano]; exact .rfl
    have ola := (Nat.two_le_iff a).mpr ⟨Nat.ne_zero_of_lt aha, ano⟩; clear ano
    by_cases atot : a.totient = 0
    · simp at atot; have := Nat.ne_zero_of_lt aha; contradiction

    let ⟨k, kha, khb, khc⟩ := padic_split atot Nat.prime_two
    specialize ih k ?_ a.totient (padicValNat 2 a.totient) ?_ kha ?_ ?_
    · have : y ≤ padicValNat 2 a.totient := by
        have := nondecr ahb oha ohb
        exact (padicValNat_dvd_iff_le atot).mp this
      have : 2^y ≤ 2 ^ (padicValNat 2 a.totient) := by refine Nat.pow_le_pow_right ?_ this; simp
      have := calc 2^y * k
        ≤ 2 ^ (padicValNat 2 a.totient) * k := Nat.mul_le_mul_right k this
        _ = a.totient                       := Eq.symm kha
        _ < a                               := Nat.totient_lt a ola
        _ = 2^y * o                         := ahb
      exact Nat.lt_of_mul_lt_mul_left this
    · exact Nat.totient_pos.mpr aha
    · exact Nat.Coprime.odd_of_left khc
    · have : 2^y ∣ a.totient := nondecr ahb oha ohb
      exact calc
        r ≤ y                       := yh
        _ ≤ padicValNat 2 a.totient := (padicValNat_dvd_iff_le atot).mp this
    let ⟨z, zh⟩ := ih
    exists z; exact ⟨.trans .φ zh.left, zh.right⟩

  let ⟨k, kha, _, khc⟩ := padic_split bha Nat.prime_two
  specialize ind k b (padicValNat 2 b) ?_ kha ?_ ?_
  · exact Nat.zero_lt_of_ne_zero bha
  · exact Nat.Coprime.odd_of_left khc
  · exact (padicValNat_dvd_iff_le bha).mp bhc
  let ⟨z, za, zb⟩ := ind
  have (i : ℕ) : Reachable (2^(r+i)) (2^r) := by
    induction i
    · simp; exact .rfl
    case succ i ih;
    refine .trans ?_ ih
    have : (2 ^ (r + (i + 1))).totient = 2 ^ (r + i) := by
      have : 0 < r + (i + 1) := by simp
      rw[Nat.totient_prime_pow Nat.prime_two this]; simp
    rw[←this]; exact .φ
  have := this (z - r)
  rw[Nat.add_sub_of_le zb] at this
  exact .trans bhb (.trans za this)

theorem POTD2414 {a b : ℕ} (ha : a > 1) (hb : b > 1) : Reachable a b := by
  have ra : Reachable (2^(b-1)) b := by
    have : σ 0 (2^(b-1)) = b-1+1 := ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two
    rw[Nat.sub_add_cancel (Nat.one_le_of_lt hb)] at this
    nth_rewrite 2 [←this]; exact .τ

  have rb : ∃ m, ∀ a, a > m → Reachable a b := by
    let ⟨m, mh⟩ := obtain_pow_two (b-1)
    exists m; intro a ah
    have := mh a ah
    exact .trans this ra
  let ⟨m, mh⟩ := rb; clear rb

  have sigma_one_increasing {a : ℕ} (h : a > 1) : σ 1 a > a := by
    have aha : a ≠ 0 := Nat.ne_zero_of_lt h
    have ahb : 1 ∉ ({a} : Finset ℕ) := Finset.notMem_singleton.mpr (Nat.ne_of_lt h)
    rw[ArithmeticFunction.sigma_one_apply a]
    let S := Finset.cons 1 {a} ahb
    have : ∑ d ∈ a.divisors, d ≥ ∑ d ∈ S, d := by
      refine Finset.sum_le_sum_of_ne_zero ?_
      intro x xh _
      unfold S at xh; simp at xh; simp
      rcases xh with cc | cc <;>
      · refine ⟨?_, aha⟩; simp[cc]
    suffices suff : ∑ d ∈ S, d > a from Nat.lt_of_lt_of_le suff this
    change 1 + a > a
    exact lt_one_add a

  have explode (m : ℕ) : ∃ c, c > m ∧ Reachable a c := by
    induction m
    · exists a; exact ⟨Nat.zero_lt_of_lt ha, .rfl⟩
    case succ m ih;
    let ⟨c, cha, chb⟩ := ih; clear ih
    by_cases chc : c ≤ 1
    · have := calc m
        _ < c := cha
        _ ≤ 1 := chc
      simp[Nat.lt_one_iff.mp this]; exists a; exact ⟨ha, .rfl⟩
    exists (σ 1 c); constructor
    · exact calc (σ 1 c)
      _ > c     := sigma_one_increasing (Nat.lt_of_add_left_lt (Nat.lt_of_not_le chc))
      _ ≥ m + 1 := cha
    · exact .trans chb .σ

  let ⟨c, ch⟩ := explode m; clear explode
  have := mh c ch.left
  exact .trans ch.right this
