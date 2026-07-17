import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.Unbundled
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.MaxPowDiv

set_option maxRecDepth 800

lemma div_alg (a b : ℕ) (h : 0 < b) : ∃ q r, a = b*q+r ∧ r < b := by
  exists (a/b), (a%b)
  refine ⟨?_, Nat.mod_lt a h⟩
  symm; exact Nat.div_add_mod a b

lemma factorize (m : ℕ) (hm : m ≠ 0) : ∃ x y k, m = 2^x * 5^y * k ∧ k.Coprime 2 ∧ k.Coprime 5 := by
  exists (padicValNat 2 m)
  obtain ⟨j, jh⟩ : 2 ^ padicValNat 2 m ∣ m := pow_padicValNat_dvd
  nth_rewrite 1 [jh]
  suffices ∃ y k, j = 5 ^ y * k ∧ k.Coprime 2 ∧ k.Coprime 5 by
    obtain ⟨y, k, h⟩ := this
    exists y, k; refine ⟨?_, h.2.1, h.2.2⟩
    rw[mul_assoc]; apply congrArg (2 ^ padicValNat 2 m * ·)
    exact h.1
  exists (padicValNat 5 m)
  obtain ⟨l, lh⟩ : 5 ^ padicValNat 5 m ∣ j := by
    have := pow_padicValNat_dvd (p := 5) (n := m)
    nth_rewrite 2 [jh] at this
    have cop : (5 ^ padicValNat 5 m).Coprime (2 ^ padicValNat 2 m) :=
      Nat.pow_gcd_pow_of_gcd_eq_one rfl
    exact Nat.Coprime.dvd_of_dvd_mul_left cop this
  nth_rewrite 1 [lh]; exists l
  refine ⟨rfl, ?_, ?_⟩
  · by_contra c; simp only [Nat.coprime_two_right, Nat.not_odd_iff_even] at c
    obtain ⟨l', lh'⟩ := c; replace lh' : l = 2 * l' := by lia
    replace jh := lh' ▸ lh ▸ jh
    replace jh : 2 ^ (padicValNat 2 m + 1) ∣ m := by
      exists 5 ^ padicValNat 5 m * l'
      nth_rewrite 1 [jh]; rw[pow_add]; lia
    have : padicValNat 2 m + 1 ≤ padicValNat 2 m := (padicValNat_dvd_iff_le hm).mp jh
    grind only
  · by_contra c
    unfold Nat.Coprime at c
    have : l.gcd 5 ∣ 5 := by exact Nat.gcd_dvd_right l 5
    replace : l.gcd 5 = 1 ∨ l.gcd 5 = 5 := (Nat.dvd_prime Nat.prime_five).mp this
    rcases this with _ | gh
    · contradiction
    obtain ⟨l', lh'⟩ := Nat.gcd_eq_right_iff_dvd.mp gh; clear c gh
    subst lh'
    replace lh : 5 ^ (padicValNat 5 m + 1) ∣ m := by
      exists 2 ^ padicValNat 2 m * l';
      nth_rewrite 1 [jh, lh]; rw[pow_add]; lia
    have : Fact (Nat.Prime 5) := by exact { out := Nat.prime_five }
    have : padicValNat 5 m + 1 ≤ padicValNat 5 m := (padicValNat_dvd_iff_le hm).mp lh
    grind only

def f (n : ℕ) := n * (n + 1) * (n + 12) * (n + 123) * (n + 1234) * (n + 12345)

open Finset in
theorem thm : Maximal (fun m ↦ ∀ n, m ∣ f n) 80 := by
  constructor
  · simp only; intro n
    have d1 : 16 ∣ f n := by
      obtain ⟨q, r, ha, hb⟩ := div_alg n 4 (Nat.zero_lt_succ 3)
      unfold f; subst ha; interval_cases r <;> grind only
    have d2 : 5 ∣ f n := by
      obtain ⟨q, r, ha, hb⟩ := div_alg n 5 (Nat.zero_lt_succ 4)
      unfold f; subst ha; interval_cases r <;> grind only
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl d1 d2
  · simp only; intro m mh temp; clear temp
    have d1 : ¬ (2^5 ∣ m ∨ 3 ∣ m ∨ 5^2 ∣ m) := by
      specialize mh 1; unfold f at mh;
      by_contra! c; rcases c with c | c | c
      <;> replace c := Nat.dvd_trans c mh
      <;> grind only
    have d2 : ∀ p, p.Prime → p ≥ 7 → ¬ p ∣ m := by
      intro p pha phb
      let S : Finset ℕ := {0, 1, 12, 123, 1234, 12345}
      let T : Finset ℕ := Finset.Ico 0 p
      let map : ℕ → ℕ := fun n ↦ n % p
      have mt : Set.MapsTo map S T := by
        intro s _; unfold map T; simp only [Nat.Ico_zero_eq_range, coe_range, Set.mem_Iio]
        refine Nat.mod_lt s ?_
        exact Nat.zero_lt_of_lt phb
      obtain ⟨t, th⟩ : ∃ t ∈ T, ¬ ∃ s ∈ S, map s = t := by
        have := calc #(Finset.image map S)
          _ ≤ #S := card_image_le
          _ = 6 := rfl
          _ < p := Nat.lt_of_succ_le phb
          _ = #T := by unfold T; simp only [Nat.Ico_zero_eq_range, card_range]
        obtain ⟨t, th⟩ := exists_mem_notMem_of_card_lt_card this
        exists t; refine ⟨th.1, ?_⟩
        grind only [= mem_image]
      by_contra! c; replace mh := Nat.dvd_trans c (mh (p-t))
      suffices ∃ s ∈ S, p ∣ (p-t) + s by
        obtain ⟨s, sh⟩ := this
        simp only [not_exists, not_and] at th; have nmap := th.2 s sh.1
        unfold map at nmap
        replace nmap : ¬ (s : ℤ) % p = (t : ℤ) := Nat.ToInt.of_diseq rfl rfl nmap
        have hcast : ((p-t+s : ℕ) : ℤ) = (p-t+s : ℤ) := by
          refine Nat.ToInt.add_congr ?_ rfl
          refine Int.ofNat_sub ?_
          grind only [= mem_Ico]
        have := Int.ofNat_dvd.mpr sh.2
        rw[hcast] at this
        replace : (p : ℤ) ∣ s-t := by grind only [dvd_sub_self_right.mpr this]
        replace : (s-t:ℤ) % p = 0 := by exact Int.emod_eq_zero_of_dvd this
        replace : (s:ℤ)%p = (t:ℤ)%p := by exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr this
        have ht : (t:ℤ)%p=t := by
          refine Int.emod_eq_of_lt ?_ ?_
          · exact Int.natCast_nonneg t
          · refine Int.ofNat_lt.mpr ?_; grind only [= mem_Ico]
        rw[ht] at this
        contradiction
      unfold f at mh;
      rcases Nat.Prime.dvd_or_dvd pha mh with mh | _
      case inr => exists 12345
      rcases Nat.Prime.dvd_or_dvd pha mh with mh | _
      case inr => exists 1234
      rcases Nat.Prime.dvd_or_dvd pha mh with mh | _
      case inr => exists 123
      rcases Nat.Prime.dvd_or_dvd pha mh with mh | _
      case inr => exists 12
      rcases Nat.Prime.dvd_or_dvd pha mh with mh | _
      case inr => exists 1
      case inl => exists 0
    have mnz : m ≠ 0 := by
      by_contra! c; subst c; specialize mh 1; unfold f at mh
      grind only
    obtain ⟨x, y, k, kh⟩ := factorize m mnz
    replace kh : m = 2^x * 5^y := by
      suffices k = 1 by grind only
      by_contra! c; obtain ⟨p, pha, phb⟩ := Nat.exists_prime_and_dvd c
      by_cases pge7 : p ≥ 7
      · specialize d2 p pha pge7
        suffices p ∣ m from d2 this
        apply Nat.dvd_trans phb
        exists 2^x * 5^y; rw[kh.1]; lia
      have : p = 2 ∨ p = 3 ∨ p = 5 := by interval_cases p <;> trivial
      rcases this with c1 | c2 | c3
      · have := Nat.Coprime.coprime_dvd_left phb kh.2.1
        subst c1; contradiction
      · simp only [not_or] at d1
        subst c2; suffices 3 ∣ m from d1.2.1 this
        apply Nat.dvd_trans phb
        exists 2^x * 5^y; rw[kh.1]; lia
      · have := Nat.Coprime.coprime_dvd_left phb kh.2.2
        subst c3; contradiction
    change m ≤ 2^4 * 5^1; subst kh
    refine Nat.mul_le_mul ?_ ?_
    · refine Nat.pow_le_pow_of_le Nat.one_lt_two ?_
      by_contra! c
      replace mh := calc 2^5
        _ ∣ 2^x := by refine Nat.pow_dvd_pow 2 ?_; exact Nat.succ_le_of_lt c
        _ ∣ 2^x * 5^y := by exists 5^y
        _ ∣ f 1 := mh 1
      unfold f at mh; grind only
    · refine Nat.pow_le_pow_of_le (Nat.one_lt_succ_succ 3) ?_
      by_contra! c
      replace mh := calc 5^2
        _ ∣ 5^y := by
          apply Nat.pow_dvd_pow; exact Nat.succ_le_of_lt c
        _ ∣ 2^x * 5^y := by exists 2^x; rw[mul_comm]
        _ ∣ f 1 := mh 1
      unfold f at mh; grind only
