import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Partition.Finpartition

theorem orb_ord {α : Type} [Fintype α] [DecidableEq α] (U : Equiv.Perm α) (a : α) (r : ℕ) :
    (U^r) a = a ↔ Finset.card {b | U.SameCycle a b} ∣ r := by
  by_cases! hu : U a = a
  · rw[Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hu]
    simp only [true_iff]; convert one_dvd r
    refine (Fintype.existsUnique_iff_card_one (U.SameCycle a)).mp ?_
    exists a; simp only
    refine ⟨Equiv.Perm.SameCycle.refl U a, ?_⟩
    intro y hy; obtain ⟨n, hn⟩ := hy
    rw[Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hu] at hn
    exact Eq.symm hn
  rw[←Equiv.Perm.cycleOf_pow_apply_self, ←zpow_natCast]
  rw[Equiv.Perm.cycle_zpow_mem_support_iff]
  · simp only [EuclideanDomain.mod_eq_zero]
    suffices (U.cycleOf a).support.card = Finset.card {b | U.SameCycle a b} by
      rw[this]; exact Int.ofNat_dvd
    apply congrArg
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    convert Equiv.Perm.mem_support_cycleOf_iff
    suffices a ∈ U.support from ⟨fun h ↦ ⟨h, this⟩, fun h ↦ h.1⟩
    exact Equiv.Perm.mem_support.mpr hu
  · exact (Equiv.Perm.isCycle_cycleOf_iff U).mpr hu
  · rw[Equiv.Perm.cycleOf_apply_self]; exact hu

theorem POTD_2662 (p : ℕ) [Fact p.Prime] (hodd : Odd p) (U : Equiv.Perm (ZMod p)) (B : ZMod p)
    (ha : ∀ a : ZMod p, B * U (U a) = a) : B ^ ((p - 1) / 2) = 1 := by
  have bnz : B ≠ 0 := by
    by_contra c; subst c; specialize ha 1; simp only [zero_mul, zero_ne_one] at ha
  suffices orderOf B ∣ (p-1)/2 by
    obtain ⟨k, hk⟩ := this
    rw[hk, pow_mul, pow_orderOf_eq_one, one_pow]
  by_cases ord_even : Odd (orderOf B)
  · apply Nat.dvd_div_of_mul_dvd
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · exact Nat.coprime_two_left.mpr ord_even
    · obtain ⟨k, kh⟩ := hodd; exists k; lia
    · apply orderOf_dvd_of_pow_eq_one
      exact ZMod.pow_card_sub_one_eq_one bnz
  apply Nat.not_odd_iff_even.mp at ord_even
  have claim1 (n : ℤ) : (U^n) 0 = 0 := by
    have := calc B * U 0
      _ = B * U (U (U 0)) := by
        apply (mul_right_inj' bnz).mpr
        apply Equiv.Perm.congr_arg
        symm; exact (mul_eq_zero_iff_left bnz).mp (ha 0)
      _ = U 0 := ha (U 0)
    apply Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
    by_contra c
    replace := (mul_eq_right₀ c).mp this; subst this
    simp only [orderOf_one, Nat.not_even_one] at ord_even
  open Classical in
  let cycles := Finpartition.ofSetoid (Equiv.Perm.SameCycle.setoid U)
  have claim2 : ∀ c ∈ cycles.parts.filter (fun x ↦ 0 ∉ x), 2 * (orderOf B) ∣ c.card := by
    intro cyc cych; simp only [Finset.mem_filter] at cych
    obtain ⟨cha, chb⟩ := cych
    unfold cycles Finpartition.ofSetoid Finpartition.ofSetSetoid at cha
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at cha
    obtain ⟨w, wh⟩ := cha
    unfold Equiv.Perm.SameCycle.setoid Equiv.Perm.SameCycle at wh; simp only at wh
    have word : (U ^ cyc.card) w = w := by
      apply (orb_ord U w cyc.card).mpr
      exists 1; simp only [mul_one]
      apply congrArg; rw[←wh]; unfold Equiv.Perm.SameCycle
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have UtoB (n : ℕ) : ∀ a : ZMod p, B^n * (U^(2*n)) a = a := by
      induction n
      case zero =>
        simp only [pow_zero, mul_zero, Equiv.Perm.coe_one, id_eq, one_mul, implies_true]
      case succ n ih =>
        intro a
        have := calc (U ^ (2 * (n + 1))) a
          _ = (U ^ (1 + 1 + 2 * n)) a := by lia
          _ = (U^(1+1)) ((U^(2*n)) a) := by
            rw[pow_add]; simp only [Equiv.Perm.coe_mul, Function.comp_apply]
          _ = U (U ((U^(2*n)) a)) := by
            rw[pow_add]; simp only [pow_one, Equiv.Perm.coe_mul, Function.comp_apply]
        exact calc B ^ (n + 1) * (U ^ (2 * (n + 1))) a
          _ = B^(n+1) * U (U ((U^(2*n)) a)) := by rw[this]
          _ = B^n * (B * U (U ((U^(2*n)) a))) := by rw[←mul_assoc]; lia
          _ = B^n * (U^(2*n)) a := by rw[ha ((U^(2*n)) a)]
          _ = a := ih a
    have := calc B^cyc.card * w
      _ = B^cyc.card * (U^(2*cyc.card)) w := by
        rw[Nat.two_mul, pow_add]; simp only [Equiv.Perm.coe_mul, Function.comp_apply]
        rw[word, word]
      _ = w := UtoB cyc.card w
    have wnz : w ≠ 0 := by
      have : w ∈ cyc := by
        rw[←wh]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exists 0
      by_contra c; subst c; exact chb this
    replace : B^cyc.card = 1 := by grind only
    obtain ⟨m, mh⟩ : 2 ∣ cyc.card := calc
      2 ∣ orderOf B := even_iff_two_dvd.mp ord_even
      _ ∣ cyc.card := orderOf_dvd_of_pow_eq_one this
    rw[mh]; apply Nat.mul_dvd_mul_left; apply orderOf_dvd_of_pow_eq_one
    have := calc B^m * w
      _ = B^m * (U^cyc.card) w := by rw[word]
      _ = B^m * (U^(2*m)) w := by rw[mh]
      _ = w := UtoB m w
    grind only
  have s := Finset.sum_filter_add_sum_filter_not cycles.parts (fun p ↦ 0 ∈ p) (fun p ↦ p.card)
  replace s := Finpartition.sum_card_parts cycles ▸ s
  simp only [Finset.card_univ, ZMod.card] at s
  have : cycles.parts.filter (fun x ↦ 0 ∈ x) = {{0}} := by
    ext A; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor
    · intro ⟨hA1, hA2⟩; ext a; simp only [Finset.mem_singleton]; constructor
      · intro ha
        unfold cycles Finpartition.ofSetoid Finpartition.ofSetSetoid at hA1
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hA1
        obtain ⟨a₀, ha₀⟩ := hA1; subst ha₀
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        apply Setoid.symm' at hA2
        obtain ⟨n, nh⟩ := Setoid.trans' (Equiv.Perm.SameCycle.setoid U) hA2 ha
        rw[claim1 n] at nh; rw[nh]
      · intro az; subst az; exact hA2
    · intro hA; constructor
      · unfold cycles Finpartition.ofSetoid Finpartition.ofSetSetoid
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exists 0; subst hA; ext a; constructor
        · intro ah
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ah
          obtain ⟨n, nh⟩ := ah; rw[claim1 n] at nh; subst nh; simp only [Finset.mem_singleton]
        · intro ah; simp only [Finset.mem_singleton] at ah; subst ah
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exists 0
      · rw[hA]; simp only [Finset.mem_singleton]
  rw[this, Finset.sum_singleton, Finset.card_singleton] at s
  apply Nat.eq_sub_of_add_eq' at s
  apply Nat.dvd_div_of_mul_dvd
  rw[←s]; exact Finset.dvd_sum claim2
