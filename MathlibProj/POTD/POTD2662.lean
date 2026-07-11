import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Group.End

lemma orb_ord (p r : ℕ) [Fact p.Prime] (U : Equiv.Perm (ZMod p)) (a : ZMod p) :
    (U^r) a = a ↔ Finset.card {b | U.SameCycle a b} ∣ r := by
  let orb : Finset (ZMod p) := {b | U.SameCycle a b}
  let o := orb.card
  have loop' (x y : ℤ) (hlt : x < y) (heq : (U^x) a = (U^y) a) : o ≤ y-x := by
    have loopy : (U^(y-x)) a = a := by
      exact calc (U^(y-x)) a
        _ = (U^(y + (-x))) a := rfl
        _ = (U ^ (-x)) ((U ^ y) a) := by rw[add_comm, zpow_add, Equiv.Perm.mul_apply]
        _ = (U ^ (-x)) ((U ^ x) a) := by rw[heq]
        _ = (U^(x +(-x))) a := by rw[←Equiv.Perm.mul_apply, ←zpow_add, add_comm]
        _ = a := by rw[Int.add_right_neg]; simp only [zpow_zero, Equiv.Perm.coe_one, id_eq]
    let map' : ℤ → ZMod p := fun n ↦ (U^n) a
    have : Set.SurjOn map' (Finset.Ico 0 (y-x)) orb := by
      intro j jh; unfold orb at jh
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at jh
      obtain ⟨i, ih⟩ := jh
      rw[←EuclideanDomain.div_add_mod i (y-x)] at ih
      exists (i%(y-x)); constructor
      · simp only [Finset.coe_Ico, Set.mem_Ico]
        constructor
        · refine Int.emod_nonneg i ?_
          apply sub_ne_zero_of_ne; exact Ne.symm (Int.ne_of_lt hlt)
        · exact Int.emod_lt_of_pos i (Int.sub_pos_of_lt hlt)
      · unfold map'; rw[←ih]
        rw[add_comm, zpow_add]; simp only [Equiv.Perm.coe_mul, Function.comp_apply]
        rw[zpow_mul]
        rw[Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self loopy (i / (y-x))]
    replace := Finset.card_le_card_of_surjOn map' this
    rw[Int.card_Ico 0 (y-x)] at this; grind only [= Finset.mem_Icc]
  have loop (x y : ℕ) (hlt : x < y) (heq : (U^x) a = (U^y) a) : o ≤ y-x := by
    have : (U^(x:ℤ)) a = (U^(y:ℤ)) a := by
      exact ZMod.valMinAbs_inj.mp (congrArg ZMod.valMinAbs heq)
    have := loop' (x:ℤ) (y:ℤ) (Int.ofNat_lt.mpr hlt) this
    rw[←Int.ofNat_sub (Nat.le_of_succ_le hlt)] at this; exact Int.ofNat_le.mp this
  let map : ℕ → ZMod p := fun n ↦ (U^n) a
  have reduce : (U^o) a = a := by
    have hc : o < (Finset.Icc 0 o).card := by
      simp only [Nat.card_Icc, tsub_zero, lt_add_iff_pos_right, zero_lt_one]
    have hf : Set.MapsTo map (Finset.Icc 0 o) orb := by
      intro x xh; unfold orb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      unfold map; exists x
    obtain ⟨x, xh, y, yh, hineq, hm⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hf
    unfold map at hm
    replace hm : (U^(min x y)) a = (U^(max x y)) a := by grind only [= max_def, = min_def]
    have : min x y < max x y := by grind only [= min_def, = max_def]
    replace := loop (min x y) (max x y) this hm
    have : min x y = 0 ∧ max x y = o := by
      grind only [= Finset.mem_Icc, = max_def, = min_def]
    rw[this.1, this.2] at hm
    simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hm
    symm; exact hm
  constructor
  · intro hfix
    have euc := Nat.div_add_mod r o
    rw[←euc, add_comm, pow_add, pow_mul, Equiv.Perm.mul_apply] at hfix
    rw[Equiv.Perm.pow_apply_eq_self_of_apply_eq_self reduce] at hfix
    by_cases roz : 0 < r % o
    · specialize loop 0 (r % o) roz
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq, tsub_zero, hfix, forall_const] at loop
      have : o ≠ 0 := by
        refine Finset.card_ne_zero.mpr ?_
        exists a; unfold orb; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Equiv.Perm.SameCycle.refl U a
      replace : r%o < o := Nat.mod_lt r (Nat.zero_lt_of_ne_zero this)
      replace := Nat.lt_of_le_of_lt loop this
      replace := (Nat.not_lt_zero 0) (Nat.lt_add_right_iff_pos.mp this)
      contradiction
    · simp only [not_lt, nonpos_iff_eq_zero] at roz
      rw[roz] at euc; rw[←euc]; exists (r/o)
  · intro hdiv; obtain ⟨k, kh⟩ := hdiv; change r = o * k at kh; subst kh
    rw[pow_mul, Equiv.Perm.pow_apply_eq_self_of_apply_eq_self reduce]

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
  have claim1 : U 0 = 0 := by
    have := calc B * U 0
      _ = B * U (U (U 0)) := by
        apply (mul_right_inj' bnz).mpr
        apply Equiv.Perm.congr_arg
        symm; exact (mul_eq_zero_iff_left bnz).mp (ha 0)
      _ = U 0 := ha (U 0)
    by_contra c
    replace := (mul_eq_right₀ c).mp this; subst this
    simp only [orderOf_one, Nat.not_even_one] at ord_even
  have claim1' (n : ℤ) := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self claim1 n
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
      apply (orb_ord p cyc.card U w).mpr
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
        rw[claim1' n] at nh; rw[nh]
      · intro az; subst az; exact hA2
    · intro hA; constructor
      · unfold cycles Finpartition.ofSetoid Finpartition.ofSetSetoid
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exists 0; subst hA; ext a; constructor
        · intro ah
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ah
          obtain ⟨n, nh⟩ := ah; rw[claim1' n] at nh; subst nh; simp only [Finset.mem_singleton]
        · intro ah; simp only [Finset.mem_singleton] at ah; subst ah
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exists 0
      · rw[hA]; simp only [Finset.mem_singleton]
  rw[this, Finset.sum_singleton, Finset.card_singleton] at s
  apply Nat.eq_sub_of_add_eq' at s
  apply Nat.dvd_div_of_mul_dvd
  rw[←s]; exact Finset.dvd_sum claim2
