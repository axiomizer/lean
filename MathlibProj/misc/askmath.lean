import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt

def P (x : Fin 6 → ℝ) := ∀ i : Fin 6, x i = ∏ j : Fin 6 with j ≠ i, x j

def ev (x : Fin 6 → ℝ) := (∀ i, |x i| = 1) ∧ (Even (Finset.card {i | x i = -1}))

lemma claim2 : {x | P x ∧ ∃ i, x i = 0} = {x : Fin 6 → ℝ | ∀ i, x i = 0} := by
  ext x; simp only [Set.mem_setOf_eq]; constructor
  · intro hx; obtain ⟨j, jh⟩ := hx.2; intro i
    by_cases hij : i = j
    · exact hij ▸ jh
    rw[hx.1 i]; clear hx
    apply Finset.prod_eq_zero _ jh
    grind only [= Finset.mem_filter, ← Finset.mem_univ]
  · intro hx; refine ⟨?_, ⟨0, hx 0⟩⟩
    intro i; rw[hx i]; symm
    obtain ⟨k, kh⟩ := exists_ne i
    apply Finset.prod_eq_zero _ (hx k)
    grind only [= Finset.mem_filter, ← Finset.mem_univ]

lemma claim3 : {x | P x ∧ ∀ i, x i ≠ 0} = {x | ev x} := by
  ext x; simp only [ne_eq, Set.mem_setOf_eq]
  have rem_prod : ∀ i, (∏ i, x i = x i * ∏ j with j ≠ i, x j) := by
    intro i
    rw[←Finset.prod_filter_mul_prod_filter_not _ (fun j ↦ j = i) _]
    apply congrArg (· * _)
    rw[←Finset.prod_singleton x i]
    apply congrArg (Finset.prod · (fun i ↦ x i))
    grind only [= Finset.mem_filter, = Finset.mem_singleton, ← Finset.mem_univ]
  have hpow : (∀ i, |x i| = 1) →
      (∀ i, x i = ∏ j with j ≠ i, x j ↔ Even (Finset.card {i | x i = -1})) := by
    intro ho i
    have : x i = ∏ j with j ≠ i, x j ↔ x i * x i = x i * ∏ j with j ≠ i, x j := by
      refine Iff.symm (mul_right_inj' ?_)
      by_contra! c; have := c ▸ ho i; simp only [abs_zero, zero_ne_one] at this
    rw[this, show x i * x i = 1 by grind only [= abs.eq_1, = max_def], ←rem_prod]
    rw[←Finset.prod_filter_mul_prod_filter_not _ (fun i ↦ x i = 1) _]
    replace : (∏ x_1 with x x_1 = 1, x x_1) = 1 := by
      apply Finset.prod_eq_one
      intro j jh; grind only [= Finset.mem_filter]
    rw[this, one_mul]
    replace : ∏ x_1 with ¬x x_1 = 1, x x_1 =
        ∏ x_1 with x x_1 = -1, x x_1 := by
      apply congrArg (Finset.prod · x)
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      replace ho := eq_or_eq_neg_of_abs_eq (ho j)
      grind only
    rw[this]
    replace : ∏ x_1 with x x_1 = -1, x x_1 =
        (-1)^Finset.card {j | x j = -1} := by
      apply Finset.prod_eq_pow_card
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, imp_self, implies_true]
    rw[this]
    have : -1 ≠ (1 : ℝ) := by
      refine neg_ne_self.mpr ?_
      exact one_ne_zero
    rw[←neg_one_pow_eq_one_iff_even this]
    grind only
  constructor
  · intro hp
    suffices ∀ (i : Fin 6), |x i| = 1 from ⟨this, ((hpow this) 0).mp (hp.1 0)⟩
    have hsqr : P x → ∀ i, (x i)^2 = ∏ i, x i := by
      intro px i; specialize px i; rw[pow_two]
      have : x i * x i = x i * ∏ j with j ≠ i, x j := by apply congrArg (x i * ·); exact px
      rw[this, rem_prod i]
    have hone : ∀ i j, |x i| = |x j| := by
      intro i j
      have := calc (x i)^2
        _ = ∏ i, x i := hsqr hp.1 i
        _ = (x j)^2 := by symm; exact hsqr hp.1 j
      exact (sq_eq_sq_iff_abs_eq_abs (x i) (x j)).mp this
    intro i; have := hp.1 i
    replace := calc |x i|
      _ = |∏ j with j ≠ i, x j| := congrArg _ this
      _ = ∏ j with j ≠ i, |x j| := by apply Finset.abs_prod
      _ = |x i|^5 := by
        convert Finset.prod_eq_pow_card _
        · clear rem_prod hpow hp hsqr hone this
          have : i ∉ ({j | j ≠ i} : Finset (Fin 6)) := by grind only [= Finset.mem_filter]
          replace := Finset.card_insert_of_notMem this
          have ins : insert i ({j | j ≠ i} : Finset (Fin 6)) = Finset.univ := by
            grind only [← Finset.mem_univ, = Finset.mem_insert, = Finset.mem_filter]
          rw[ins] at this; clear ins
          simp only [Finset.card_univ, Fintype.card_fin, Nat.reduceEqDiff] at this
          symm; assumption
        · intro j _; exact hone j i
    replace : 1 = |x i|^2 * |x i|^2 := by grind only [= abs.eq_1, = max_def]
    replace := (Real.sqrt_eq_iff_mul_self_eq (zero_le_one' ℝ) (sq_nonneg |x i|)).mpr this
    have : 1 = |x i| * |x i| := by grind only [= Real.sqrt_one]
    replace := (Real.sqrt_eq_iff_mul_self_eq (zero_le_one' ℝ) (abs_nonneg (x i))).mpr this
    simp only [Real.sqrt_one] at this; rw[this]
  · intro hi; refine ⟨?_, by intro i; grind only [hi.1 i, = abs.eq_1]⟩
    have := hpow hi.1; simp only [hi.2, iff_true] at this; exact this

lemma claim5 : {x | ev x}.encard = 32 := by
  let S := {s : Finset (Fin 6) | Even s.card}
  suffices S.encard = 32 by
    rw[←this]; clear this; symm
    refine Set.encard_congr ?_
    refine Set.BijOn.equiv (fun s ↦ (fun i ↦ if i ∈ s then -1 else 1)) ?_
    and_intros
    · intro s hs; simp only [Set.mem_setOf_eq]; constructor
      · intro i; grind only [= Set.setOf_true, = Set.setOf_false, = abs.eq_1, = max_def,
        = Set.mem_empty_iff_false]
      · simp only [ite_eq_left_iff]
        rw[congrArg (a₂ := s.card) (Even ·)]
        · unfold S at hs; simp only [Set.mem_setOf_eq] at hs; exact hs
        · apply congrArg; ext
          grind only [= Finset.mem_filter, ← Finset.mem_univ]
    · intro s hs t ht hst
      simp only at hst; ext i
      have := congrFun hst i; grind only
    · intro x hx; simp only [Set.mem_setOf_eq] at hx; simp only [Set.mem_image]
      exists ({i | x i = -1} : Finset (Fin 6))
      refine ⟨hx.2, ?_⟩
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases xno : x i = -1 <;> simp only [xno, ↓reduceIte]
      replace hx := hx.1 i
      grind only[eq_or_eq_neg_of_abs_eq hx]
  rw[Set.encard_eq_coe_toFinset_card {s : Finset (Fin 6) | Even s.card}]
  decide

theorem thm : {x | P x}.encard = 33 := by
  have claim1 : {x | P x}.encard =
      {x | P x ∧ ∃ i, x i = 0}.encard + {x | P x ∧ ∀ i, x i ≠ 0}.encard := by
    rw[←Set.encard_union_add_encard_inter {x | P x ∧ ∃ i, x i = 0} {x | P x ∧ ∀ i, x i ≠ 0}]
    have : {x | P x ∧ ∃ i, x i = 0} ∩ {x | P x ∧ ∀ i, x i ≠ 0} = ∅ := by
      ext; grind only [= Set.setOf_true, = Set.setOf_false, = Set.mem_inter_iff,
        = Set.mem_empty_iff_false, usr Set.mem_setOf_eq]
    rw[this]; simp only [Set.encard_empty, add_zero]
    apply congrArg; ext x; grind only [usr Set.mem_setOf_eq, = Set.mem_union]
  have claim4 : {x : Fin 6 → ℝ | ∀ i, x i = 0}.encard = 1 := by
    refine Set.encard_eq_one.mpr ?_
    exists fun i ↦ 0; ext x; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro xh; ext i; exact xh i
    · intro xh; rw[xh]; simp only [implies_true]
  rw[claim1, claim2, claim3, claim4, claim5]; grind only
