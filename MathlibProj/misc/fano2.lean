import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Pairwise.Basic

open Finset

def block_design (t k n : ℕ) (bd : Finset (Finset (Fin n))) : Prop :=
  (∀ b ∈ bd, #b = k) ∧ (∀ s : Finset (Fin n), #s = t → ∃! b ∈ bd, s ⊆ b)

lemma pair_count {bd : Finset (Finset (Fin 7))} (hbd : ∀ b ∈ bd, #b = 3)
    (h2 : ∀ x a b, a ∈ bd → b ∈ bd → #x = 2 → x ⊆ a → x ⊆ b → a = b) :
    3 * #bd = #{p | #p = 2 ∧ ∃ b ∈ bd, p ⊆ b} := by
  let t : Finset (Fin 7) → Finset (Finset (Fin 7)) :=
    fun b ↦ {p : Finset (Fin 7) | #p = 2 ∧ p ⊆ b}
  have disj : Set.PairwiseDisjoint bd t := by
    intro a ha b hb hab; unfold Function.onFun
    apply Finset.disjoint_iff_ne.mpr
    intro x hx y hy; by_contra c; subst c
    replace hx := (mem_filter.mp hx).2
    replace hy := (mem_filter.mp hy).2
    have := h2 x a b ha hb hx.1 hx.2 hy.2
    contradiction
  exact calc 3 * #bd
    _ = ∑ u ∈ bd, #(t u) := by
      symm; rw[mul_comm]; refine sum_const_nat ?_
      intro x hx
      convert Finset.card_powersetCard 2 x
      · ext i; unfold t
        simp only [mem_filter, mem_univ, true_and, mem_powersetCard]
        rw[and_comm]
      · simp[hbd x hx]
    _ = #(bd.biUnion t) := by rw[Finset.card_biUnion disj]
    _ = #{p | #p = 2 ∧ ∃ b ∈ bd, p ⊆ b} := by
      apply congrArg; grind only [= mem_biUnion, = mem_filter, ← mem_univ]

lemma bd7 {bd : Finset (Finset (Fin 7))} (hbd : block_design 2 3 7 bd) : #bd = 7 := by
  have := calc 3 * #bd
    _ = #{p : Finset (Fin 7) | #p = 2} := by
      have h2 : ∀ x a b, a ∈ bd → b ∈ bd → #x = 2 → x ⊆ a → x ⊆ b → a = b := by
        intro x a b ha hb hx1 hx2 hx3
        exact ExistsUnique.unique (hbd.2 x hx1) ⟨ha, hx2⟩ ⟨hb, hx3⟩
      rw[pair_count (fun b hb ↦ hbd.1 b hb) h2]
      apply congrArg; ext p
      simp only [mem_filter, mem_univ, true_and, univ_filter_card_eq, mem_powersetCard, subset_univ,
        and_iff_left_iff_imp]
      intro hp; exact ExistsUnique.exists (hbd.2 p hp)
    _ = 21 := by
      simp only [univ_filter_card_eq, card_powersetCard, card_univ, Fintype.card_fin]; rfl
  lia

theorem thm : ∀ bd, block_design 2 3 7 bd ↔
    #bd = 7 ∧ (∀ b ∈ bd, #b = 3) ∧ (∀ a ∈ bd, ∀ b ∈ bd, a ≠ b → #(a ∩ b) ≤ 1) := by
  intro bd; constructor
  · intro hbd; refine ⟨bd7 hbd, hbd.1, ?_⟩
    intro a ha b hb hab
    by_contra! c
    obtain ⟨p, hp⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt c)
    suffices a = b by contradiction
    apply ExistsUnique.unique (hbd.2 p hp.2) ⟨ha, ?_⟩ ⟨hb, ?_⟩
    · exact Finset.Subset.trans hp.1 inter_subset_left
    · exact Finset.Subset.trans hp.1 inter_subset_right
  · intro hbd; refine ⟨hbd.2.1, ?_⟩
    intro p hp
    have h2 : ∀ x a b, a ∈ bd → b ∈ bd → #x = 2 → x ⊆ a → x ⊆ b → a = b := by
      intro x a b ha hb hx1 hx2 hx3; by_contra! c
      have := calc 2
        _ = #x := Eq.symm hx1
        _ ≤ #(a ∩ b) := card_le_card (subset_inter hx2 hx3)
        _ ≤ 1 := hbd.2.2 a ha b hb c
      contradiction
    have hcard := hbd.1 ▸ pair_count hbd.2.1 h2
    have hsubset : ({p | #p = 2 ∧ ∃ b ∈ bd, p ⊆ b} : Finset _) ⊆
        ({p : Finset (Fin 7) | #p = 2} : Finset _) := by
      grind only [= subset_iff, = mem_filter]
    have := Finset.eq_of_subset_of_card_le hsubset (le_of_eq hcard)
    replace := ((Finset.ext_iff.mp this) p).mpr
    simp only [univ_filter_card_eq, mem_powersetCard, subset_univ, true_and, mem_filter,
      mem_univ] at this
    obtain ⟨b, hb⟩ := (this hp).2
    exists b; simp only [and_imp]; refine ⟨hb, ?_⟩; intro a ha1 ha2
    exact h2 p a b ha1 hb.1 hp ha2 hb.2
