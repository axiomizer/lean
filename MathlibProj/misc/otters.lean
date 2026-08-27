import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

abbrev V := Fin 2024

open Finset in
theorem friendly (G : SimpleGraph V) :
    ¬ (∀ S : Finset V, #S = 1012 → ∃! o ∉ S, ∀ s ∈ S, G.Adj o s) := by
  by_contra cont
  have cliques : ∀ i : V, ∀ n : ℕ, n ≤ 1012 →
      ∃ K : Finset V, i ∈ K ∧ #K = n + 1 ∧ G.IsClique K := by
    intro i n; induction n with | zero | succ n ih
    · intro _; exists {i}; refine ⟨by simp only [mem_singleton], rfl, ?_⟩
      rw[coe_singleton]; exact SimpleGraph.isClique_singleton i
    · intro hn
      obtain ⟨K, hK1, hK2, hK3⟩ := ih (Nat.le_of_succ_le hn)
      have hcomp := calc #(Kᶜ)
        _ = 2024 - #K := by
          apply Nat.eq_sub_of_add_eq'
          convert Finset.card_add_card_compl K
          simp only [Fintype.card_fin]
        _ ≥ 1012 - (n+1) := by lia
      obtain ⟨J, hJ⟩ := Finset.exists_subset_card_eq hcomp
      have : #(K ∪ J) = 1012 := by
        have := LE.le.disjoint_compl_right hJ.1
        rw[compl_compl] at this
        rw[union_comm, card_union_of_disjoint this, hJ.2, hK2]
        grind only
      obtain ⟨o, ho1, _⟩ := cont (K ∪ J) this
      exists (K ∪ {o}); and_intros
      · exact mem_union_left {o} hK1
      · have : Disjoint K {o} := by
          simp only [disjoint_singleton_right]
          by_contra cont
          exact ho1.1 (mem_union_left J cont)
        rw[card_union_of_disjoint this, hK2, card_singleton]
      · intro a ha b hb hab
        simp only [union_singleton, coe_insert, Set.mem_insert_iff, SetLike.mem_coe] at ha hb
        by_cases a = o
        · subst a; apply ho1.2; grind only [= mem_union]
        by_cases b = o
        · symm; subst b; apply ho1.2; grind only [= mem_union]
        have : a ∈ K ∧ b ∈ K := by grind only
        exact hK3 this.1 this.2 hab
  obtain ⟨clique1, hc1a, hc1b, hc1c⟩ := cliques 0 1012 (Nat.le_refl 1012)
  have : #clique1 < ENat.card V := by
    rw[hc1b]; unfold V
    simp only [Nat.cast_ofNat, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    trivial
  obtain ⟨i, hi⟩ := Finset.exists_not_mem_of_card_lt_enatCard this
  obtain ⟨clique2, hc2a, hc2b, hc2c⟩ := cliques i 1012 (Nat.le_refl 1012)
  replace : 1 < #(clique1 ∩ clique2) := by
    grind only [card_finset_fin_le (clique1 ∪ clique2), card_union clique1 clique2]
  obtain ⟨o1, ho1, o2, ho2, ho⟩ := Finset.one_lt_card.mp this
  specialize cont ((clique1 \ {o1, o2}) ∪ {i}) ?_
  · have disj : Disjoint (clique1 \ {o1, o2}) {i} := by
      simp only [disjoint_singleton_right]
      exact notMem_sdiff_of_notMem_left hi
    replace subs : {o1, o2} ⊆ clique1 := by
      grind only [= subset_iff, = mem_inter, = mem_insert, = mem_singleton]
    rw[card_union_of_disjoint disj, card_sdiff_of_subset subs]
    rw[hc1b, card_singleton, card_pair ho]
  obtain ⟨eq, _, heq⟩ := cont
  suffices suff : ∀ o, o = o1 ∨ o = o2 → o = eq by
    rw[suff o1 (by left; rfl), suff o2 (by right; rfl)] at ho
    contradiction
  intro o ho; refine heq _ ⟨?_, ?_⟩
  · grind only [= mem_inter, = mem_union, = mem_sdiff, = mem_singleton, = mem_insert]
  · intro s hs; rcases (mem_union.mp hs) with c1 | c2
    · refine hc1c (by grind only [= mem_coe, = mem_inter]) (Finset.mem_sdiff.mp c1).1 ?_
      grind only [= mem_sdiff, = mem_insert, = mem_singleton]
    · refine hc2c (by grind only [= mem_coe, = mem_inter]) ((mem_singleton.mp c2) ▸ hc2a) ?_
      grind only [= mem_inter, = mem_singleton]
