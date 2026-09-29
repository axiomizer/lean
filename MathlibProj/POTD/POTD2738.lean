import Mathlib.Data.Nat.Init
import Mathlib.Tactic.ByContra
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Card
import Mathlib.Order.Interval.Finset.Nat

theorem proof1 (f g : Nat → Nat) (hf : f.Injective) (hg : g.Surjective) (hle : ∀ n, f n ≤ g n) :
    f = g := by
  suffices ∀ N n, g n ≤ N → f n = g n by ext n; exact this (g n) n (Nat.le_refl (g n))
  intro N; induction N using Nat.strong_induction_on with | h N ih
  intro n hn; by_contra c
  replace c := Nat.lt_of_le_of_ne (hle n) c
  obtain ⟨m, hm⟩ := hg (f n)
  specialize ih (g m) (Nat.lt_of_lt_of_le (hm ▸ c) hn) m (Nat.le_refl (g m))
  specialize hf (hm ▸ ih)
  have : 0 < 0 := Nat.lt_add_right_iff_pos.mp (hf ▸ hm ▸ c)
  contradiction

theorem proof2 (f g : Nat → Nat) (hf : f.Injective) (hg : g.Surjective) (hle : ∀ n, f n ≤ g n) :
    f = g := by
  let A (N : ℕ) : Set ℕ := {n : ℕ | f n ≤ N}
  let B (N : ℕ) : Set ℕ := {n : ℕ | g n ≤ N}
  have h0 : ∀ N, B N ⊆ A N := by
    intro N; unfold A B; simp only [Set.ofPred_subset_ofPred]; intro n hn
    exact Nat.le_trans (hle n) hn
  have h1 : ∀ N, Set.encard (A N) ≤ N+1 := by
    intro N
    have mt : Set.MapsTo f (A N) (Set.Icc 0 N) := by
      unfold A; intro n; simp only [Set.mem_ofPred_eq, Set.mem_Icc, zero_le, true_and, imp_self]
    convert Set.encard_le_encard_of_injOn mt (Function.Injective.injOn hf)
    rw[Set.encard_Icc]; simp only [Nat.cast_add, Nat.cast_one, Nat.card_Icc, tsub_zero]
  have h2 : ∀ N, Set.encard (B N) ≥ N+1 := by
    intro N
    convert Set.encard_image_le g (B N)
    suffices g '' B N = Set.Icc 0 N by
      rw[this, Set.encard_Icc]
      simp only [Nat.cast_add, Nat.cast_one, Nat.card_Icc, tsub_zero]
    ext n; constructor
    · unfold B; grind only [= Set.mem_image, = Set.mem_Icc, usr Set.mem_ofPred_eq]
    · intro hn; unfold B; simp only [Set.mem_image, Set.mem_ofPred_eq]
      obtain ⟨x, hx⟩ := hg n; exists x; refine ⟨?_, hx⟩
      rw[hx]; grind only [= Set.mem_Icc]
  have h3 : ∀ N, B N = A N := by
    intro N
    refine Set.Finite.eq_of_subset_of_encard_le ?_ (h0 N) ?_
    · refine Set.Finite.subset ?_ (h0 N)
      exact Set.finite_of_encard_le_coe (h1 N)
    · exact Std.IsPreorder.le_trans (A N).encard (N+1) (B N).encard (h1 N) (h2 N)
  ext n
  have : n ∈ A (f n) := by unfold A; simp only [Set.mem_ofPred_eq, Std.le_refl]
  rw[←h3 (f n)] at this; unfold B at this; simp only [Set.mem_ofPred_eq] at this
  exact Nat.le_antisymm (hle n) this
