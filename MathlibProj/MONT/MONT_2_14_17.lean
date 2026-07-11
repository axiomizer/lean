import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

theorem ELMO_2019_5 (S : Set ℕ) (ne : S.Nonempty) (hs : ∀ a b, a ∈ S → b ∈ S → a * b + 1 ∈ S) :
    {p : ℕ | p.Prime ∧ ∀ s ∈ S, ¬ p ∣ s}.Finite := by
  obtain ⟨w, wh⟩ := ne
  let Sp (p : ℕ) : Set (ZMod p) := {a : ZMod p | ∃ x ∈ S, a = x}
  open Classical in
  have card1 : ∀ p : ℕ, p.Prime → 0 ∉ (Sp p) → ∃! a, a ∈ (Sp p) := by
    intro p pha phb;
    have : NeZero p := ⟨pha.ne_zero⟩
    have : Fact p.Prime := by exact { out := pha }
    let s := ∑ x ∈ Sp p, x
    let n : ZMod p := (Sp p).toFinset.card
    have hs : ∀ a ∈ Sp p, a = 1 - n / s := by
      intro a ah
      have anz : a ≠ 0 := by by_contra c; subst c; exact phb ah
      let f : ZMod p → ZMod p := fun x ↦ a*x + 1
      have mt : Set.MapsTo f (Sp p) (Sp p) := by
        intro x xh
        obtain ⟨av, avh⟩ := ah; obtain ⟨xv, xvh⟩ := xh
        exact ⟨av * xv + 1, hs av xv avh.1 xvh.1, by grind only⟩
      have inj : Set.InjOn f (Sp p) := by
        intro x hx y hy hxy; unfold f at hxy
        simp only [add_left_inj, mul_eq_mul_left_iff] at hxy
        exact Or.resolve_right hxy anz
      have hsum := calc s
        _ = ∑ x ∈ Sp p, f x := by
          symm; apply Finset.sum_nbij f
          · unfold Set.MapsTo at mt; grind only [= Set.mem_toFinset]
          · simp only [Set.coe_toFinset]; exact inj
          · simp only [Set.coe_toFinset]
            have := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite (Sp p)) mt).mp
            exact (this inj).2.2
          · simp only [Set.mem_toFinset, implies_true]
        _ = ∑ x ∈ Sp p, a*x + ∑ x ∈ Sp p, 1 := by
          exact Finset.sum_add_distrib
        _ = a * ∑ x ∈ Sp p, x + ∑ x ∈ Sp p, 1 := by
          apply (add_left_inj _).mpr
          symm; apply Finset.mul_sum
        _ = a * s + n := by
          apply (add_right_inj _).mpr
          symm; apply Finset.cast_card
      have : s ≠ 0 := by
        by_contra sz; simp only [sz, mul_zero, zero_add] at hsum
        unfold n at hsum
        apply congrArg ZMod.val at hsum
        rw[ZMod.val_zero, ZMod.val_natCast] at hsum
        obtain ⟨k, kh⟩ : p ∣ (Sp p).toFinset.card := by
          apply Nat.dvd_of_mod_eq_zero
          symm; exact hsum
        have : k < 2 := by
          have := calc p * k
            _ ≤ Fintype.card (ZMod p) := by
              rw[←kh]
              exact Finset.card_le_univ (Sp p).toFinset
            _ = p := ZMod.card p
            _ < p * 2 := by have := Nat.pos_of_neZero p; lia
          exact Nat.lt_of_mul_lt_mul_left this
        rcases k with _ | k
        · simp only [Set.toFinset_card, Fintype.card_ofFinset, mul_zero, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff, Finset.mem_univ, forall_const] at kh
          specialize kh ah; trivial
        rcases k
        · simp only [zero_add, mul_one] at kh
          replace kh := calc (Sp p).toFinset.card
            _ = p := kh
            _ = Fintype.card (ZMod p) := by symm; exact ZMod.card p
          have := Finset.eq_univ_of_card (Sp p).toFinset kh
          replace := this ▸ (Finset.mem_univ 0)
          apply Set.mem_toFinset.mp at this
          exact phb this
        trivial
      grind only
    exists 1 - n / s; refine ⟨?_, hs⟩
    have : ↑w ∈ Sp p := by exists w
    rw[←hs w this]; exact this
  let P := {p : ℕ | p.Prime ∧ ∀ s ∈ S, ¬ p ∣ s}; change P.Finite
  by_contra c
  obtain ⟨a, b, hab⟩ := show ∃ a b, a ∈ S ∧ b ∈ S ∧ a ≠ b by
    exists w, (w*w + 1); refine ⟨wh, hs w w wh wh, ?_⟩
    have := calc w * w + 1
      _ > w * w := by apply lt_add_one
      _ ≥ w := Nat.le_mul_self w
    exact Nat.ne_of_lt this
  obtain ⟨p, hp⟩ := show ∃ p, p ∈ P ∧ p > a ∧ p > b by
    by_contra c2; simp only [gt_iff_lt, not_exists, not_and, not_lt] at c2
    have h_subset : P ⊆ Set.Iic (max a b) := by
      intro x xh; specialize c2 x xh
      simp only [Set.mem_Iic, le_sup_iff]; grind only
    have := Set.Finite.subset (t := P) (Set.finite_Iic (max a b)) h_subset
    exact c this
  specialize card1 p hp.1.1 ?_
  · intro zp; obtain ⟨c, hc⟩ := zp
    have : p ∣ c := by
      refine Nat.dvd_of_mod_eq_zero ?_
      have := congrArg ZMod.val hc.2
      simp only [ZMod.val_zero, ZMod.val_natCast] at this
      symm; exact this
    exact hp.1.2 c hc.1 this
  have : a = b := by
    obtain ⟨e, eh⟩ := card1
    have := calc ↑a
      _ = e := eh.2 a ⟨a, hab.1, rfl⟩
      _ = ↑b := Eq.symm (eh.2 b ⟨b, hab.2.1, rfl⟩)
    exact calc
      a = (a : ZMod p).val := Eq.symm (ZMod.val_natCast_of_lt hp.2.1)
      _ = (b : ZMod p).val := congrArg ZMod.val this
      _ = b := ZMod.val_natCast_of_lt hp.2.2
  exact hab.2.2 this
