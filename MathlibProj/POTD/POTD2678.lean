import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

theorem POTD_2678 (n : ℕ) (p : ZMod (2 * n) → ℤ) (hp : ∀ i, |p i - p (i + 1)| ≤ 10) :
    ∃ i, |p i - p (i+n)| ≤ 10 := by
  let diff (i : ZMod (2*n)) := p i - p (i+n)
  have recur (i : ZMod (2 * n)) (j : ℕ) (h : diff i ≤ 10 ∧ diff (i+j) ≥ -10) :
      ∃ k, |diff k| ≤ 10 := by
    induction j with | zero | succ j ih
    · simp only [Nat.cast_zero, add_zero, and_comm] at h
      exists i; exact abs_le.mpr h
    · by_cases! c : diff (i + (j+1)) ≤ 10
      · exists (i+(j+1)); apply abs_le.mpr; grind only
      · apply ih; refine ⟨h.1, ?_⟩
        exact calc diff (i+j)
          _ = p (i+j) - p (i+j+n) := rfl
          _ ≥ p (i+j+1) - p (i+j+n) - 10 := by grind only [(abs_le.mp (hp (i+j))).1]
          _ ≥ p (i+j+1) - p (i+j+n+1) - 20 := by grind only [(abs_le.mp (hp (i+j+n))).2]
          _ ≥ -10 := by
            rw[show i+j+1 = i+(j+1) by rw[add_assoc]]
            rw[show i+j+n+1 = i+(j+1)+n by grind only]
            grind only
  obtain ⟨i, hi⟩ : ∃ i, diff i ≤ 10 ∧ diff (i+n) ≥ -10 := by
    by_cases p 0 ≤ p n
    · exists 0; grind[ZMod.natCast_self (2*n)]
    · exists n; grind[ZMod.natCast_self (2*n)]
  exact recur i n hi
