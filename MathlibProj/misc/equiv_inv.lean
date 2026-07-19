import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Real.Basic

open Function in
theorem thm (f : ℝ → ℝ) (hinc : Monotone f) :
    ∀ x ∈ Set.range f, f x = invFun f x → f x = x := by
  intro x h1 h2; by_cases! h3 : x ≤ f x
  · have := invFun_eq h1 ▸ hinc (h2 ▸ h3)
    exact le_antisymm this h3
  · apply Std.le_of_lt at h3
    have := invFun_eq h1 ▸ hinc (h2 ▸ h3)
    exact le_antisymm h3 this
