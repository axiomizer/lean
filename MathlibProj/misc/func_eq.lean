import Mathlib.Data.Int.Init
import Mathlib.Tactic.Linarith

theorem thm (f : ℤ → ℤ)
    (hf : ∀ x y : ℤ, f (x+y) + f (x*y-1) = f x * f y + 2) :
    f 45 = 2026 := by
  have plug := hf 0 (-1); simp at plug
  have f0 : f 0 = 1 := by
    by_contra c
    have : f 0 - f (-1) = (f 0 * f 0 + 2) - (f 0 * f (-1) + 2) := by
      simp[←(hf 0 0), ←plug]
    replace : (f 0 - f (-1)) * (f 0 - 1) = 0 := by linarith
    simp at this; rcases this with c1 | c2
    · replace c1 : f (-1) = f 0 := by linarith
      rw[c1] at plug
      have := calc
        0 ≤ (f 0 - 1) * (f 0 - 1) := by apply mul_self_nonneg
        _ = -1                    := by linarith
      contradiction
    · replace c2 : f 0 = 1 := by linarith
      contradiction
  have fn1 : f (-1) = 2 := by rw[f0] at plug; linarith
  clear plug
  have fn2 : f (-2) = 5 := by
    have := hf (-1) (-1)
    simp[f0, fn1] at this; linarith
  have f1 : f 1 = 2 := by
    have := hf (-1) 1
    simp[f0, fn1, fn2] at this; linarith
  have recur : ∀ x, f x = 2 * f (x-1) - f (x-2) + 2 := by
    intro x; specialize hf (x-1) 1
    simp[f1] at hf
    have : x - 1 - 1 = x - 2 := by linarith
    rw[this] at hf
    linarith
  clear fn1 fn2 hf
  have closed : ∀ x, 0 ≤ x → f x = x * x + 1 := by
    intro x
    induction x using Int.strongRec (m := 2) with | lt n hn | ge n hn ih
    · intro np
      by_cases no : n = 1
      · simp[no, f1]
      have : n = 0 := by grind
      simp[this, f0]
    · intro _; rw[recur n]
      have : n-1 < n ∧ 0 ≤ n-1 := by grind
      rw[ih (n-1) this.left this.right]
      replace : n-2 < n ∧ 0 ≤ n-2 := by grind
      rw[ih (n-2) this.left this.right]
      linarith
  specialize closed 45 (Int.zero_le_ofNat 45)
  simp[closed]
