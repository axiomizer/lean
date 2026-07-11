import Mathlib.Data.Int.Init
import Mathlib.Data.Int.Order.Lemmas

theorem POTD2395 (f : ℤ → ℤ) :
    (∀ m n : ℤ, f (m + f n) = f m + n) ↔ (f = id ∨ f = fun x ↦ -x) := by
  apply Iff.intro
  · intro h
    have inj : Function.Injective f := by
      intro a b fab
      have := calc f 0 + a
        _ = f (0 + f a) := by rw[h 0 a]
        _ = f (f a)     := by simp
        _ = f (f b)     := congrArg f fab
        _ = f (0 + f b) := by simp
        _ = f 0 + b     := by rw[h 0 b]
      simp at this
      assumption
    have fzz : f 0 = 0 := by
      have := h 0 0
      simp at this
      exact inj this
    have ffnn (n : ℤ) : f (f n) = n := by
      have := h 0 n
      simp[fzz] at this
      assumption
    have fnf1 (n : ℤ) : f n = n * (f 1) := by
      induction n
      case zero => simp[fzz]
      case succ i ih => exact calc f (i+1)
        _ = f (1 + f (f i))   := by rw[add_comm, ffnn i]
        _ = (f 1) + (f i)     := h 1 (f i)
        _ = (f 1) + i * (f 1) := by rw[ih]
        _ = (1+i) * (f 1)     := by rw[one_add_mul]
        _ = (i+1) * (f 1)     := by rw[add_comm]
      case pred i ih => exact calc f (-i-1)
        _ = f 1 + f (-i-1) - f 1       := by simp
        _ = f (1 + f (f (-i-1))) - f 1 := by rw[h 1 (f (-i-1))]
        _ = f (1 + (-i-1)) - f 1       := by rw[ffnn (-i-1)]
        _ = f (-i) - f 1               := by simp
        _ = -i * f 1 - f 1             := by rw[ih]
        _ = (-i-1) * f 1               := by rw[sub_one_mul]
    have f1s : f 1 = 1 ∨ f 1 = -1 := by
      have := calc (f 1) * (f 1)
        _ = f (f 1)       := by rw[fnf1 (f 1)]
        _ = 1             := ffnn 1
      exact Int.eq_one_or_neg_one_of_mul_eq_one this
    apply Or.elim f1s
    · intro f11
      apply Or.inl
      ext n
      exact calc f n
        _ = n * (f 1) := fnf1 n
        _ = id n  := by simp[f11]
    · intro f1n1
      apply Or.inr
      ext n
      exact calc f n
        _ = n * (f 1) := fnf1 n
        _ = -n        := by simp[f1n1]
  · intro
  | Or.inl h, _, _ => simp[h]
  | Or.inr h, _, _ => simp[h]; rw[add_comm]
