import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Sign

noncomputable def f (a : PNat → ℝ) (i j : PNat) := (a i + a j) / (1 + a i * a j)

lemma recip {a b : ℝ} (h : a / b > 0) : b/a > 0 := by
  refine one_div_pos.mp ?_; simp[h]

open Real

lemma sign_mul (a b : ℝ) : sign a * sign b = sign (a*b) := by
  unfold sign; rcases (lt_trichotomy a 0) with c | c | c
  <;> rcases (lt_trichotomy b 0) with d | d | d
  <;> simp[c, d, Std.not_gt_of_lt, mul_neg_of_pos_of_neg, mul_pos_of_neg_of_neg]

theorem POTD_2494 (a : PNat → ℝ) (ha1 : ∀ n, a n > 0)
    (ha2 : ∀ k l m n, k + n = m + l → f a k n = f a m l) :
    ∃ b c, b > 0 ∧ c > 0 ∧ ∀ n, b ≤ a n ∧ a n ≤ c := by
  let r := a 1 - a 2
  let s := 1 - a 1 * a 2

  have nz_denom (n m : PNat) : 1 + a n * a m ≠ 0 := by
    refine ne_of_gt ?_
    refine Right.add_pos' zero_lt_one ?_
    exact Left.mul_pos (ha1 n) (ha1 m)
  have sign_eq_helper (n : PNat) (x y : ℝ) (h : a n * x = y) : sign x = sign y := by
    unfold sign; rcases (lt_trichotomy x 0) with c | c | c
    · have := mul_neg_of_pos_of_neg (ha1 n) c
      rw[h] at this; grind
    · simp[c] at h; grind
    · have := Left.mul_pos (ha1 n) c
      rw[h] at this; grind
  have eq1 : ∀ n, s * (a n - a (n+1)) = r * (1 - a n * a (n+1)) := by
    intro n
    have fh := ha2 n 1 (n+1) 2; specialize fh rfl
    have := (div_eq_div_iff (nz_denom n 2) (nz_denom (n+1) 1)).mp fh
    linarith
  have eq2 : ∀ n, sign (r * a n - s) = sign (-s * a n + r) := by
    intro n
    have fh : a (n+1) * (r * a n - s) = (-s * a n + r) := by have := eq1 n; linarith
    exact sign_eq_helper (n+1) (r * a n - s) (-s * a n + r) fh
  have eq3 : ∀ n, n > 1 → sign (r * a n + s) = sign (s * a n + r) := by
    intro n nh
    have := calc n-1+2
      _ = (n-1+1)+1 := rfl
      _ = n+1 := by rw[PNat.sub_add_of_lt nh]
    have fh := ha2 (n-1) 1 n 2; specialize fh this;
    replace fh := (div_eq_div_iff (nz_denom (n-1) 2) (nz_denom n 1)).mp fh
    replace fh : a (n-1) * (r * a n + s) = (s * a n + r) := by linarith
    exact sign_eq_helper (n-1) (r * a n + s) (s * a n + r) fh
  clear nz_denom sign_eq_helper

  by_cases rz : r = 0
  · have ind (n : ℕ) : a (Nat.succPNat n) = a 1 := by
      induction n with | zero | succ n ih
      · rfl
      · by_cases sz : s = 0
        · have aoo : a 1 = 1 := calc a 1
            _ = √ (a 1 * a 1) := by
              symm; refine Real.sqrt_mul_self ?_
              exact Std.le_of_lt (ha1 1)
            _ = 1   := by grind
          rw[aoo]; rw[aoo] at ih
          let nn := n.succPNat; let x := a (nn + 1); change x = 1
          have := calc (x + x) / (1 + x * x)
            _ = (a nn + a (nn + 2)) / (1 + a nn * a (nn + 2)) :=
              ha2 (nn+1) (nn+2) nn (nn+1) (add_left_comm (nn + 1) nn 1)
            _ = (1 + a (nn + 2)) / (1 + a (nn + 2)) := by rw[ih]; simp
            _ = 1 := by refine (div_eq_one_iff_eq ?_).mpr rfl; grind
          replace := calc x + x
            _ = ((x + x) / (1 + x * x)) * (1 + x * x) := by
              symm; exact div_mul_cancel₀ (x + x) (by grind)
            _ = 1 + x * x := by simp[this]
          grind
        · simp[sz, rz] at eq1; specialize eq1 n.succPNat
          change a (n.succPNat + 1) = a 1; grind
    exists (a 1) / 2, a 1 + 1; and_intros
    · exact half_pos (ha1 1)
    · exact add_pos (ha1 1) Real.zero_lt_one
    · intro n
      specialize ind (PNat.natPred n); simp at ind; simp[ind]
      exact Std.le_of_lt (ha1 1)
  by_cases sz : s = 0
  · simp[sz, rz] at eq1
    have ind (n : ℕ) : a (Nat.succPNat n) = a 1 ∨ a (Nat.succPNat n) = 1 / a 1 := by
      induction n with | zero | succ n ih
      · left; rfl
      · specialize eq1 (Nat.succPNat n)
        rw[show (n+1).succPNat = n.succPNat + 1 by rfl]
        grind
    exists min (a 1) (1/(a 1)), max (a 1) (1/(a 1))
    and_intros
    · grind
    · grind
    · intro n; specialize ind (n.natPred); simp at ind; grind

  have sign_lem {a : ℝ} : a ≥ 0 ↔ sign a ≠ -1 := by
    unfold sign; rcases (lt_trichotomy a 0) with c | c | c <;> simp[c]
    simp[Std.le_of_lt c]; exact self_ne_neg.mpr (by simp)
  by_cases rs : r/s > 0
  · exists (min (r/s) (s/r)), (max (r/s) (s/r))
    and_intros
    · exact lt_inf_iff.mpr ⟨rs, recip rs⟩
    · refine lt_sup_iff.mpr ?_; left; assumption
    intro n
    have sgn : a n ≥ s/r ↔ r/s ≥ a n := calc a n ≥ s/r
      _ ↔ a n - s/r ≥ 0 := Iff.symm sub_nonneg
      _ ↔ (r/s) * (a n - s/r) ≥ 0 := Iff.symm (mul_nonneg_iff_of_pos_left rs)
      _ ↔ (1/s) * (r * a n - s) ≥ 0 := le_iff_le_of_cmp_eq_cmp (congrArg (cmp 0) (by grind))
      _ ↔ sign (1/s) * sign (r * a n - s) ≠ -1 := by rw[sign_lem, sign_mul]
      _ ↔ (1/s) * (-s * a n + r) ≥ 0 := by rw[eq2 n, sign_mul, sign_lem]
      _ ↔ r/s ≥ a n := by
        rw[show (1/s) * (-s * a n + r) = - a n + r/s by grind]
        exact le_neg_add_iff_le
    rcases (iff_iff_and_or_not_and_not.mp sgn) <;> grind
  · replace rs := Std.lt_of_le_of_ne (Std.not_lt.mp rs) (div_ne_zero rz sz)
    exists min (min (r/(-s)) ((-s)/r)) (a 1), max (max (r/(-s)) ((-s)/r)) (a 1)
    and_intros
    · refine lt_inf_iff.mpr ⟨?_, ha1 1⟩
      refine lt_inf_iff.mpr ⟨by grind, recip (by grind)⟩
    · refine lt_sup_iff.mpr ?_; right; exact ha1 1
    intro n
    by_cases ngo : n = 1
    · grind
    replace ngo : n > 1 := by by_contra c; simp at c; exact ngo c
    have sgn : a n ≥ (-s) / r ↔ r / (-s) ≥ a n := calc a n ≥ (-s) / r
      _ ↔ a n + s/r ≥ 0 := by grind
      _ ↔ (r/(-s)) * (a n + s/r) ≥ 0 := by symm; refine mul_nonneg_iff_of_pos_left (by grind)
      _ ↔ (1/(-s)) * (r * a n + s) ≥ 0 := le_iff_le_of_cmp_eq_cmp (congrArg (cmp 0) (by grind))
      _ ↔ sign (1/(-s)) * sign (r * a n + s) ≠ -1 := by rw[sign_lem, sign_mul]
      _ ↔ (1/(-s)) * (s * a n + r) ≥ 0 := by rw[eq3 n, sign_mul, sign_lem]; assumption
      _ ↔ r / (-s) ≥ a n := by
        rw[show (1/(-s)) * (s * a n + r) = r/(-s) - a n by grind]
        exact sub_nonneg
    rcases (iff_iff_and_or_not_and_not.mp sgn) <;> grind
