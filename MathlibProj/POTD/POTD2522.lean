import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Rat.Floor

def a : ℕ → ℚ
| 0     => 0
| (n+1) => 1 / (2*⌊a n⌋ - a n + 1)

theorem POTD_2522 : a 2024 = 13/46 := by
  have claim1 (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
    rcases n with zero | n
    · contradiction
    clear hn; induction n with | zero | succ n ih
    · simp[a]
    unfold a; apply one_div_pos.mpr
    rw[show 2*⌊a (n+1)⌋ - a (n+1) + 1 = ⌊a (n+1)⌋ + (⌊a (n+1)⌋ - a (n+1) + 1) by lia]
    apply Right.add_pos_of_nonneg_of_pos
    · simp only [Int.cast_nonneg_iff]
      exact Mathlib.Meta.Positivity.int_floor_nonneg_of_pos ih
    · grind only [Int.lt_floor_add_one (a (n + 1))]
  have claim2 (n : ℕ) (hn : n ≥ 1) : 1/(a (2*n)) = 1+1/(a n) ∧ a (2*n+1) = 1 + (a n) := by
    rcases n with zero | n
    · contradiction
    clear hn; induction n with | zero | succ n ih
    · simp only [a, Int.floor_zero, Int.cast_zero, mul_zero, sub_self, zero_add, ne_eq,
      one_ne_zero, not_false_eq_true, div_self, Int.floor_one, Int.cast_one, mul_one,
      sub_add_cancel]; refine ⟨by lia, ?_⟩
      rw[show ⌊(1/2 : ℚ)⌋ = 0 from Int.floor_eq_iff.mpr (by grind)]
      lia
    have := calc 1 / a (2*(n+1+1))
      _ = 2*⌊a (2*n+3)⌋ - a (2*n+3) + 1 := by
        rw[show 2*(n+1+1) = (2*n+3)+1 by lia]
        conv => lhs; unfold a; simp
      _ = 2*⌊a (n+1) + 1⌋ - a (n+1) := by grind only [ih.2]
      _ = 1 + (2*⌊a (n+1)⌋ - a (n+1) + 1) := by rw[Int.floor_add_one (a (n + 1))]; lia
      _ = 1 + 1 / a (n + 1 + 1) := by conv => rhs; unfold a; simp
    refine ⟨this, ?_⟩
    exact calc a (2 * (n + 1 + 1) + 1)
      _ = 1 / (2*⌊a (2*(n+2))⌋ - a (2*(n+2)) + 1) := by conv => lhs; unfold a
      _ = 1 / (2*⌊a (n+2)/(a (n+2)+1)⌋ - a (n+2)/(a (n+2)+1) + 1) := by
        rw[show a (2*(n+2)) = a (n+2) / (a (n+2)+1) by grind only]
      _ = 1 / (1 - a (n+2) / (a (n+2)+1)) := by
        suffices ⌊a (n+2)/(a (n+2)+1)⌋ = 0 by rw[this]; lia
        refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
        · exact (le_div_iff₀ (by grind)).mpr (by grind)
        · simp only [Int.cast_zero, zero_add]
          refine (div_lt_one₀ (by grind)).mpr (by grind)
      _ = 1 + a (n + 1 + 1) := by grind only
  rw[←one_div_one_div (a 2024), (claim2 1012 (by simp)).1]
  rw[(claim2 506 (by simp)).1]
  rw[(claim2 253 (by simp)).1]
  rw[(claim2 126 (by simp)).2]
  rw[←one_div_one_div (a 126), (claim2 63 (by simp)).1]
  rw[(claim2 31 (by simp)).2]
  rw[(claim2 15 (by simp)).2]
  rw[(claim2 7 (by simp)).2]
  rw[(claim2 3 (by simp)).2]
  rw[(claim2 1 (by simp)).2]
  simp[a]; lia
