import Mathlib.Data.Nat.Prime.Defs

theorem POTD_2506 (p q : ℕ) (h3 : p < q) (h4 : ¬∃ r, r.Prime ∧ p < r ∧ r < q) :
    ¬∃ r, r.Prime ∧ p+q = 2*r := by
  intro r; rcases r with ⟨r, rha, rhb⟩
  refine h4 ⟨r, rha, ?_, ?_⟩
  · exact Nat.lt_of_mul_lt_mul_left (Nat.two_mul p ▸ rhb ▸ Nat.add_lt_add_left h3 p)
  · exact Nat.lt_of_mul_lt_mul_left (Nat.two_mul q ▸ rhb ▸ Nat.add_lt_add_right h3 q)
