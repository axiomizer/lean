import Mathlib.Data.Real.Sqrt

theorem POTD_2507 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (eq1 : x ^ 2 + y ^ 2 + x * y = 1)
    (eq2 : y ^ 2 + z ^ 2 + y * z = 4)
    (eq3 : z ^ 2 + x ^ 2 + z * x = 5) :
    x + y + z = √(5 + 2*√3) := by
  rcases (show x^2 = (11-6*√3)/39 ∨ x^2 = (11+6*√3)/39 by grind) with c | c
  · replace c : x = √((11-6*√3)/39) := by
      symm; refine (Real.sqrt_eq_iff_mul_self_eq_of_pos hx).mpr ?_
      rw[←pow_two]; assumption
    have : y = √((20+8*√3)/39) := by
      symm; exact (Real.sqrt_eq_iff_mul_self_eq_of_pos hy).mpr (by grind)
    have := calc z < 0
      _ ↔ 4*x - 3*y < 0 := by rw[show z = 4*x - 3*y by grind]
      _ ↔ (4*x)^2 < (3*y)^2 := by grind only [sq_lt_sq₀]
      _ ↔ 168*√3+4 > 0 := by grind
      _ ↔ True := by
        simp only [gt_iff_lt, iff_true]
        refine Right.add_pos' ?_ ?_ <;> simp
    exfalso; grind
  have d : y^2 = (20-8*√3)/39 := by grind
  have e : z^2 = (164-24*√3)/39 := by grind
  rw[←show √((x+y+z)^2) = x+y+z by refine Real.sqrt_sq ?_; grind]
  refine congrArg Real.sqrt ?_; grind
