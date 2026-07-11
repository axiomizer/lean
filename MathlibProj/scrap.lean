import Mathlib.Data.Finset.Basic

open Finset
lemma claim1 (p : ℕ) [Fact p.Prime] :
    #{n : ZMod (p^2) | n^2+1 = 0} ≤ if p % 4 = 1 then 2 else 0 := by
  sorry
