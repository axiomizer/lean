import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs

def Zp := {n : ℕ // n ≠ 0}
def one : Zp := ⟨1, Nat.one_ne_zero⟩

theorem POTD2409 (f : Zp → Zp) :
    (∀ m n : Zp, (m.val)^2+(f n).val ∣ m.val * (f m).val + n.val) ↔ f = id := by
  apply Iff.intro
  · intro h
    have fndn (n : Zp) : (f n).val ∣ n.val := by
      have : (f n).val ∣ (f n).val^2 + (f n).val := by rw[Nat.pow_two]; simp[Nat.dvd_mul_left]
      have hh : (f n).val ∣ (f n).val * (f (f n)).val + n.val := Nat.dvd_trans this (h (f n) n)
      have : (f n).val ∣ (f n).val * (f (f n)).val := by simp[Nat.dvd_mul_right]
      exact (Nat.dvd_add_iff_right this).mpr hh
    have f11 : (f one).val = 1 := by
      have := fndn one
      simp[one] at this; exact this
    have fngen (n : Zp) : (f n).val ≥ n.val := by
      have dv := h n one
      simp[f11] at dv; simp[one] at dv; rw[Nat.pow_two] at dv
      have : 0 < n.val * (f n).val + 1 := by simp
      have le := (Nat.le_of_dvd this) dv
      simp at le
      exact (Nat.le_of_mul_le_mul_left le) (Nat.zero_lt_of_ne_zero n.property)
    have fnen (n : Zp) : (f n).val = n.val := by
      have := Nat.le_of_dvd (Nat.zero_lt_of_ne_zero n.property) (fndn n)
      exact Nat.le_antisymm this (fngen n)
    ext n; simp
    exact SetCoe.ext_iff.mp (fnen n)
  · intro h m n
    simp[h, Nat.pow_two]
