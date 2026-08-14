import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Prime.Defs

inductive Reachable {n : ℕ} : (ZMod n → ZMod 2) → (ZMod n → ZMod 2) → Prop
| rfl {l}       : Reachable l l
| trans {a b c} : Reachable a b → Reachable b c → Reachable a c
| apply {l} (d i : ℕ) : (_ : d ∣ n ∧ d < n) → (_ : ∀ k : ℕ, l i = l (i + d*k)) →
                  Reachable l (fun x ↦ if ∃ k : Fin n, i + d*k = x then l x + 1 else l x)

inductive Reachable' {n : ℕ} : (ZMod n → ZMod 2) → (ZMod n → ZMod 2) → Prop
| rfl {l}       : Reachable' l l
| trans {a b c} : Reachable' a b → Reachable' b c → Reachable' a c
| apply {l} (d i : ℕ) (hd : d ∣ n ∧ d < n) :
                  Reachable' l (fun x ↦ if ∃ k : Fin n, i + d*k = x then l x + 1 else l x)

lemma reachable_imp_reachable' {n : ℕ} {a b : ZMod n → ZMod 2} (h : Reachable a b) :
    Reachable' a b := by
  induction h with
  | rfl => exact Reachable'.rfl
  | trans _ _ ih1 ih2 => exact Reachable'.trans ih1 ih2
  | apply d i hd _ => exact Reachable'.apply d i hd

lemma factorize (n p : ℕ) (hp : p.Prime) : ∃ r k, n = p^r * k ∧ p.Coprime k := by sorry

open Finset in
theorem thm (n : ℕ) (hn : n > 0) :
    Reachable (fun x : ZMod n ↦ if x == 0 then 1 else 0) (fun x ↦ 1) ↔ n = 1 := by
  by_cases hno : n = 1
  · subst hno; simp only [beq_iff_eq, iff_true]
    have := Reachable.rfl (l := fun x : ZMod 1 ↦ 1)
    convert this with x; simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    exact Subsingleton.eq_zero x
  simp only [beq_iff_eq, hno, iff_false]
  by_contra c; replace c := reachable_imp_reachable' c
  induction n using Nat.strong_induction_on with | h n ih
  obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd hno
  obtain ⟨r, k, hrk⟩ := factorize n p hp.1
  by_cases hko : k = 1
  · subst hko; simp only [mul_one, Nat.coprime_one_right_eq_true, and_true] at hrk
    have := NeZero.of_pos hn
    suffices suff : ∀ f : ZMod n → ZMod 2, Reachable' f (fun x ↦ 1) →
        p ∣ #(Finset.univ.filter (fun x => f x = 1)) by
      specialize suff (fun x ↦ if x = 0 then 1 else 0) c
      simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not] at suff
      have : ({x | x = 0} : Finset (ZMod n)) = {0} := by
        grind only [= mem_filter, = mem_singleton, ← mem_univ]
      simp only [this, card_singleton, Nat.dvd_one] at suff
      have := suff ▸ hp.1; contradiction
    sorry
  suffices suff : Reachable' (fun x : ZMod k ↦ if x == 0 then 1 else 0) (fun x ↦ 1) by
    have : k < n := by
      have : 1 < p^r := by
        refine Nat.one_lt_pow ?_ (Nat.Prime.one_lt hp.1)
        by_contra cc; subst cc; simp only [pow_zero, one_mul] at hrk
        have := (Nat.Prime.coprime_iff_not_dvd hp.1).mp hrk.2
        exact this (hrk.1 ▸ hp.2)
      replace := (Nat.lt_mul_iff_one_lt_left (a := p^r) (b := k) (by grind only)).mpr this
      grind only
    specialize ih k this (by grind only) hko
    grind only
  clear ih
  sorry
