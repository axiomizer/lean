import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.ConditionallyCompleteLattice.Group
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice

def closest_mult (j V : ℕ) : ℕ :=
  if j = 0 then 0 else
    let lower := (V / j) * j
    let upper := lower + j
    if (V - lower) < (upper - V) then lower else upper

inductive Obtainable : ℕ → ℕ → Prop
| base n         : Obtainable n 1
| replace n V j  : Obtainable n V → (1 ≤ j ∧ j ≤ n) → Obtainable n (closest_mult j V)

noncomputable def f (n : ℕ) := sSup {m : ℕ | Obtainable n m}

lemma f_bounded {n : ℕ} : BddAbove {m : ℕ | Obtainable n m} := by
  exists Nat.factorial n
  intro k kh; change (Obtainable n k) at kh
  induction kh with
  | base => exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  | replace V j ha hb ih =>
    unfold closest_mult
    simp only [Nat.ne_zero_of_lt hb.1, ↓reduceIte]
    by_cases div : j ∣ V
    · obtain ⟨k, kh⟩ := div
      subst kh
      rw[Nat.mul_div_cancel_left k hb.1]
      grind only
    suffices V / j * j + j ≤ n.factorial from by
      by_cases c : V - (V / j) * j < (V / j) * j + j - V
      · simp only [c, ↓reduceIte, ge_iff_le]
        exact Nat.le_of_add_right_le this
      · simp only [c, ↓reduceIte, ge_iff_le]; exact this
    obtain ⟨f, fh⟩ : j ∣ n.factorial := Nat.dvd_factorial hb.1 hb.2
    rw[fh]; rw[fh] at ih; clear fh
    replace ih : V < j*f := by
      refine Nat.lt_of_le_of_ne ih ?_
      by_contra; symm at this
      exact div (Dvd.intro f this)
    suffices V/j < f by grind[Nat.mul_le_mul_right j this]
    exact Nat.div_lt_of_lt_mul ih

lemma l1 {n m mod r1 r2 : ℕ} (ha : r2 ≤ n) (hb : r2 ∣ mod) (hc : r1 ≤ r2)
    (hd : 2 * r1 ≥ r2) (he : Obtainable n (mod * (m / mod) + r1)) :
    Obtainable n (mod*(m/mod) + r2) := by
  by_cases rreq : r1 = r2
  · grind only
  let base := mod * (m/mod)
  by_cases r2a : r2 = 0
  · have : r1 = 0 := by rw[r2a] at hc; exact Nat.eq_zero_of_le_zero hc
    rw[this] at he; rw[r2a]
    assumption
  have : 1 ≤ r2 := by exact Nat.one_le_iff_ne_zero.mpr r2a
  convert Obtainable.replace n (base + r1) r2 he ⟨this, ha⟩ using 1
  unfold closest_mult; simp only [r2a, ↓reduceIte]
  have l1a (a b c : ℕ) (h : b < c) : (a * c + b) / c = a := by
    have h1 := Nat.div_add_mod (a*c+b) c
    have : (a*c+b)%c = b := by exact Nat.mul_add_mod_of_lt h
    rw[this, mul_comm] at h1
    apply Nat.add_right_cancel at h1
    apply Nat.mul_right_cancel at h1
    · assumption
    · exact Nat.zero_lt_of_lt h
  have bb : (base + r1) / r2 * r2 = base := by
    replace hc : r1 < r2 := by exact Nat.lt_of_le_of_ne hc rreq
    unfold base
    obtain ⟨j, jh⟩ := hb
    nth_rewrite 1 [jh]
    rw[mul_assoc]; nth_rewrite 2 [mul_comm]
    rw[l1a (j*(m/mod)) r1 r2 hc]
    grind only
  have : ¬ base + r1 - (base + r1) / r2 * r2 < (base + r1) / r2 * r2 + r2 - (base + r1) := by
    rw[bb]
    simp only [Nat.add_sub_cancel_left, not_lt, Nat.sub_le_iff_le_add]
    grind only
  simp only [this, ↓reduceIte, Nat.add_right_cancel_iff]
  rw[bb]

theorem t1 : ∀ z, z > 0 → ∃ N, ∀ n, n ≥ N → (z ∣ f n) := by
  intro z znz
  by_cases zno : z = 1
  · exists 0; intro _ _
    simp only [zno, Nat.one_dvd]
  obtain ⟨r, rha, rhb⟩ : ∃ r : ℕ, 2^r < z ∧ 2*2^r ≥ z := by
    let s := sSup {r | 2^r < z}
    have bdd : BddAbove {r | 2^r < z} := by
      exists z; intro a ah; change 2^a < z at ah
      grind[Nat.lt_two_pow_self]
    exists s; constructor
    · refine Nat.sSup_mem ?_ bdd;
      exists 0; change 2^0 < z; grind only
    by_contra c; simp only [ge_iff_le, not_le] at c; rw[←Nat.pow_succ'] at c
    change s.succ ∈ {r | 2^r < z} at c
    have : s ≥ s.succ := by exact
      ConditionallyCompleteLattice.le_csSup {r | 2 ^ r < z} s.succ bdd c
    grind only
  let mod := z*2^r
  exists mod; intro n nh
  suffices ∀ m, ∃ l, l ≥ m ∧ z ∣ l ∧ (Obtainable n m → Obtainable n l) from by
    obtain ⟨l, lha, lhb, lhc⟩ := this (f n); clear this
    have : Obtainable n (f n) := Nat.sSup_mem ⟨1, Obtainable.base n⟩ f_bounded
    have : l ≤ f n := le_csSup f_bounded (lhc this)
    rw[Nat.le_antisymm lha this]; assumption
  intro m
  by_cases zdivm : z ∣ m
  · exists m; simp only [ge_iff_le, le_refl, imp_self, and_true, true_and]; assumption
  let base := mod * (m / mod)
  by_cases lvl0 : m%mod ≤ z
  · exists base + z; and_intros
    · unfold base; nth_rewrite 2 [←Nat.div_add_mod m mod]
      grind only
    · exists 2^r * (m/mod) + 1
      lia
    intro ob
    have zln := calc
      z ≤ mod := Nat.le_mul_of_pos_right z (Nat.two_pow_pos r)
      _ ≤ n := nh
    rw [←Nat.div_add_mod m mod] at ob
    have recur (s : ℕ) : ∀ a, a ≥ 2^(r - s) → a ≤ z → Obtainable n (base + a) →
        Obtainable n (base + z) := by
      induction s with
      | zero =>
        intro a aha ahb ahc; simp only [Nat.sub_zero, ge_iff_le] at aha
        have := calc 2 * a
          _ ≥ 2 * 2^r := Nat.mul_le_mul_left 2 aha
          _ ≥ z := rhb
        exact l1 zln (Nat.dvd_mul_right z (2 ^ r)) ahb this ahc
      | succ s ih =>
        intro a aha ahb ahc
        by_cases atest : a ≥ 2^(r-s)
        · exact ih a atest ahb ahc
        simp only [ge_iff_le, not_le] at atest
        have p2 := calc 2^(r-s)
          _ ∣ 2^r := Nat.pow_dvd_pow 2 (by simp)
          _ ∣ mod := Nat.dvd_mul_left (2 ^ r) z
        have p3 : a ≤ 2^(r-s) := by exact Nat.le_of_succ_le atest
        have p4 := calc 2*a
          _ ≥ 2 * 2^(r-(s+1)) := Nat.mul_le_mul_left 2 aha
          _ = 2 ^ (r-(s+1)+1) := by exact Eq.symm Nat.pow_succ'
          _ ≥ 2^(r-s) := Nat.pow_le_pow_right (by simp) (by grind)
        have := calc 2^(r-s)
          _ ≤ 2^r := by refine Nat.pow_le_pow_right (by simp) (by simp)
          _ ≤ z := by exact Nat.le_of_succ_le rha
          _ ≤ n := zln
        have ob1 := l1 this p2 p3 p4 ahc
        have p5 := calc 2^(r-s)
          _ ≤ 2^r := Nat.pow_le_pow_right (by simp) (by simp)
          _ ≤ z := Nat.le_of_succ_le rha
        exact ih (2^(r-s)) (by simp only [ge_iff_le, le_refl]) p5 ob1
    refine recur r (m%mod) ?_ lvl0 ob
    by_contra c; simp only [Nat.sub_self, pow_zero, ge_iff_le, not_le, Nat.lt_one_iff] at c
    have := calc
      z ∣ mod := Nat.dvd_mul_right z (2 ^ r)
      _ ∣ m := Nat.dvd_of_mod_eq_zero c
    contradiction
  simp only [not_le] at lvl0
  obtain ⟨s, sha, shb⟩ : ∃ s, z * 2^s < m % mod ∧ m % mod ≤ z * 2^(s+1) := by
    let s := sSup {s | z * 2^s < m % mod}
    exists s
    have bdd : BddAbove {s | z * 2 ^ s < m % mod} := by
      exists m%mod; intro ss ssh
      have := calc z * 2^ss
        _ < m%mod := ssh
        _ < 2^(m%mod) := Nat.lt_two_pow_self
        _ ≤ z * 2^(m%mod) := Nat.le_mul_of_pos_left (2 ^ (m % mod)) znz
      apply (Nat.mul_lt_mul_left znz).mp at this
      suffices ss < m%mod from Nat.le_of_succ_le this
      by_contra c; simp only [not_lt] at c
      replace c : 2^(m%mod) ≤ 2^ss := by refine Nat.pow_le_pow_right Nat.zero_lt_two c
      replace c := Nat.lt_of_lt_of_le this c
      simp only [lt_self_iff_false] at c
    have : z * 2 ^ s < m % mod := by
      refine Nat.sSup_mem ?_ bdd
      exists 0; simp only [Set.mem_setOf_eq, pow_zero, mul_one]
      exact lvl0
    refine ⟨this, ?_⟩
    by_contra c; simp only [not_le] at c
    replace c : s+1 ∈ {s | z * 2^s < m % mod} := Set.mem_setOf.mpr c
    have : s ≥ s+1 := by exact
      ConditionallyCompleteLattice.le_csSup {s | z * 2 ^ s < m % mod} (s + 1) bdd c
    grind only
  exists base + z * 2^(s+1)
  and_intros
  · grind only [Nat.div_add_mod m mod]
  · exists (2^r) * (m/mod) + 2^(s+1); lia
  · rw[←Nat.div_add_mod m mod]
    intro ob
    have spoleqr : s+1 ≤ r := by
      have := calc z * 2^s
        _ < m % mod := sha
        _ < mod := by
          refine Nat.mod_lt m ?_
          by_contra c; simp only [not_lt, Nat.le_zero_eq] at c; change z*2^r = 0 at c
          rcases Nat.mul_eq_zero.mp c with cas | cas
          · rw[cas] at znz; contradiction
          · have := Nat.two_pow_pos r
            rw[cas] at this; contradiction
        _ = z * 2^r := rfl
      apply (Nat.mul_lt_mul_left znz).mp at this
      replace this : s < r := by
        by_contra c; simp only [not_lt] at c
        grind only [Nat.pow_le_pow_right Nat.zero_lt_two c]
      exact Nat.succ_le_of_lt this
    have ha : z * 2^(s+1) ≤ n := by
      have := (Nat.pow_le_pow_right Nat.zero_lt_two) spoleqr
      apply (Nat.mul_le_mul_left_iff znz).mpr at this
      exact calc z * 2^(s+1)
        _ ≤ mod := this
        _ ≤ n := nh
    have hb : z * 2^(s+1) ∣ mod := by
      have : 2^(s+1) ∣ 2^r := Nat.pow_dvd_pow_iff_le_right'.mpr spoleqr
      exact (Nat.mul_dvd_mul_left z) this
    have hc : m%mod ≤ z * 2^(s+1) := by grind only
    have hd : 2 * (m%mod) ≥ z * 2^(s+1) := by
      have := Nat.mul_lt_mul_of_pos_left sha Nat.zero_lt_two
      apply Nat.le_of_succ_le at this
      rw[show 2 * (z * 2 ^ s) = z * 2^(s+1) by grind only] at this
      exact this
    exact l1 ha hb hc hd ob
