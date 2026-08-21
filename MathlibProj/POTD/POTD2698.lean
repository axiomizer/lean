import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Algebra.BigOperators.Intervals

open Finset

def valid {N : ℕ} (t : ZMod N → ℕ) (k : ℕ) := ∀ i, (t i ≤ 1) ∧
    (t i = 1 → ∑ j ∈ Icc 1 k, t (i-j) = ∑ j ∈ Icc 1 k, t (i+j)) ∧
    (t i = 0 → ∑ j ∈ Icc 1 k, t (i-j) ≠ ∑ j ∈ Icc 1 k, t (i+j))

lemma split_sum {N : ℕ} (t : ZMod N → ℕ) (k : ℕ) (i : ZMod N) : ∑ j ∈ Ico 0 (2*k+1), t (i+j) =
    (∑ j ∈ Icc 1 k, t (i+k-j)) + t (i+k) + (∑ j ∈ Icc 1 k, t (i+k+j)) := by
  rw[←sum_Ico_consecutive _ (m := 0) (n := k+1) (k := 2*k+1) (by grind only) (by grind only)]
  have := calc ∑ j ∈ Ico (k+1) (2*k+1), t (i+j)
    _ = ∑ j ∈ Ico 1 (k+1), t (i+k+j) := by
      symm; convert Finset.sum_Ico_add (fun j : ℕ ↦ t (i+j)) 1 (k+1) k using 2
      · apply congrArg; grind only
      · congr 1 <;> grind only
    _ = ∑ j ∈ Icc 1 k, t (i+k+j) := sum_sdiff_eq_sum_sdiff_iff.mp rfl
  simp only [this, Nat.add_right_cancel_iff]
  exact calc ∑ j ∈ Ico 0 (k+1), t (i+j)
    _ = ∑ j ∈ Ico 0 (k+1), t (i+k-j) := by
      refine sum_nbij (fun j ↦ k-j) ?_ ?_ ?_ ?_
      · grind only [= mem_Ico]
      · intro x hx y hy hxy; grind only [= mem_coe, = mem_Ico]
      · intro x hx; exists k-x; grind only [= mem_coe, = mem_Ico]
      · intro j hj; apply congrArg
        have : ((k-j : ℕ) : ZMod N) = (k-j : ZMod N) := by
          refine Nat.cast_sub ?_; grind only [= mem_Ico]
        grind only
    _ = ∑ j ∈ Icc 0 k, t (i+k-j) := sum_sdiff_eq_sum_sdiff_iff.mp rfl
    _ = ∑ j ∈ Icc 1 k, t (i+k-j) + t (i+k) := by
      rw[←show insert 0 (Icc 1 k) = Icc 0 k by grind only [= mem_Icc, = mem_insert]]
      simp only [mem_Icc, nonpos_iff_eq_zero, one_ne_zero, zero_le, and_true, not_false_eq_true,
        sum_insert, Nat.cast_zero, sub_zero, add_comm]

lemma oddity {N : ℕ} [NeZero N] (t : ZMod N → ℕ) (k : ℕ) (ht : valid t k) :
    ∀ i, Odd (∑ j ∈ Ico 0 (2*k+1), t (i+j)) := by
  intro i; rw[split_sum t k i]
  by_cases htk : t (i+k) = 1
  · grind only [= Nat.odd_iff, (ht (i + k)).2.1 htk]
  replace htk : t (i+k) = 0 := by grind only [(ht (i + k)).1]
  simp only [htk, add_zero]
  suffices ∀ t : ZMod N → ℕ, ∀ i, valid t k →
      t i = 0 → ∑ j ∈ Icc 1 k, t (i-j) < ∑ j ∈ Icc 1 k, t (i+j) →
      Odd (∑ j ∈ Icc 1 k, t (i-j) + ∑ j ∈ Icc 1 k, t (i+j)) by
    rcases Nat.lt_or_gt_of_ne ((ht (i + k)).2.2 htk) with hside | hside
    · exact this t (i+k) ht htk hside
    · let tinv := fun j ↦ t (2*(i+k) - j)
      have hr1 : ∑ j ∈ Icc 1 k, t (i+k-j) = ∑ j ∈ Icc 1 k, tinv (i+k+j) := by
        unfold tinv; congr; ext j; apply congrArg; grind only
      have hr2 : ∑ j ∈ Icc 1 k, t (i+k+j) = ∑ j ∈ Icc 1 k, tinv (i+k-j) := by
        unfold tinv; congr; ext j; apply congrArg; grind only
      rw[hr1, hr2, add_comm]
      refine this tinv (i+k) ?_ ?_ ?_
      · unfold valid tinv; intro j; refine ⟨(ht (2*(i+k)-j)).1, ?_⟩
        conv => lhs; ext; rw[eq_comm]
        conv => rhs; ext; rw[ne_comm]
        convert (ht (2*(i+k)-j)).2 using 5 <;> grind only
      · unfold tinv; rw[show 2*(i+k)-(i+k) = i+k by grind only]; exact htk
      · rw[←hr1, ←hr2]; exact hside
  clear ht htk t i; intro t i ht htk hside
  have hne : ((Icc 1 k).filter (fun j : ℕ ↦ t (i+j) = 1)).Nonempty := by
    by_contra! c; simp only [filter_eq_empty_iff, mem_Icc, and_imp] at c
    replace c : ∀ j ∈ Icc 1 k, t (i+j) = 0 := by
      intro j hj
      specialize c (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
      grind[(ht (i+j)).1]
    rw[Finset.sum_eq_zero c] at hside; contradiction
  let m := ((Icc 1 k).filter (fun j : ℕ ↦ t (i+j) = 1)).min' hne
  have hm1 : m ∈ Icc 1 k := by grind only [= mem_filter, Finset.min'_mem _ hne]
  have hm2 : t (i+m) = 1 := by grind only [= mem_filter, Finset.min'_mem _ hne]
  have := calc ∑ j ∈ Icc 1 k, t (i+j)
    _ = ∑ j ∈ Icc 1 (m-1), t (i+j) + ∑ j ∈ Icc m k, t (i+j) := by
      rw[show Icc 1 (m-1) = Ico 1 m by grind only [= nonempty_def, = mem_Ico, = mem_Icc]]
      rw[show Icc m k = Ico m (k+1) by grind only [= mem_Ico, = mem_Icc]]
      rw[show Icc 1 k = Ico 1 (k+1) by grind only [= mem_Ico, = mem_Icc]]
      symm; refine Finset.sum_Ico_consecutive _ ?_ ?_
      <;> grind only [= mem_filter, = mem_Icc]
    _ = ∑ j ∈ Icc m k, t (i+j) := by
      suffices ∑ j ∈ Icc 1 (m-1), t (i+j) = 0 by simp only [this, zero_add]
      apply Finset.sum_eq_zero
      by_contra! c; obtain ⟨nz, hnz1, hnz2⟩ := c
      replace hnz2 : t (i+nz) = 1 := by grind only [(ht (i+nz)).1]
      have : nz ∈ Icc 1 k := by grind only [= mem_Icc]
      have := calc
        m ≤ nz := by apply Finset.min'_le; grind only [= mem_filter]
        _ < m := by grind only [= mem_Icc]
      grind only
    _ = 1 + ∑ j ∈ Icc (m+1) k, t (i+j) := by
      have : Icc m k = insert m (Icc (m+1) k) := by
        grind only [= nonempty_def, = mem_Icc, = mem_insert]
      grind only [= sum_insert', = mem_Icc]
    _ ≤ 1 + ∑ j ∈ Icc (m+1) (m+k), t (i+j) := by
      apply Nat.add_le_add_iff_left.mpr
      exact sum_le_sum_of_ne_zero (by grind only [= mem_Icc])
    _ = 1 + ∑ j ∈ Icc 1 k, t (i+m+j) := by
      apply congrArg (1 + ·)
      iterate 2 rw[←Ico_add_one_right_eq_Icc]
      rw[add_comm, show m+k+1 = k+1+m by lia]
      rw[←Finset.sum_Ico_add (fun j : ℕ ↦ t (i+j)) 1 (k+1) m]
      congr; ext j; apply congrArg t; grind only
    _ = 1 + ∑ j ∈ Icc 1 k, t (i+m-j) := by
      apply congrArg (1 + ·)
      rw[(ht (i+m)).2.1 hm2]
    _ = 1 + ∑ j ∈ Icc 1 (m-1), t (i+m-j) + ∑ j ∈ Icc m k, t (i+m-j) := by
      nth_rewrite 1 [add_assoc]; apply congrArg (1 + ·)
      iterate 3 rw[←Ico_add_one_right_eq_Icc]
      symm; rw[show m-1+1 = m by grind only [= mem_Icc]]
      apply Finset.sum_Ico_consecutive <;> grind only [= mem_Icc]
    _ = 1 + ∑ j ∈ Icc m k, t (i+m-j) := by
      suffices ∑ j ∈ Icc 1 (m-1), t (i+m-j) = 0 by
        simp only [this, add_zero]
      apply Finset.sum_eq_zero
      by_contra! c; obtain ⟨nz, hnz1, hnz2⟩ := c
      replace hnz2 : t (i+m-nz) = 1 := by grind only [(ht (i+m-nz)).1]
      have : m - nz ∈ Icc 1 k := by grind only [= mem_Icc]
      have := calc
        m ≤ m - nz := by
          apply Finset.min'_le
          simp only [mem_filter, mem_Icc, tsub_le_iff_right]
          refine ⟨by grind only [= mem_Icc], ?_⟩
          have : i+m-nz = i+(m-nz : ℕ) := by
            suffices (m-nz : ZMod N) = (m-nz : ℕ) by grind only
            exact Eq.symm (Nat.cast_sub (by grind only [= mem_Icc]))
          rw[←this]; assumption
        _ < m := by grind only [= mem_Icc]
      grind only
    _ = 1 + t i + ∑ j ∈ Icc (m+1) k, t (i+m-j) := by
      nth_rewrite 1 [add_assoc]; apply congrArg (1 + ·)
      have : Icc m k = insert m (Icc (m+1) k) := by
        grind only [= nonempty_def, = mem_Icc, = mem_insert]
      nth_rewrite 2 [show i = i+m-m by grind only]
      grind only [= sum_insert', = mem_Icc]
    _ = 1 + ∑ j ∈ Icc (m+1) k, t (i+m-j) := by simp only [htk, add_zero]
    _ ≤ 1 + ∑ j ∈ Icc (m+1) (m+k), t (i+m-j) := by
      apply Nat.add_le_add_iff_left.mpr
      exact sum_le_sum_of_ne_zero (by grind only [= mem_Icc])
    _ = 1 + ∑ j ∈ Icc 1 k, t (i-j) := by
      apply congrArg (1 + ·)
      iterate 2 rw[←Ico_add_one_right_eq_Icc]
      rw[add_comm, show m+k+1 = k+1+m by lia]
      rw[←Finset.sum_Ico_add (fun j : ℕ ↦ t (i+m-j)) 1 (k+1) m]
      congr; ext j; apply congrArg t; grind only
  grind only [= Nat.odd_iff]

lemma claim4 (k N : ℕ) (hN : N > 2 * k + 1) [NeZero N] :
    (∀ (t : ZMod N → ℕ), valid t k → ∀ (i : ZMod N), t i = 1) → N.Coprime (2 * k + 1) := by
  intro h; by_contra! c
  let d := N.gcd (2*k+1)
  change (d ≠ 1) at c
  let t : ZMod N → ℕ := fun i ↦ if ∃ x, d*x = i then 1 else 0
  suffices valid t k by
    specialize h t this 1
    unfold t at h; simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not] at h
    replace : ZMod.val (1 : ZMod N) = 1 := ZMod.val_one'' (by grind only)
    have := (ZMod.isUnit_iff_coprime _ _).mp (isUnit_iff_exists_inv.mpr h)
    grind only
  intro i; and_intros
  · unfold t; split <;> trivial
  · intro ht; congr; ext j; unfold t
    suffices (∃ x, d*x = i+j) ↔ (∃ x, d*x = i-j) by split <;> grind only
    constructor; all_goals
    · intro hd; obtain ⟨x1, hx1⟩ := hd
      unfold t at ht
      simp only [ite_eq_left_iff, not_exists, zero_ne_one, imp_false, not_forall,
        Decidable.not_not] at ht
      obtain ⟨x2, hx2⟩ := ht
      exists (2*x2 - x1); grind only
  · intro hti; by_contra cc
    suffices ∀ i, Odd (∑ j ∈ Ico 0 (2*k+1), t (i+j)) by
      replace := split_sum t k (i-k) ▸ this (i-k)
      simp only [sub_add_cancel, hti, add_zero, cc] at this
      grind only [= Nat.odd_iff]
    clear hti cc i c h; intro i
    obtain ⟨x, hdx⟩ : d ∣ 2*k+1 := Nat.gcd_dvd_right N (2 * k + 1)
    have : (range x).biUnion (fun i ↦ Ico (d * i) (d * (i + 1))) = Ico 0 (2*k+1) := by
      ext b
      simp only [mem_biUnion, mem_range, mem_Ico, Nat.Ico_zero_eq_range, Order.lt_add_one_iff]
      constructor
      · intro hb; obtain ⟨i, hi⟩ := hb
        have := calc
          b+1 ≤ d*(i+1) := by grind only
          _ ≤ d*x := by apply Nat.mul_le_mul_left; grind only
          _ = 2*k+1 := by rw[hdx]
        grind only
      · intro hb; exists b/d; and_intros
        · suffices d*(b/d) < d*x from Nat.lt_of_mul_lt_mul_left this
          exact calc d*(b/d)
            _ ≤ b := Nat.mul_div_le b d
            _ < d*x := by grind only
        · exact Nat.mul_div_le b d
        · simp only [mul_add, mul_one]
          nth_rewrite 1 [←Nat.div_add_mod b d]; simp only [add_lt_add_iff_left]
          refine Nat.mod_lt b ?_; grind only
    rw[←this]
    have disj : Set.PairwiseDisjoint (range x) (fun i ↦ Ico (d*i) (d*(i+1))) := by
      intro r hr s hs hrs; unfold Function.onFun; simp only
      refine disjoint_left.mpr ?_; intro a ha
      rcases (show r+1 ≤ s ∨ r ≥ s+1 by grind only) with hcas | hcas
      <;> grind [Nat.mul_le_mul_left d hcas]
    replace := Finset.sum_biUnion (f := fun (j : ℕ) ↦ t (i+j)) disj
    rw[this]
    suffices ∀ x1 ∈ range x, ∑ j ∈ Ico (d*x1) (d*(x1+1)), t (i+j) = 1 by
      simp only [Finset.sum_eq_card_nsmul this, card_range, smul_eq_mul, mul_one]
      replace : x ∣ 2*k+1 := by exists d; rw[hdx, mul_comm]
      apply Odd.of_dvd_nat ?_ this
      grind only [= Nat.odd_iff]
    suffices ∀ x1 ∈ range x, #({x ∈ Ico (d*x1) (d * (x1 + 1)) | t (i + x) = 1} : Finset ℕ) = 1 by
      intro x1 hx1; specialize this x1 hx1
      rw[←Finset.sum_filter_ne_zero]
      conv =>
        lhs; congr; congr; intro a
        rw[show t (i+a) ≠ 0 ↔ t (i+a) = 1 by unfold t; split <;> trivial]
      have hfilter : ∀ x ∈ Finset.filter (fun x : ℕ ↦ t (i + x) = 1) (Ico (d*x1) (d * (x1 + 1))),
          t (i + x) = 1 := by
        unfold t; simp only [ite_eq_left_iff, not_exists, zero_ne_one, imp_false, not_forall,
          Decidable.not_not, mem_filter, mem_Ico, and_imp, imp_self, implies_true]
      rw[Finset.sum_eq_card_nsmul hfilter]
      simp only [this, smul_eq_mul, mul_one]
    have hle : ∀ x1 ∈ range x, #({x ∈ Ico (d*x1) (d*(x1+1)) | t (i+x) = 1} : Finset ℕ) ≤ 1 := by
      intro x1 hx1; unfold t; by_contra! hc
      obtain ⟨m1, hm1, m2, hm2, hm1m2⟩ := Finset.one_lt_card.mp hc
      simp only [ite_eq_left_iff, not_exists, zero_ne_one, imp_false, not_forall, Decidable.not_not,
        mem_filter, mem_Ico] at hm1 hm2
      obtain ⟨j1, j1h⟩ := hm1.2
      obtain ⟨j2, j2h⟩ := hm2.2
      have : m1-m2 = d*(j1-j2) := by grind only
      replace : m1 = d*(j1-j2) + m2 := by grind only
      apply congrArg ZMod.val at this; rw[ZMod.val_add] at this
      simp only [ZMod.val_natCast, Nat.add_mod_mod] at this
      obtain ⟨s, hs⟩ := Nat.ModEq.dvd this; clear this
      rw[ZMod.val_mul d (j1-j2)] at hs
      simp only [ZMod.val_natCast, Nat.mod_mul_mod, Nat.cast_add, Int.natCast_emod, Nat.cast_mul,
        ZMod.natCast_val] at hs
      rw[Int.emod_def] at hs
      obtain ⟨z, hz⟩ : ∃ z, z*(d:ℤ) = (m2:ℤ)-(m1:ℤ) := by
        obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (m2 : ℤ) - (m1 : ℤ) = (d : ℤ)*u + (N : ℤ)*v := by
          exists (-(j1-j2).cast), ((d : ℤ)*(j1 - j2).cast / (N : ℤ) + s)
          grind only
        obtain ⟨y, hy⟩ := Nat.gcd_dvd_left N (2 * k + 1)
        exists (u+y*v)
        grind only [show d * y = (N : ℤ) by grind only]
      have habs : abs ((m2:ℤ)-(m1:ℤ)) ≥ d := by
        by_cases hz1 : z > 0
        · suffices (m2:ℤ)-(m1:ℤ) ≥ d by grind only
          rw[←hz]
          replace hz1 : z ≥ 1 := Int.le_of_sub_one_lt hz1
          have := Int.mul_le_mul_of_nonneg_right hz1 (Int.natCast_nonneg d)
          grind only
        by_cases hz2 : z < 0
        · suffices (m2:ℤ)-(m1:ℤ) ≤ -d by grind only
          rw[←hz]
          replace hz2 : z ≤ -1 := Int.add_le_zero_iff_le_neg.mp hz2
          have := Int.mul_le_mul_of_nonneg_right hz2 (Int.natCast_nonneg d)
          grind only
        grind only
      grind only [= abs.eq_1, = max_def]
    intro b hb
    suffices suff : ∃ x, x ∈ ({x ∈ Ico (d * b) (d * (b + 1)) | t (i + ↑x) = 1} : Finset ℕ) by
      obtain ⟨x, hx⟩ := suff
      have := card_ne_zero_of_mem hx
      grind only
    by_cases hdd : d ∣ i.val
    · obtain ⟨z, hz⟩ := hdd
      exists (d*b)
      unfold t; simp only [ite_eq_left_iff, not_exists, zero_ne_one, imp_false, not_forall,
        Decidable.not_not, mem_filter, mem_Ico, Std.le_refl, true_and, Nat.cast_mul]
      refine ⟨by grind only, ?_⟩
      exists (z+b); rw[mul_add, add_left_inj, ←Nat.cast_mul, ←hz, ZMod.natCast_zmod_val]
    exists (d*(b+1) - i.val % d)
    unfold t; simp only [ite_eq_left_iff, not_exists, zero_ne_one, imp_false, not_forall,
      Decidable.not_not, mem_filter, mem_Ico, tsub_lt_self_iff, Order.lt_add_one_iff, zero_le,
      mul_pos_iff_of_pos_right]
    have hiv : i.val % d < d := by refine Nat.mod_lt i.val ?_; grind only
    and_intros
    · rw[mul_add, mul_one]
      grind only
    · grind only
    · by_contra c; replace c : i.val % d = 0 := by grind only
      exact hdd (Nat.dvd_of_mod_eq_zero c)
    · exists ((b+1) + ((i.val/d : ℕ) : ZMod N))
      rw[Nat.cast_sub (by grind)]
      rw [show ((d*(b+1) : ℕ) : ZMod N) = (d*(b+1) : ZMod N) by grind only]
      suffices (i : ZMod N) = d*((i.val / d : ℕ) : ZMod N) + (i.val % d : ℕ) by grind only
      have := Nat.div_add_mod i.val d
      apply congrArg (Nat.cast (R := ZMod N)) at this
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id_eq] at this
      symm; assumption

theorem POTD_2698 (k N : ℕ) (hN : N > 2 * k + 1) :
    (∀ t : ZMod N → ℕ, valid t k → ∀ i, t i = 1) ↔ (N.Coprime (2*k+1)) := by
  have nzn : NeZero N := NeZero.of_gt hN
  refine ⟨claim4 k N hN, ?_⟩; intro h t ht
  have periodic : ∀ i, t i = t (i + (2*k+1)) := by
    intro i
    let middlesum := ∑ j ∈ Ico 1 (2*k+1), t (i+j)
    have o1 : ∑ j ∈ Ico 0 (2*k+1), t (i+j) = t i + middlesum := by
      have := Finset.sum_eq_sum_Ico_succ_bot (a := 0) (b := 2*k+1)
        (Nat.zero_lt_succ (2 * k)) (fun j ↦ t (i + j))
      simp only [Nat.cast_zero, add_zero, zero_add] at this
      exact this
    replace o1 := o1 ▸ oddity t k ht i
    have o2 : ∑ j ∈ Ico 0 (2*k+1), t (i+1+j) = middlesum + t (i+(2*k+1)) := by
      have : ∑ j ∈ Ico 0 (2 * k + 1), t (i + 1 + j) =
          ∑ j ∈ Ico 0 (2 * k + 1), t (i + j + 1) := by
        congr; ext x; apply congrArg; grind only
      rw[this]
      have := Finset.sum_Ico_succ_top (a := 0) (b := 2*k)
        (Nat.zero_le (2 * k)) (fun j ↦ t (i+j+1))
      rw[this]
      rw[show i+((2*k : ℕ) : ZMod N)+1 = i+(2*k+1 : ZMod N) by grind only]
      simp only [Nat.add_right_cancel_iff]
      unfold middlesum
      have := Finset.sum_Ico_add' (fun j : ℕ ↦ t (i + j)) 0 (2*k) 1
      simp only [Nat.cast_add, Nat.cast_one, zero_add] at this
      rw[←this]; congr; ext x; apply congrArg; grind only
    replace o2 := o2 ▸ oddity t k ht (i+1)
    have : Even (t i + t (i+(2*k+1))) := by grind only [= Nat.odd_iff, = Nat.even_iff]
    grind [(ht i).1, (ht (i+(2*k+1))).1]
  have periodic' : ∀ i n, t i = t (i + n * (2*k+1)) := by
    intro i
    suffices ∀ n : ℕ, t i = t (i + n * (2*k+1)) by
      intro n; rw[←ZMod.natCast_zmod_val n]; exact this n.val
    intro n; induction n with | zero | succ n ih
    · simp only [Nat.cast_zero, zero_mul, add_zero]
    · rw[Nat.cast_add_one, add_mul, one_mul, ←add_assoc, ←periodic (i + n * (2*k+1))]
      exact ih
  obtain ⟨i, hi⟩ : ∃ i, t i = 1 := by
    by_contra! c
    replace c : ∀ i, t i = 0 := by intro i; grind only [(ht i).1]
    replace ht := (ht 0).2.2 (c 0)
    grind only
  intro j
  obtain ⟨inv, hinv⟩ : ∃ inv : ZMod N, inv * (2*k+1) = 1 := by
    obtain ⟨u, _⟩ := (ZMod.isUnit_iff_coprime _ _).mpr (Nat.coprime_comm.mp h)
    exists u⁻¹; simp only [ZMod.inv_coe_unit, Units.inv_mul_eq_one]; grind only
  rw[←hi, periodic' i ((j-i)*inv), mul_assoc, hinv]; simp only [mul_one, add_sub_cancel]
