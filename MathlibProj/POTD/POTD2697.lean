import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Pairwise.Basic

def valid_grid {k : ℕ} (g : Fin k → Fin k → Fin 2) (D : Finset (Fin k → Fin 2)) : Prop :=
    (∀ i, (fun j ↦ g i j) ∈ D) ∧ (∀ j, (fun i ↦ g i j) ∈ D)

open Finset in
theorem POTD_2697 (k : ℕ) (hk : k > 0) :
    Minimal (fun m ↦ ∀ D : Finset (Fin k → Fin 2), #D ≥ m → ∃ g, valid_grid g D) (2^(k-1)) := by
  constructor
  · let inverse {k : ℕ} (d : Fin k → Fin 2) : Fin k → Fin 2 := fun i ↦ if d i = 0 then 1 else 0
    simp only; intro D hD
    by_cases hD1 : (fun _ ↦ 0) ∈ D
    · exists fun i j ↦ 0; constructor <;> grind only
    by_cases hD2 : (fun _ ↦ 1) ∈ D
    · exists fun i j ↦ 1; constructor <;> grind only
    let U := (univ : Finset (Fin k → Fin 2))
    let const : Finset (Fin k → Fin 2) := {fun _ ↦ 0, fun _ ↦ 1}
    let partition :=
      ({pair : Finset (Fin k → Fin 2) | ∃ d, pair = {d, inverse d}} : Finset _) \ {const}
    have collapse : ∀ p ∈ partition, ∀ d ∈ p, p = {d, inverse d} := by
      intro p hp d hd; unfold partition at hp
      simp only [mem_sdiff, mem_filter, mem_univ, true_and, mem_singleton] at hp
      obtain ⟨⟨x, hx⟩, hx'⟩ := hp; clear hx'; subst p
      by_cases hdx : d = x
      · subst d; rfl
      replace hdx : d = inverse x := by grind only [= mem_insert, = mem_singleton]
      subst d; clear hd
      rw[show inverse (inverse x) = x by unfold inverse; grind only]
      grind only [= mem_insert, = mem_singleton]
    have part_card : #partition = 2^(k-1) - 1 := by
      have : (partition : Set (Finset (Fin k → Fin 2))).PairwiseDisjoint id := by
        intro p1 hp1 p2 hp2 hp1p2; unfold Function.onFun; simp only [id_eq]
        intro X hX1 hX2 x hx
        suffices p1 = p2 by contradiction
        rw[collapse p1 hp1 x (mem_def.mpr (hX1 hx))]
        rw[collapse p2 hp2 x (mem_def.mpr (hX2 hx))]
      replace := Finset.card_biUnion this; simp only [id_eq] at this
      have sum_const : ∀ u ∈ partition, #u = 2 := by
        intro u hu; unfold partition at hu
        simp only [mem_sdiff, mem_filter, mem_univ, true_and, mem_singleton] at hu
        obtain ⟨⟨d, hd⟩, hd'⟩ := hu; clear hd'; subst u
        refine card_pair ?_; unfold inverse; by_contra c
        replace c := congrFun c ⟨0, hk⟩; grind only
      replace sum_const := Finset.sum_eq_card_nsmul sum_const
      have part_cover : partition.biUnion id = U \ const := by
        ext d; constructor
        · intro hd; simp only [mem_biUnion, id_eq] at hd
          obtain ⟨p, hp1, hp2⟩ := hd
          unfold U const; simp only [mem_sdiff, mem_univ, true_and]; by_contra c
          suffices p = const by
            subst p; unfold partition at hp1
            simp only [mem_sdiff, mem_filter, mem_univ, true_and, mem_singleton, not_true_eq_false,
              and_false] at hp1
          specialize collapse p hp1 d hp2; subst p; clear hp1 hp2; unfold const inverse
          by_cases cas : d = fun _ ↦ 0
          · subst d; grind only
          · replace cas : d = fun _ ↦ 1 := by grind only [= mem_insert, = mem_singleton]
            subst d; grind only [= insert_eq_of_mem, = mem_singleton, = mem_insert]
        · unfold U; simp only [mem_sdiff, mem_univ, true_and, mem_biUnion, id_eq]
          intro hd; exists {d, inverse d}; refine ⟨?_, mem_insert_self d {inverse d}⟩
          unfold partition; simp only [mem_sdiff, mem_filter, mem_univ, true_and, mem_singleton]
          refine ⟨⟨d, rfl⟩, ?_⟩; by_contra c; rw[←c] at hd
          grind only [= mem_insert]
      rw[sum_const, part_cover] at this; clear sum_const part_cover
      simp only [nsmul_eq_mul, Nat.cast_id] at this
      suffices #partition * 2 = (2^(k-1) - 1) * 2 by
        apply (Nat.mul_left_inj (show 2 ≠ 0 by simp)).mp; rw[this]
      rw[←this]; clear this
      rw[Finset.card_sdiff (t := U) (s := const)]
      unfold U; simp only [card_univ, Fintype.card_pi, Fintype.card_fin, prod_const, inter_univ]
      rw[Nat.sub_mul, Nat.two_pow_pred_mul_two hk]; simp only [one_mul]
      have : 2^(k-1) * 2 = 2^k := by exact Nat.two_pow_pred_mul_two hk
      suffices #const = 2 by rw[this]
      apply Finset.card_pair; by_contra c
      replace := congrFun c ⟨0, hk⟩; contradiction
    let pigeon_map : (Fin k → Fin 2) → Finset (Fin k → Fin 2) := fun d ↦ {d, inverse d}
    obtain ⟨x, hx, y, hy, hxy1, hxy2⟩ : ∃ x ∈ D, ∃ y ∈ D, x ≠ y ∧ pigeon_map x = pigeon_map y := by
      apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := D) (t := partition)
      · grind only [Nat.pow_pos]
      · intro d hd; unfold pigeon_map partition
        simp only [coe_sdiff, coe_filter, mem_univ, true_and, coe_singleton, Set.mem_sdiff,
          Set.mem_setOf_eq, Set.mem_singleton_iff]
        refine ⟨⟨d, rfl⟩, ?_⟩
        suffices d ∉ const by grind only [= mem_insert]
        grind only [= mem_insert, = insert_eq_of_mem, = mem_coe, = mem_singleton]
    have : y = inverse x := by
      unfold pigeon_map at hxy2
      have := hxy2 ▸ (mem_insert_self y {inverse y})
      grind only [= mem_insert, = mem_singleton]
    subst y; clear hxy1 hxy2
    exists fun i j ↦ if x i = 0 then x j else (inverse x) j
    constructor
    · intro i; simp only [Fin.isValue]
      by_cases c : x i = 0 <;> simp only [c] <;> grind only
    · intro j; simp only [Fin.isValue]
      by_cases c : x j = 0
      · convert hx; unfold inverse; grind only
      · convert hy using 1; unfold inverse; grind only
  · simp only; intro m hm hm'; clear hm'; by_contra! c
    let D := ({d | d ⟨0, hk⟩ = 0} : Finset (Fin k → Fin 2)) \ {fun _ ↦ 0}
    have dcard : #D = 2^(k-1)-1 := by
      unfold D; rw[Finset.card_sdiff]
      simp only [Fin.isValue, mem_filter, mem_univ, and_self, singleton_inter_of_mem,
        card_singleton]
      apply congrArg (· - 1)
      have : #(univ : Finset (Fin (k-1) → Fin 2)) = 2^(k-1) := by
        simp only [card_univ, Fintype.card_pi, Fintype.card_fin, prod_const]
      rw[←this]; clear this
      apply Finset.card_nbij (fun d ↦ (fun i ↦ d ⟨i+1, by grind only⟩))
      · simp only [coe_univ, Set.mapsTo_univ]
      · simp only [Fin.isValue, coe_filter, mem_univ, true_and]
        intro x hx y hy hxy; simp only at hxy
        ext i; congr
        by_cases! hi : i = ⟨0, hk⟩
        · grind only [usr Set.mem_setOf_eq]
        have := congrFun hxy ⟨i-1, by grind only [= Lean.Grind.toInt_fin]⟩
        grind only [= Set.setOf_true, = Set.setOf_false, = Lean.Grind.toInt_fin,
          = Set.mem_empty_iff_false]
      · simp only [Fin.isValue, coe_filter, mem_univ, true_and, coe_univ]
        intro y hy'; clear hy'
        have (i : Fin k) (hi : i ≠ ⟨0, hk⟩) : i-1 < k-1 := by
          grind only [= Lean.Grind.toInt_fin]
        exists fun i ↦ if _ : i = ⟨0, hk⟩ then 0 else y ⟨i-1, by grind only⟩
    obtain ⟨g, hg⟩ := hm D (by grind only [Nat.pow_pos]); clear hm c m dcard
    unfold valid_grid at hg
    have find_nz {d : Fin k → Fin 2} (hd : d ∈ D) : ∃ i, d i = 1 := by
      unfold D at hd; grind only [= mem_sdiff, = mem_singleton]
    obtain ⟨j, hj⟩ := find_nz (hg.1 ⟨0, hk⟩)
    have := hg.2 j; unfold D at this
    simp only [Fin.isValue, mem_sdiff, mem_filter, mem_univ, true_and, mem_singleton] at this
    rw[this.1] at hj; contradiction
