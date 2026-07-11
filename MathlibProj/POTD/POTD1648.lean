import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Combinatorics.Pigeonhole

open Equiv Finset

theorem POTD_1648 {n : ℕ} [NeZero n] :
    let p (a : Perm (Fin n)) :=
      ∀ j k : Fin n, j < k → (j.val+1) * (a j + 1) ≤ (k.val+1) * (a k + 1)
    #(filter p univ) = Nat.fib (n+1) := by
  intro p
  have claim1 : ∀ a, p a → ∀ k, k.val ≤ a k + 1 := by
    intro a ha k
    cases n with | zero => exact k.elim0 | succ n
    induction k using Fin.induction with | zero | succ k ih
    · simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, le_add_iff_nonneg_left, zero_le]
    · by_contra c; simp only [Fin.val_succ, add_le_add_iff_right, not_le] at c
      specialize ha k.castSucc k.succ (by grind only [= Fin.val_castSucc, usr Fin.val_succ])
      rw[Fin.val_castSucc k] at ih ha; rw[Fin.val_succ k] at ha
      have : (k+1) * ((a k.castSucc).val + 1) < (k+1) * ((a k.succ).val + 2) := by lia
      replace := Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left this)
      simp only [Nat.succ_eq_add_one, add_le_add_iff_right, Fin.val_fin_le] at this
      replace : a k.castSucc < a k.succ := by
        by_contra c; simp only [not_lt] at c
        apply le_antisymm this at c
        apply congrArg a.symm at c
        simp only [symm_apply_apply] at c
        grind only [= Fin.val_castSucc, Fin.val_succ]
      grind only [= Fin.val_castSucc]
  have claim2 : ∀ a, p a → ∀ k, a k ≤ k.val+1 := by
    intro a ha k; by_contra c; simp only [not_le] at c
    by_cases knn : k = n-1
    · grind only
    obtain ⟨j, jh⟩ : ∃ j : Fin n, a j = k := by
      exists (a.symm k)
      exact (apply_eq_iff_eq_symm_apply a).mpr rfl
    have jh2 : j.val = k+1 := by
      apply le_antisymm (jh ▸ claim1 a ha j)
      by_contra c2; simp only [not_le] at c2
      replace c2 : j.val < k.val := by
        apply Nat.lt_of_le_of_ne (Nat.le_of_lt_succ c2)
        grind only
      have := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := {a : Fin n | a ≤ k.val})
        (t := {a : Fin n | a < k.val}) (f := a.symm) (n := 1)
      specialize this ?_ ?_
      · simp only [Fin.val_fin_le, mem_filter, mem_univ, true_and, Fin.val_fin_lt]
        intro l lh
        by_cases hlk : l = k
        · grind only [= symm_apply_apply]
        replace lh := Std.lt_of_le_of_ne lh hlk; clear hlk
        replace := claim1 a ha ((Equiv.symm a) l); simp only [apply_symm_apply] at this
        replace : ((Equiv.symm a) l) ≤ k := by lia
        grind only [= apply_symm_apply]
      · simp only [Fin.val_fin_lt, mul_one, Fin.val_fin_le]
        let s : Finset (Fin n) := {a : Fin n | a < k}
        let t : Finset (Fin n) := {a : Fin n | a = k}
        have : ({a : Fin n | a ≤ k} : Finset (Fin n)) = s ∪ t := Finset.ext_iff.mpr (by grind)
        rw[this]
        rw[Finset.card_union_eq_card_add_card.mpr (disjoint_filter.mpr (by grind))]
        simp only [lt_add_iff_pos_right, card_pos]; exists k
        simp only [mem_filter, mem_univ, and_self]
      let ⟨y, _, yh⟩ := this
      let s : Finset (Fin n) := {x ∈ {a | a ≤ k} | a.symm x = y}
      have := calc
        1 < #s := yh
        _ ≤ #({a y} : Finset (Fin n)) := by
          apply card_le_card
          intro z zh; unfold s at zh; simp at zh
          grind only [= apply_symm_apply, = mem_singleton]
        _ = 1 := card_singleton (a y)
      contradiction
    have s : (k+1).val = k.val+1 := Fin.val_add_one_of_lt' (by grind only)
    have := calc (k.val+1)*(k.val+2)
      _ < (k.val+1)*((a k).val+1) := by
        refine Nat.mul_lt_mul_of_pos_left ?_ (by apply Nat.zero_lt_succ)
        exact Nat.lt_succ_of_le c
      _ ≤ ((k+1).val+1)*((a (k+1)).val + 1) := ha k (k+1) (by grind only)
      _ = (k.val+1)*(k.val+2) := by
        rw[mul_comm, s]
        simp only [mul_eq_mul_right_iff, Nat.add_right_cancel_iff, Nat.add_eq_zero_iff,
          Fin.val_eq_zero_iff, one_ne_zero, and_false, and_self, or_false]
        grind only
    grind only
  let q (a : Perm (Fin n)) := ∀ k : Fin n, k.val-1 ≤ a k ∧ a k ≤ k.val+1
  have claim3 : filter p univ = filter q univ := by
    refine filter_inj'.mpr (fun a _ ↦ ?_)
    refine ⟨by grind, ?_⟩; intro qh j k hjk
    exact calc (j.val+1) * (a j + 1)
      _ ≤ (j.val+1) * (j.val + 2) := by
        apply Nat.mul_le_mul_left
        simp only [add_le_add_iff_right]; exact (qh j).2
      _ ≤ k.val * (k.val + 1) := by apply mul_le_mul <;> lia
      _ ≤ (k.val+1) * (a k + 1) := by
        rw[mul_comm]; apply Nat.mul_le_mul_left
        exact Nat.le_add_of_sub_le (qh k).1
  rw[claim3]; clear claim1 claim2 claim3 p
  induction n using Nat.strong_induction_on with | h n ih
  rcases n with _ | _ | n
  · unfold q; simp only [tsub_le_iff_right, IsEmpty.forall_iff, univ_unique, Perm.default_eq,
    filter_true, card_singleton, zero_add, Nat.fib_one]
  · unfold q; simp only [Nat.reduceAdd, Fin.val_eq_zero, zero_tsub, le_refl, zero_add, zero_le,
    and_self, implies_true, univ_unique, Perm.default_eq, filter_true, card_singleton, Nat.fib_two]
  let fin1 := Fin.ofNat (n+2) (n+1)
  let fin2 := Fin.ofNat (n+2) n
  have : fin1.val = n+1 := by rw[Fin.val_ofNat]; apply Nat.mod_succ
  have : fin2.val = n := Nat.mod_eq_of_lt (Nat.lt_add_of_pos_right Nat.zero_lt_two)
  rw[←Finset.card_filter_add_card_filter_not (s := filter q univ) (fun a ↦ a fin1 = fin1)]
  rw[Nat.fib_add_two, add_comm]
  apply (show ∀ a b c d : ℕ, a = b → c = d → a+c = b+d by lia)
  · have : ({a ∈ filter q univ | ¬a fin1 = fin1} : Finset _) =
           ({a : Perm (Fin (n+2)) | q a ∧ a fin1 = fin2 ∧ a fin2 = fin1} : Finset _) := by
      ext a; simp only [mem_filter, mem_univ, true_and, and_congr_right_iff]; intro ah
      refine ⟨?_, by grind only⟩; intro _
      refine ⟨by grind only, ?_⟩
      suffices a.symm fin1 = fin2 by grind only [= apply_symm_apply]
      grind only [(ah (a.symm fin1)).2, = apply_symm_apply]
    rw[this]; specialize ih n (by grind only); rw[←ih]; clear ih this
    refine Finset.card_bij ?_ ?_ ?_ ?_
    · intro a ah; simp only [mem_filter, mem_univ, true_and] at ah
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine fun i ↦ (a (i.castAdd 2)).castLT ?_
        by_contra c
        replace c : a (i.castAdd 2) = fin1 ∨ a (i.castAdd 2) = fin2 := by grind only
        rcases c with c1 | c2
        · grind only [= Fin.val_castAdd]
        · replace c2 := congrArg a.symm c2; simp only [symm_apply_apply] at c2
          replace c2 : i.castAdd 2 = fin1 := by grind only [= symm_apply_apply]
          grind only [= Fin.val_castAdd]
      · refine fun i ↦ (a.symm (i.castAdd 2)).castLT ?_
        by_contra c
        replace c : a (i.castAdd 2) = fin1 ∨ a (i.castAdd 2) = fin2 := by
          grind only [= apply_symm_apply, = Fin.val_castAdd]
        rcases c with c1 | c2
        · grind only [= Fin.val_castAdd]
        · replace c2 := congrArg a.symm c2; simp only [symm_apply_apply] at c2
          replace c2 : i.castAdd 2 = fin1 := by grind only [= symm_apply_apply]
          grind only [= Fin.val_castAdd]
      · intro i; simp only [Fin.castAdd_castLT, symm_apply_apply, Fin.castLT_castAdd]
      · intro i; simp only [Fin.castAdd_castLT, apply_symm_apply, Fin.castLT_castAdd]
    · intro a ha; simp only [mem_filter, mem_univ, true_and] at ha
      simp only [tsub_le_iff_right, mem_filter, mem_univ, coe_fn_mk, Fin.val_castLT, true_and]
      grind only [= Lean.Grind.toInt_fin, = Fin.val_castAdd]
    · intro a1 a1h a2 a2h feq
      ext k; by_cases kg : k ≥ n
      · rcases (show k = fin1 ∨ k = fin2 by grind only) <;> grind only [= mem_filter]
      simp only [ge_iff_le, not_le] at kg
      replace feq := congrArg Equiv.toFun feq; simp only at feq
      replace feq := congrFun feq (k.castLT kg)
      simp only [Fin.castAdd_castLT] at feq
      replace feq := congrArg Fin.val feq
      simp only [Fin.val_castLT] at feq
      assumption
    · intro b bh; simp only [tsub_le_iff_right, mem_filter, mem_univ, true_and] at bh
      let a : Perm (Fin (n+2)) := {
        toFun := fun i ↦ if il : i.val < n then (b (i.castLT il)).castAdd 2
          else if i = fin1 then fin2 else fin1
        invFun := fun i ↦ if il : i.val < n then (b.symm (i.castLT il)).castAdd 2
          else if i = fin1 then fin2 else fin1
        left_inv := by
          intro i; by_cases il : i.val < n
          · simp[il]
          · by_cases i = fin1 <;> grind only
        right_inv := by
          intro i; by_cases il : i.val < n
          · simp[il]
          · by_cases i = fin1 <;> grind only
      }
      exists a; refine ⟨?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]; refine ⟨?_, ?_, ?_⟩
        · intro i; by_cases il : i.val < n
          · unfold a; simp only [coe_fn_mk, il, ↓reduceDIte, Fin.val_castAdd, tsub_le_iff_right]
            exact Prod.mk_le_mk.mp (bh (i.castLT il))
          · by_cases i = fin1 <;> grind only [= coe_fn_mk]
        · unfold a; simp[show ¬fin1.val < n by grind only]
        · unfold a; simp[show ¬fin2.val < n by grind only]
      · apply Perm.ext; intro i; simp only [coe_fn_mk]; unfold a
        simp only [coe_fn_mk, Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.castLT_castAdd]
  · specialize ih (n+1) (lt_add_one (n+1)); rw[←ih]; clear ih
    refine Finset.card_bij ?_ ?_ ?_ ?_
    · intro a ah; simp only [mem_filter, mem_univ, true_and] at ah
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine fun i ↦ (a (i.castAdd 1)).castLT ?_
        by_contra _; have := (symm_apply_eq a).mpr (Eq.symm ah.2)
        replace : (i.castAdd 1) = fin1 := by grind only [= symm_apply_apply]
        grind only [= Fin.val_castAdd]
      · refine fun i ↦ (a.symm (i.castAdd 1)).castLT ?_
        by_contra _; grind only [= apply_symm_apply, = Fin.val_castAdd]
      · intro i; simp only [Fin.castAdd_castLT, symm_apply_apply, Fin.castLT_castAdd]
      · intro i; simp only [Fin.castAdd_castLT, apply_symm_apply, Fin.castLT_castAdd]
    · intro a ha; simp only [mem_filter, mem_univ, true_and] at ha
      simp only [tsub_le_iff_right, mem_filter, mem_univ, coe_fn_mk, Fin.val_castLT, true_and]
      grind only [= Lean.Grind.toInt_fin, = Fin.val_castAdd]
    · intro a1 a1h a2 a2h feq
      ext k; by_cases kf : k = fin1
      · grind only [= mem_filter]
      replace feq := congrArg Equiv.toFun feq; simp only at feq
      replace feq := congrFun feq (k.castLT (by grind only))
      simp only [Fin.castAdd_castLT] at feq
      replace feq := congrArg Fin.val feq
      simp only [Fin.val_castLT] at feq
      assumption
    · intro b bh; simp only [tsub_le_iff_right, mem_filter, mem_univ, true_and] at bh
      let a : Perm (Fin (n+2)) := {
        toFun := fun i ↦ if _ : i = fin1 then fin1 else (b (i.castLT (by lia))).castSucc
        invFun := fun i ↦ if _ : i = fin1 then fin1 else (b.symm (i.castLT (by lia))).castSucc
        left_inv := by
          intro i; by_cases il : i = fin1
          · simp[il]
          · simp[il]; grind only [= Fin.val_castSucc]
        right_inv := by
          intro i; by_cases il : i = fin1
          · simp[il]
          · simp[il]; grind only [= Fin.val_castSucc]
      }
      exists a; refine ⟨?_, ?_⟩
      · grind only [= mem_filter, = coe_fn_mk, ← mem_univ, = Fin.val_castSucc, = Fin.val_castLT]
      · apply Perm.ext; intro i; simp only [coe_fn_mk]
        grind only [= Fin.val_castLT, = coe_fn_mk, = Fin.val_castAdd, = Fin.val_castSucc]
