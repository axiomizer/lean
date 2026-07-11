import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Real.Sqrt

lemma fin_cast_mul (a b n : ℕ) [NeZero n] :
    Fin.ofNat n (a*b) = (Fin.ofNat n a) * (Fin.ofNat n b) := by
  refine Fin.eq_of_val_eq ?_
  unfold HMul.hMul; unfold instHMul; unfold Mul.mul; unfold Fin.instMul; unfold Fin.mul
  simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mul_mod_mod, Nat.mod_mul_mod]
  unfold HMul.hMul; unfold instHMul; unfold Mul.mul; simp

lemma l1 {n : ℕ} [NeZero n] (h1 : n % 3 = 1) (h2 : n ≥ 3) : 3 * Fin.ofNat n (n/3-1) = -4 := by
  have : (3 : Fin n) = Fin.ofNat n 3 := Fin.eq_of_val_eq rfl
  rw[this]
  rw[←fin_cast_mul 3 (n/3-1)]
  have : 3 * (n/3-1) = n-4 := by lia
  rw[this]
  refine Fin.eq_of_val_eq ?_
  simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.self_sub_mod]
  unfold Fin.val; unfold Neg.neg; unfold Fin.neg; simp only [Fin.coe_ofNat_eq_mod]
  by_cases nf : n = 4
  · simp[nf]
  have : 4%n = 4 := by refine Nat.mod_eq_of_lt ?_; lia
  rw[this]; symm; exact Nat.self_sub_mod n 4

lemma l2 {n : ℕ} [NeZero n] (h1 : n % 3 = 2) (h2 : n ≥ 3) : 3 * Fin.ofNat n (n/3) = -2 := by
  rw[show (3 : Fin n) = Fin.ofNat n 3 from Fin.eq_of_val_eq rfl, ←fin_cast_mul]
  rw[show 3*(n/3) = n-2 by lia]
  refine Fin.eq_of_val_eq ?_
  simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.self_sub_mod]
  unfold Fin.val; unfold Neg.neg; unfold Fin.neg; simp only [Fin.coe_ofNat_eq_mod]
  simp[show 2%n = 2 from Nat.mod_eq_of_lt h2]

lemma l3 {n : ℕ} [NeZero n] (a : Fin n) (h : a.val < n / 3) : (a*3).val = a.val*3 := by
  unfold HMul.hMul; unfold instHMul; unfold Mul.mul; unfold Fin.instMul; unfold Fin.mul
  simp only [Nat.mul_mod_mod]
  suffices a.val * 3 % n = a.val * 3 from by rw[this]; rfl
  refine Nat.mod_eq_of_modEq rfl ?_
  replace h := Nat.mul_lt_mul_of_pos_right (k := 3) h (by simp)
  lia

open Finset

lemma l4 {n : ℕ} [NeZero n] {x : Fin n → NNReal} {i₀ : Fin n} (hn : n ≥ 3) (r : Fin n)
    (rh : r.val < 3) :
    ∑ k with k.val < n/3, x (i₀ + 3 * k + r) =
    ∑ k ∈ {x : Fin n | x.val < n/3*3} with k % 3 = r, x (i₀ + k) := by
  have help (a : Fin n) (h : a.val < n/3) : (a*3+r).val = a.val*3+r.val := by
    unfold HMul.hMul instHMul Mul.mul Fin.instMul Fin.mul;
    simp only [Fin.coe_ofNat_eq_mod, Nat.mul_mod_mod]
    unfold HAdd.hAdd instHAdd Add.add Fin.instAdd Fin.add;
    simp only [Nat.mod_add_mod]
    change (a.val*3+r.val)%n = a.val*3+r.val
    exact Nat.mod_eq_of_lt (by lia)
  have help2 : n = 3 ∨ 3%n = 3 := by
    by_cases n = 3
    · left; assumption
    right; exact Nat.mod_eq_of_lt (by grind only)
  refine sum_bij (M := NNReal) (fun k _ ↦ k*3+r) ?_ ?_ ?_ (by grind only)
  · intro a ha; simp only [mem_filter, mem_univ, true_and]
    simp only [mem_filter, mem_univ, true_and] at ha
    constructor
    · rw[help a ha]
      replace ha := Nat.le_sub_one_of_lt ha
      replace ha := Nat.mul_le_mul_right 3 ha
      replace ha := Nat.add_le_add_right ha r.val
      suffices (n/3-1)*3+r.val < (n/3)*3 from Nat.lt_of_le_of_lt ha this
      grind only
    · unfold HMod.hMod; unfold instHMod; unfold Mod.mod; unfold Fin.instMod; unfold Fin.mod
      simp only [Fin.coe_ofNat_eq_mod]
      refine Fin.eq_of_val_eq ?_; simp only
      rcases help2 with n3 | n3
      · simp only [show 3 % n = 0 by simp [n3], Nat.mod_zero]; lia
      rw[help a ha]; lia
  · intro a ha b hb; simp only; intro hab
    simp only [mem_filter, mem_univ, true_and] at ha
    simp only [mem_filter, mem_univ, true_and] at hb
    replace hab := Fin.val_eq_of_eq hab
    simp only [help a ha, help b hb, Nat.add_right_cancel_iff, mul_eq_mul_right_iff,
      OfNat.ofNat_ne_zero, or_false] at hab
    exact Fin.eq_of_val_eq hab
  · intro b bh; simp only [mem_filter, mem_univ, true_and] at bh
    exists (b/3); exists by grind only [= mem_filter, ← mem_univ]
    grind only [usr Fin.isLt, = Lean.Grind.toInt_fin]

noncomputable def f {n : ℕ} [NeZero n] (x : Fin n → NNReal) (i : Fin n) :=
  x i + NNReal.sqrt (x (i+1) * x (i+2))
noncomputable def maxf (n : ℕ) [NeZero n] (x : Fin n → NNReal) :=
  (Finset.image (f x) Finset.univ).max' (by simp)
theorem POTD_2490 {n : ℕ} [NeZero n] (hn : n ≥ 3) :
    Minimal (maxf n '' (fun x ↦ ∑ i, x i = 1)) (1 / (2*n/3 : ℕ)) := by
  let m : NNReal := 1 / (2*n/3 : ℕ)
  have oln : 1%n = 1 := Nat.mod_eq_of_lt (by grind only)
  have tln : 2%n = 2 := Nat.mod_eq_of_lt (by grind only)
  and_intros
  · let w (i : Fin n) := if i.val % 3 = 0 then 0 else m
    exists w; and_intros
    · change ∑ i, w i = 1; unfold w
      let s : Finset (Fin n) := {i | i.val % 3 = 0}
      let t : Finset (Fin n) := {i | ¬i.val % 3 = 0}
      have h1 : ∑ i ∈ s, w i = 0 := by
        convert ← Finset.sum_eq_card_nsmul _
        · exact nsmul_zero #{i : Fin n | i.val % 3 = 0}
        · unfold s; intro a ha; simp at ha; simp [w, ha]
      have h2 : ∑ i ∈ t, w i = #t • m := by
        unfold t; apply Finset.sum_eq_card_nsmul
        intro a ha; simp at ha; simp [w, ha]
      have h3 : #t = 2 * n / 3 := by
        have comp : #(s ∪ t) = #s + #t := by
          refine card_union_of_disjoint ?_
          exact disjoint_filter_filter_not univ univ fun i : Fin n ↦ i.val % 3 = 0
        rw[filter_union_filter_not_eq (fun i : Fin n ↦ i.val % 3 = 0) univ, card_fin n] at comp
        suffices #s = (n+2)/3 by lia
        refine card_eq_of_bijective (fun i ↦ fun _ ↦ Fin.ofNat n (i * 3)) ?_ ?_ ?_
        · intro a ah; unfold s at ah; simp only [mem_filter, mem_univ, true_and] at ah
          let ⟨j, jh⟩ := Nat.dvd_of_mod_eq_zero ah
          exists j; exists by have := jh ▸ a.isLt; lia
          simp only [Fin.ofNat_eq_cast]
          refine Fin.eq_of_val_eq ?_
          simp only [Fin.val_natCast]; rw[jh, mul_comm]
          exact Nat.mod_eq_of_lt (jh ▸ a.isLt)
        · intro i ih; unfold s
          simp only [Fin.ofNat_eq_cast, mem_filter, mem_univ, Fin.val_natCast, true_and]
          rw[show i*3%n = i*3 by refine Nat.mod_eq_of_lt (by lia)]; lia
        · intro i j ih jh; simp only [Fin.ofNat_eq_cast]; intro ijh
          replace ijh := Fin.val_eq_of_eq ijh; simp only [Fin.val_natCast] at ijh
          rw[show i*3%n = i*3 by refine Nat.mod_eq_of_lt (by lia)] at ijh
          rw[show j*3%n = j*3 by refine Nat.mod_eq_of_lt (by lia)] at ijh
          lia
      rw [← sum_filter_add_sum_filter_not _ fun i : Fin n ↦ i.val % 3 = 0, h1, h2, h3]
      simp only [nsmul_eq_mul, zero_add]
      refine mul_one_div_cancel (Nat.cast_ne_zero.mpr ?_)
      omega
    · refine (Finset.max'_eq_iff _ _ _).mpr ⟨?_, fun b bh ↦ ?_⟩
      · simp only [mem_image, mem_univ, true_and]
        exists 0; unfold f w m
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceIte, zero_add, oln, Nat.one_mod,
          one_ne_zero, tln, Nat.mod_succ, OfNat.ofNat_ne_zero, NNReal.sqrt_mul_self]
      · simp only [mem_image, mem_univ, true_and] at bh
        rcases bh with ⟨i, rfl⟩
        unfold f w m
        by_cases c1 : (i.val % 3 = 0) <;> simp only [c1, ↓reduceIte]
        <;> by_cases c2 : ((i+1).val % 3 = 0) <;> simp only [c2, ↓reduceIte]
        <;> by_cases c3 : ((i+2).val % 3 = 0) <;> simp only [c3, ↓reduceIte]
        · simp only [mul_zero, NNReal.sqrt_zero, add_zero, one_div, zero_le]
        · simp only [one_div, zero_mul, NNReal.sqrt_zero, add_zero, zero_le]
        · simp only [one_div, mul_zero, NNReal.sqrt_zero, add_zero, zero_le]
        · simp only [one_div, NNReal.sqrt_mul_self, zero_add, le_refl]
        · simp only [one_div, mul_zero, NNReal.sqrt_zero, add_zero, le_refl]
        · simp only [one_div, zero_mul, NNReal.sqrt_zero, add_zero, le_refl]
        · simp only [one_div, mul_zero, NNReal.sqrt_zero, add_zero, le_refl]
        exfalso; clear w m
        unfold HAdd.hAdd instHAdd Add.add Fin.instAdd Fin.add at c2 c3
        simp only [oln] at c2; simp only [tln] at c3
        by_cases ip2 : i.val+2 = n
        · simp only [ip2, Nat.mod_self, not_true_eq_false] at c3
        by_cases ip1 : i.val+1 = n
        · simp only [ip1, Nat.mod_self, not_true_eq_false] at c2
        rw[show (i.val+1)%n = i.val + 1 by refine Nat.mod_eq_of_lt (by lia)] at c2
        rw[show (i.val+2)%n = i.val + 2 by refine Nat.mod_eq_of_lt (by lia)] at c3
        clear ip1 ip2; lia
  · intro fx ⟨x, xha, xhb⟩ xhc; clear xhc; change ∑ i, x i = 1 at xha
    let g (i : Fin n) := x i + min (x (i+1)) (x (i+2))
    let gmax := (Finset.image g univ).max' (by simp)
    suffices m ≤ gmax from by
      refine le_trans this ?_
      replace := Finset.max'_mem (Finset.image g univ) (by simp)
      obtain ⟨j, -, jhb⟩ := mem_image.mp this; clear this
      unfold gmax; rw[←jhb, ←xhb]; clear jhb xhb
      have := le_max' (Finset.image (f x) Finset.univ) (f x j) (by simp)
      refine le_trans ?_ this; unfold g f
      simp only [add_le_add_iff_left, inf_le_iff]
      by_cases gt : x (j+1) ≤ x (j+2)
      · left;
        have := mul_le_mul_right gt (x (j + 1))
        replace := NNReal.sqrt_le_sqrt.mpr this
        simp at this; assumption
      · right; simp only [not_le] at gt; replace gt := Std.le_of_lt gt
        have := mul_le_mul_left gt (x (j + 2))
        replace := NNReal.sqrt_le_sqrt.mpr this
        simp at this; assumption
    clear xhb fx
    obtain ⟨i₀, ih⟩ : ∃ i, ∀ j, x (i-1) ≤ x j := by
      have := Finset.min'_mem (Finset.image x univ) (by simp)
      obtain ⟨i, -, ih⟩ := mem_image.mp this; exists i+1; simp only [add_sub_cancel_right]
      have := (Finset.min'_eq_iff (Finset.image x univ) (by simp) (x i)).mp (Eq.symm ih)
      intro j; refine this.right (x j) ?_
      exact mem_image_of_mem x (by simp)
    let h (i : Fin n) := if x (i+1) ≥ x (i+2) then i+1 else i+2
    refine NNReal.div_le_of_le_mul' ?_
    let res := if n%3 = 1 then x (i₀-1) else (if n%3 = 2 then x (i₀-1) + x (i₀-2) else 0)
    let c₁ (k : Fin n) := k < (n+1)/3
    let c₂ (k : Fin n) := k < n/3
    have mod_disj : n%3 = 0 ∨ n%3 = 1 ∨ n%3 = 2 := by
      have : n%3 < 3 := Nat.mod_lt n (Nat.zero_lt_succ 2); grind only
    exact calc (2*n/3 : ℕ) * gmax
      _ = ((n+1)/3 : ℕ) * gmax + (n/3 : ℕ) * gmax := by
        have : 2*n/3 = (n+1)/3 + n/3 := by lia
        simp[this, right_distrib]
      _ = (∑ k with c₁ k, gmax) + (∑ k with c₂ k, gmax) := by
        clear xha ih res h m hn i₀ mod_disj
        have (a : ℕ) (h : a ≤ n) : a * gmax = ∑ (k : Fin n) with k.val < a, gmax := by
          nth_rewrite 2 [show gmax = gmax*1 by simp]; rw[←mul_sum, mul_comm]
          refine congrArg (HMul.hMul gmax) ?_
          simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]; symm
          refine card_eq_of_bijective (fun i ↦ (fun (h : i < a) ↦ ⟨i, by grind only⟩)) ?_ ?_ ?_
          · intro a ah; simp only [mem_filter, mem_univ, true_and] at ah; exists a.val, ah
          · intros; grind only [= mem_filter, ← mem_univ]
          · intros; grind only
        rw[this ((n+1)/3), this (n/3)] <;> lia
      _ ≥ (∑ k with c₁ k, g (i₀+3*k)) + (∑ k with c₂ k, g (h (i₀+3*k))) := by
        refine add_le_add ?_ ?_ <;>
        · refine sum_le_sum ?_; intros
          have := (Finset.max'_eq_iff _ (by simp) gmax).mp rfl
          exact this.right _ (by simp)
      _ ≥ (∑ k with c₂ k, g (i₀+3*k)) +
          (∑ k with c₂ k, max (x (i₀+3*k+1)) (x (i₀+3*k+2))) + res := by
        clear xha gmax m
        have le1 (hmod : n%3 ≠ 2) : ∑ k with c₂ k, g (i₀+3*k) ≤ ∑ k with c₁ k, g (i₀+3*k) := by
          refine le_of_eq ?_
          refine sum_bijective id (by simp) ?_ ?_ <;> grind
        have le2 {S : Finset (Fin n)} : ∑ k ∈ S, max (x (i₀+3*k+1)) (x (i₀+3*k+2)) ≤
            (∑ k ∈ S, g (h (i₀+3*k))) := by
          refine sum_le_sum ?_; intros
          convert le_self_add
          · grind only [= max_def]
          exact NNReal.instCanonicallyOrderedAdd
        have singl {klast : Fin n} {p : Fin n → Prop} [DecidablePred p] {f : Fin n → NNReal}
            (h : p klast) : ∑ k ∈ {k1 | p k1} with k = klast, f k = f klast := by
          rw[←sum_singleton f klast]
          refine sum_bijective id (by simp) ?_ (by simp)
          simp only [mem_filter, mem_univ, true_and, id_eq, mem_singleton,
            and_iff_right_iff_imp, forall_eq, h]
        rcases mod_disj with d | d | d <;> unfold res <;> clear res
        · simp only [d, zero_ne_one, ↓reduceIte, OfNat.zero_ne_ofNat, add_zero, ge_iff_le]
          exact add_le_add (le1 (by grind only)) le2
        · simp only [d, ↓reduceIte, ge_iff_le]
          rw[add_assoc]
          refine add_le_add (le1 (by grind only)) ?_; clear le1
          rw[add_comm]
          have : NeZero (n/3) := by
            refine neZero_iff.mpr ?_
            exact Nat.div_ne_zero_iff.mpr ⟨by simp, hn⟩
          let klast := Fin.ofNat n (n/3-1)
          rw[←sum_filter_add_sum_filter_not _ (fun k ↦ k = klast)]
          nth_rewrite 3 [←sum_filter_add_sum_filter_not _ (fun k ↦ k = klast)]
          rw[←add_assoc]; refine add_le_add ?_ le2; clear le2
          refine le_of_eq ?_
          have (f : Fin n → NNReal): ∑ k ∈ {k1 | c₂ k1} with k = klast, f k = f klast := by
            refine singl ?_; unfold c₂
            rw[Fin.val_ofNat n (n/3-1)]
            rw[show (n/3-1)%n = n/3-1 by refine Nat.mod_eq_of_lt ?_; grind only]
            grind only
          simp only [this]; clear singl this
          unfold h; clear h
          by_cases cas : x (i₀+3*klast+1) ≥ x (i₀+3*klast+2)
          · simp only [cas, sup_of_le_left, ↓reduceIte]
            unfold g; rw[add_comm]; simp only [add_right_inj]
            suffices suff : i₀+3*klast+1+2 = i₀-1 from by
              rw[suff]; simp only [ih, inf_of_le_right]
            rw[l1 d hn]; grind only
          · simp only [show x (i₀ + 3 * klast + 2) ≥ x (i₀ + 3 * klast + 1) by grind only,
              sup_of_le_right, ge_iff_le, cas, ↓reduceIte]
            unfold g; rw[add_comm]
            suffices suff : i₀+3*klast+2+1 = i₀-1 from by
              rw[suff]; simp only [ih, inf_of_le_left]
            rw[l1 d hn]; grind only
        · clear le1
          simp only [d, OfNat.ofNat_ne_one, ↓reduceIte, ge_iff_le]
          rw[add_assoc]; nth_rewrite 1 [add_comm]; rw[add_assoc]; nth_rewrite 4 [add_comm]
          refine add_le_add le2 ?_; clear le2
          refine le_of_eq ?_
          let klast := Fin.ofNat n (n/3)
          nth_rewrite 2 [←sum_filter_add_sum_filter_not _ (fun k ↦ k = klast)]
          refine (show ∀ {a b c d : NNReal}, a = b → c = d → a+c = b+d by lia) ?_ ?_
          · have (f : Fin n → NNReal): ∑ k ∈ {k1 | c₁ k1} with k = klast, f k = f klast := by
              refine singl ?_; unfold c₁; clear singl c₁
              rw[Fin.val_ofNat n (n/3)]
              rw[show (n/3)%n = n/3 by refine Nat.mod_eq_of_lt ?_; lia]
              grind only
            rw[this]; unfold g; rw[l2 d hn]
            rw[show i₀+(-2)+1 = i₀-1 by grind only]
            simp[ih]; grind only
          · clear singl hn ih h d
            refine sum_bijective id (by simp) ?_ (by intros; grind)
            intro k; simp only [mem_filter, mem_univ, true_and, id_eq]
            refine Iff.intro ?_ ?_
            · unfold c₁ c₂; intro kh; refine ⟨by lia, ?_⟩
              unfold klast; by_contra cont; rw[cont] at kh
              simp only [Fin.ofNat_eq_cast, Fin.val_natCast] at kh
              rw[show (n/3)%n = n/3 from Nat.mod_eq_of_lt (by lia)] at kh
              exact (lt_self_iff_false _).mp kh
            · intro ⟨kha, khb⟩
              by_contra cont; simp at cont
              unfold klast at khb
              simp only [←show k.val = n/3 by lia] at khb
              simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self, not_true_eq_false] at khb
      _ = (∑ k with c₂ k, (g (i₀+3*k) + max (x (i₀+3*k+1)) (x (i₀+3*k+2)))) + res := by
        refine (add_left_inj _).mpr ?_
        rw[←sum_add_distrib]
      _ = (∑ k with c₂ k, (x (i₀+3*k) + x (i₀+3*k+1) + x (i₀+3*k+2))) + res := by
        grind only [= min_def, = max_def]
      _ = ∑ k : Fin n, x k := by
        clear xha m gmax g c₁
        have : ∑ k, x (i₀+k) = ∑ k, x k :=
          Equiv.Perm.sum_comp ⟨fun k ↦ i₀+k, fun k ↦ k-i₀,
            by grind only [= Function.LeftInverse.eq_1],
            by grind only [= Function.RightInverse.eq_1, = Function.LeftInverse.eq_1]⟩
            univ x (by simp only [Equiv.coe_fn_mk, ne_eq, add_eq_right, coe_univ, Set.subset_univ])
        rw[←this]; clear this
        simp only [sum_add_distrib]
        rw[←sum_filter_add_sum_filter_not _ (fun k : Fin n ↦ k < (n/3)*3) (fun k ↦ x (i₀+k))]
        rw[←sum_filter_add_sum_filter_not _ (fun k ↦ k%3 = 0) (fun k ↦ x (i₀+k))]
        nth_rewrite 2 [←sum_filter_add_sum_filter_not _ (fun k ↦ k%3 = 1) (fun k ↦ x (i₀+k))]
        nth_rewrite 1 [←add_assoc]
        iterate 3 refine (show ∀ {a b c d : NNReal}, a = b → c = d → a+c = b+d by lia) ?_ ?_
        · have : ∑ k with c₂ k, x (i₀+3*k) = ∑ k with c₂ k, x (i₀+3*k+0) := by
            exact congrArg (Finset.sum _) (by simp only [add_zero])
          rw[this]
          exact l4 hn 0 (Nat.lt_of_sub_eq_succ rfl)
        · have : ∑ k ∈ {x ∈ {x | x.val < n / 3 * 3} | ¬x % 3 = 0} with k % 3 = 1, x (i₀ + k) =
                 ∑ k ∈ {x | x.val < n / 3 * 3} with k % 3 = 1, x (i₀ + k) := by
            refine congrArg (fun y ↦ Finset.sum (M := NNReal) y _) ?_
            ext k; refine Iff.intro (by grind only [= mem_filter]) ?_
            intro kh; simp only [mem_filter, mem_univ, true_and] at kh;
            simp only [mem_filter, mem_univ, true_and]
            refine ⟨⟨kh.left, ?_⟩, kh.right⟩
            rw[kh.right]; simp only [Fin.one_eq_zero_iff]; grind only
          rw[this]; refine l4 hn 1 ?_
          rw[Fin.val_one' n]; exact Nat.mod_lt_of_lt (Nat.one_lt_succ_succ 1)
        · clear ih h res mod_disj
          have : ∑ k ∈ {x ∈ {x | x.val < n / 3 * 3} | ¬x % 3 = 0} with ¬k % 3 = 1, x (i₀ + k) =
                 ∑ k ∈ {x | x.val < n/3 * 3} with k % 3 = 2, x (i₀ + k) := by
            have mod_help {m : ℕ} {k : Fin n} (hm : m < n) (hk : k.val % 3 = m) :
                k % (3 : Fin n) = Fin.ofNat n m := by
              unfold HMod.hMod instHMod Mod.mod Fin.instMod Fin.mod
              simp only [Fin.coe_ofNat_eq_mod]
              by_cases nth : n = 3
              · simp only [nth, Nat.mod_self, Nat.mod_zero, Fin.eta, Fin.ofNat_eq_cast]
                have : k.val < 3 := by grind only
                refine Fin.eq_of_val_eq ?_
                simp only [Fin.val_natCast]; rw[Nat.mod_eq_of_lt hm]
                rw[Nat.mod_eq_of_lt this] at hk
                assumption
              simp only [show 3 % n = 3 from Nat.mod_eq_of_lt (by grind only)]
              refine Fin.eq_of_val_eq ?_
              simp only [Fin.ofNat_eq_cast, Fin.val_natCast]
              rw[show m%n = m from Nat.mod_eq_of_lt hm]
              assumption
            refine congrArg (fun y ↦ Finset.sum (M := NNReal) y _) ?_
            ext k; refine Iff.intro ?_ ?_
            · simp only [mem_filter, mem_univ, true_and, and_imp]
              intro kha khb khc; refine ⟨kha, ?_⟩
              have : k.val%3 < 3 := by refine Nat.mod_lt k.val (Nat.zero_lt_succ 2)
              replace : k.val%3 = 0 ∨ k.val%3 = 1 ∨ k.val%3 = 2 := by grind only
              rcases this with cas | cas | cas
              · have := mod_help (m := 0) (by grind only) cas
                contradiction
              · have := mod_help (m := 1) (by grind only) cas
                contradiction
              · have := mod_help (m := 2) (by grind only) cas
                assumption
            · clear c₂ i₀ x
              simp only [mem_filter, mem_univ, true_and, and_imp]
              intro kha khb; rw[and_assoc]; refine ⟨kha, ?_⟩
              have : k.val%3 < 3 := by refine Nat.mod_lt k.val (Nat.zero_lt_succ 2)
              replace : k.val%3 = 0 ∨ k.val%3 = 1 ∨ k.val%3 = 2 := by grind only
              have oln : 1%n = 1 := Nat.mod_eq_of_lt (by grind only)
              have tln : 2%n = 2 := Nat.mod_eq_of_lt (by grind only)
              rcases this with cas | cas | cas
              · have := mod_help (m := 0) (by grind only) cas
                simp only [this, Fin.ofNat_eq_cast] at khb
                replace khb := Fin.val_eq_of_eq khb
                simp only [Fin.val_natCast, Nat.zero_mod, Fin.coe_ofNat_eq_mod,
                  Nat.mod_eq_of_lt hn, OfNat.zero_ne_ofNat] at khb
              · have := mod_help (m := 1) (by grind only) cas
                simp only [this, Fin.ofNat_eq_cast] at khb
                replace khb := Fin.val_eq_of_eq khb
                simp only [Fin.val_natCast, Fin.coe_ofNat_eq_mod] at khb
                rw[oln, tln] at khb
                contradiction
              · simp only [khb]; constructor
                <;> by_contra cont
                <;> replace cont := Fin.val_eq_of_eq cont
                <;> simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod] at cont
                <;> rw[tln] at cont
                · contradiction
                · rw[oln] at cont; contradiction
          rw[this]; refine l4 hn 2 ?_
          rw[show (2 : Fin n).val = 2%n from Fin.coe_ofNat_eq_mod n 2]
          simp only [Nat.mod_eq_of_lt hn, Nat.lt_add_one]
        · clear ih h c₂
          replace oln : (-1 : Fin n).val = n-1 := by
            unfold Neg.neg Fin.neg; simp only [Fin.coe_ofNat_eq_mod]
            rw[oln, show (n-1)%n = n-1 from Nat.mod_eq_of_lt (Nat.sub_one_lt_of_lt hn)]
          replace tln : (-2 : Fin n).val = n-2 := by
            unfold Neg.neg Fin.neg; simp only [Fin.coe_ofNat_eq_mod]
            rw[tln, show (n-2)%n = n-2 from Nat.mod_eq_of_lt (by grind only)]
          subst res
          rcases mod_disj with d | d | d
          <;> simp only [d, zero_ne_one, ↓reduceIte, OfNat.zero_ne_ofNat, not_lt]
          · rw[←Finset.sum_empty (f := fun k : Fin n ↦ x (i₀ + k))]
            refine congrArg (fun s ↦ Finset.sum s _) ?_
            ext x; constructor
            · simp only [notMem_empty, mem_filter, mem_univ, true_and, IsEmpty.forall_iff]
            · simp only [mem_filter, mem_univ, true_and, notMem_empty, imp_false, not_le]
              rw[show n/3*3 = n by grind only]; exact x.isLt
          · have : ∑ k ∈ {(-1 : Fin n)}, x (i₀ + k) = x (i₀ - 1) := by
              rw[sum_singleton]; refine congrArg x ?_; grind only
            rw[←this]; refine congrArg (fun s ↦ Finset.sum s _) ?_
            ext x; constructor
            · simp only [mem_singleton, mem_filter, mem_univ, true_and]
              intro xh;
              rw[Fin.val_eq_of_eq xh, oln]; lia
            · simp only [mem_filter, mem_univ, true_and, mem_singleton]
              intro xh;
              refine Fin.eq_of_val_eq ?_
              rw[show x.val = n-1 by lia, oln]
          · simp only [OfNat.ofNat_ne_one, ↓reduceIte]
            have : (-1 : Fin n) ≠ -2 := by
              intro h
              replace h := Fin.val_eq_of_eq h
              rw[oln, tln] at h; omega
            replace := Finset.sum_pair (f := fun k ↦ x (i₀+k)) this
            simp only [show i₀+(-1) = i₀-1 by grind only] at this
            simp only [show i₀+(-2) = i₀-2 by grind only] at this
            rw[←this]; clear this
            congr; ext x; apply Iff.intro
            · intro xh; simp only [mem_insert, mem_singleton] at xh
              simp only [mem_filter, mem_univ, true_and]
              rcases xh <;> lia
            · intro xh; simp only [mem_filter, mem_univ, true_and] at xh
              replace xh : n-2 ≤ x.val := Nat.le_trans (by lia) xh
              simp only [mem_insert, mem_singleton]
              suffices x.val = n-1 ∨ x.val = n-2 from by
                rcases this
                · left; apply Fin.eq_of_val_eq; rw[oln]; assumption
                · right; apply Fin.eq_of_val_eq; rw[tln]; assumption
              grind only
      _ = 1 := by rw[←xha]
