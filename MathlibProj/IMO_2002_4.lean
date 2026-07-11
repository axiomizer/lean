import Mathlib

section IMO_2002_4
def Nat.d (n : ℕ) := n.divisors.sort (· ≤ ·)
def d_sorted (n : ℕ) : n.d.Sorted (· ≤ ·) := Finset.sort_sorted (· ≤ ·) n.divisors
def d_nodup (n : ℕ) : n.d.Nodup := Finset.sort_nodup (· ≤ ·) n.divisors

lemma l₁ (a n : ℕ) (h : a ∈ n.divisors) : n/a ∈ n.divisors :=
  have h₁ := Finset.mem_image_of_mem (fun x => n / x) h
  have := Nat.image_div_divisors_eq_divisors n
  have : Finset.image (fun x : ℕ => n/x) n.divisors ⊆ n.divisors := Finset.subset_of_eq this
  this h₁

lemma l₂ (n k : ℕ) (h : 0 < k) :
    letI S : Finset ℕ := {x ∈ n.divisors | x < k}
    letI T : Finset ℕ := {x ∈ n.divisors | x > n/k}
    S.card = T.card :=
  let S : Finset ℕ := {x ∈ n.divisors | x < k}
  let T : Finset ℕ := {x ∈ n.divisors | x > n/k}

  let σ : ℕ → ℕ := fun x => n/x
  have mt : Set.MapsTo σ S T := fun s hs =>
    let ⟨hfrom₁, hfrom₂⟩ := Finset.mem_filter.mp hs
    have h₁ : σ s ∈ n.divisors := l₁ s n hfrom₁
    have hto₂'' : n/s ≠ 0 := fun h => (Nat.mem_divisors.mp h₁).right (calc
      n = n/s * s := Eq.symm (Nat.div_mul_cancel (Nat.mem_divisors.mp hfrom₁).left)
      _ = 0 * s   := by rw[h]
      _ = 0       := Nat.zero_mul s)
    have hto₂' : (n/s) * s < (n/s) * k :=
      Nat.mul_lt_mul_of_pos_left hfrom₂ (Nat.zero_lt_of_ne_zero hto₂'')
    have : (n/s) * s = n := (Nat.div_mul_cancel (Nat.mem_divisors.mp hfrom₁).left)
    have : n < (n/s) * k := lt_of_eq_of_lt (Eq.symm this) hto₂'
    have := (Nat.div_lt_iff_lt_mul h).mpr this
    Finset.mem_filter.mpr ⟨h₁, this⟩
  have inj : Set.InjOn σ S := fun a as b bs heq =>
    have amem := Nat.mem_divisors.mp (Finset.mem_filter.mp as).left
    have bmem := Nat.mem_divisors.mp (Finset.mem_filter.mp bs).left
    show a = b from calc
      a = n/(n/a) := Eq.symm (Nat.div_div_self amem.left amem.right)
      _ = n/(n/b) := congrArg (HDiv.hDiv n) heq
      _ = b       := Nat.div_div_self bmem.left bmem.right
  have surj : Set.SurjOn σ S T := fun t ht =>
    let ⟨hfrom₁, hfrom₂⟩ := (Finset.mem_filter.mp ht)
    let tdivn := (Nat.mem_divisors.mp hfrom₁).left
    have nnotzero := (Nat.mem_divisors.mp hfrom₁).right
    have nts : n/t ∈ S :=
      have ⟨kk, hkk⟩ := tdivn
      have h₁ : n/t ∈ n.divisors := l₁ t n hfrom₁
      have tnotzero := fun tzero =>
        have : n = 0 := calc
          n = t*kk := hkk
          _ = 0    := mul_eq_zero_of_left tzero kk
        nnotzero this
      have := ((Nat.div_lt_iff_lt_mul h).mp hfrom₂)
      have := calc n/t
        _ < t*k/t     := Nat.div_lt_div_of_lt_of_dvd ⟨k, rfl⟩ this
        _ = k         := Eq.symm (Nat.eq_div_of_mul_eq_right tnotzero rfl)
      Finset.mem_filter.mpr ⟨h₁, this⟩
    have maps : σ (n/t) = t := calc σ (n/t)
      _ = n/(n/t) := rfl
      _ = t       := Nat.div_div_self tdivn nnotzero
    ⟨n/t, nts, maps⟩
  Set.BijOn.finsetCard_eq σ ⟨mt, inj, surj⟩

lemma l₃ (n i : ℕ) (h : i < n.d.length) : {x ∈ n.divisors | x < n.d[i]}.card = i := by
  induction i
  case zero =>
    simp
    intro d hd nnz
    have : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hd, nnz⟩
    have : d ∈ n.d := (Finset.mem_sort (· ≤ ·)).mpr this
    let ⟨j, hj, hjj⟩ := List.getElem_of_mem this
    have : 0 ≤ j := Nat.zero_le j
    have : (⟨0, h⟩ : Fin n.d.length) ≤ (⟨j, hj⟩ : Fin n.d.length) := this
    have := List.Sorted.rel_get_of_le (d_sorted n) this
    exact le_of_le_of_eq this hjj
  case succ j IH =>
    have e₁ : ∀ x ∈ n.divisors, x < n.d[j+1] ∧ ¬x = n.d[j] ↔ x < n.d[j] := by
      intro hx hxx
      apply Iff.intro
      · intro ⟨h₁, h₂⟩
        have : hx ∈ n.d := (Finset.mem_sort (· ≤ ·)).mpr hxx
        let ⟨z, hz, hzz⟩ := List.getElem_of_mem this
        have zlj1 := hzz ▸ h₁
        apply Or.elim (Nat.lt_trichotomy z (j+1))
        · intro hhh
          have : z ≤ j := Nat.le_of_lt_succ hhh
          have : n.d[z] ≤ n.d[j] := List.Sorted.rel_get_of_le (d_sorted n) this
          have := hzz ▸ this
          exact Nat.lt_of_le_of_ne this h₂
        · intro hhh
          have : j+1 ≤ z := by
            apply (Or.elim hhh)
            · intro hhhh
              exact Nat.le_of_eq (Eq.symm hhhh)
            · intro hhhh
              exact Nat.le_of_succ_le hhhh
          have : n.d[j+1] ≤ n.d[z] := List.Sorted.rel_get_of_le (d_sorted n) this
          have : n.d[j+1] < n.d[j+1] := Nat.lt_of_le_of_lt this zlj1
          have := (lt_self_iff_false n.d[j+1]).mp this
          contradiction
      · intro h₁
        have : j ≤ j+1 := Nat.le_add_right j 1
        have : n.d[j] ≤ n.d[j+1] := List.Sorted.rel_get_of_le (d_sorted n) this
        exact ⟨Nat.lt_of_lt_of_le h₁ this, Nat.ne_of_lt h₁⟩
    have e₂ : ∀ x ∈ n.divisors, x < n.d[j+1] ∧ x = n.d[j] ↔ x = n.d[j] := by
      intro hx hxx
      apply Iff.intro
      · exact fun ⟨_, hh⟩ => hh
      · intro hh
        have : j ≤ j+1 := Nat.le_add_right j 1
        have hleq : n.d[j] ≤ n.d[j+1] := List.Sorted.rel_get_of_le (d_sorted n) this
        have : n.d[j+1] = n.d[j] ↔ j+1 = j := List.Nodup.getElem_inj_iff (d_nodup n)
        have : n.d[j+1] ≠ n.d[j] := (Iff.ne this).mpr (Nat.succ_ne_self j)
        have : n.d[j] < n.d[j+1] := Nat.lt_of_le_of_ne hleq (Ne.symm this)
        exact ⟨hh ▸ this, hh⟩
    have : n.d[j] ∈ n.d := by simp
    have ndd : n.d[j] ∈ n.divisors := (Finset.mem_sort (· ≤ ·)).mp this
    have seteq : {x ∈ n.divisors | x = n.d[j]} = {n.d[j]} := by
      simp[Finset.ext_iff]
      simp at ndd
      exact ndd
    calc {x ∈ n.divisors | x < n.d[j+1]}.card
      _ = ({x ∈ n.divisors | x < n.d[j+1]} \ {x ∈ n.divisors | x = n.d[j]}).card +
          ({x ∈ n.divisors | x < n.d[j+1]} ∩ {x ∈ n.divisors | x = n.d[j]}).card := by simp
      _ = {x ∈ n.divisors | x < n.d[j+1] ∧ ¬x = n.d[j]}.card +
          ({x ∈ n.divisors | x < n.d[j+1]} ∩ {x ∈ n.divisors | x = n.d[j]}).card
          := by rw[Finset.filter_and_not n.divisors (fun x ↦ x < n.d[j+1]) fun x ↦ x = n.d[j]]
      _ = {x ∈ n.divisors | x < n.d[j+1] ∧ ¬x = n.d[j]}.card +
          {x ∈ n.divisors | x < n.d[j+1] ∧ x = n.d[j]}.card
          := by rw[Finset.filter_and (fun x ↦ x < n.d[j+1]) (fun x ↦ x = n.d[j]) n.divisors]
      _ = {x ∈ n.divisors | x < n.d[j]}.card + {x ∈ n.divisors | x = n.d[j]}.card :=
          by rw[Finset.filter_congr e₁, Finset.filter_congr e₂]
      _ = j + {x ∈ n.divisors | x = n.d[j]}.card := by rw[IH (Nat.lt_of_succ_lt h)]
      _ = j + 1 := by simp[seteq]

lemma l₄' (s : Finset ℕ) (a : ℕ) (h : a ∈ s) :
    {x ∈ s | x < a}.card = s.card - 1 - {x ∈ s | x > a}.card :=
  have equiv₁ : ∀ x ∈ s, ¬x < a ∧ x = a ↔ x = a := fun x xh =>
    have dir₁ : ¬x < a ∧ x = a → x = a := fun hh => hh.right
    have dir₂ : x = a → ¬x < a ∧ x = a := fun hh => ⟨Eq.not_gt (Eq.symm hh), hh⟩
    ⟨dir₁, dir₂⟩
  have equiv₂ : ∀ x ∈ s, ¬x < a ∧ ¬x = a ↔ x > a := fun x xh =>
    have dir₁ : ¬x < a ∧ ¬x = a → x > a := fun xh => Or.elim (Nat.lt_trichotomy x a)
      (fun xhh => False.elim (xh.left xhh))
      (fun xhh => Or.elim xhh
        (fun xhhh => False.elim (xh.right xhhh))
        (fun xhhh => xhhh))
    have dir₂ : x > a → ¬x < a ∧ ¬x = a := fun xh => ⟨Nat.not_lt_of_gt xh, Nat.ne_of_lt' xh⟩
    ⟨dir₁, dir₂⟩
  calc {x ∈ s | x < a}.card
    _ = s.card - {x ∈ s | ¬x < a}.card :=
      Nat.eq_sub_of_add_eq (Finset.filter_card_add_filter_neg_card_eq_card fun x => x < a)
    _ = s.card - (({x ∈ s | ¬x < a} ∩ {x ∈ s | x = a}).card +
                  ({x ∈ s | ¬x < a} \ {x ∈ s | x = a}).card) := by simp
    _ = s.card - ({x ∈ s | ¬x < a ∧ x = a}.card +
                  ({x ∈ s | ¬x < a} \ {x ∈ s | x = a}).card) :=
      by rw[Finset.filter_and (fun a_1 ↦ ¬a_1 < a) (fun a_1 ↦ a_1 = a) s]
    _ = s.card - ({x ∈ s | ¬x < a ∧ x = a}.card + {x ∈ s | ¬x < a ∧ ¬x = a}.card) :=
      by rw[Finset.filter_and_not s (fun a_1 ↦ ¬a_1 < a) fun a_1 ↦ a_1 = a]
    _ = s.card - ({x ∈ s | x = a}.card + {x ∈ s | ¬x < a ∧ ¬ x = a}.card) :=
      by rw[Finset.filter_congr equiv₁]
    _ = s.card - ((∑ x ∈ s, if x = a then 1 else 0) + {x ∈ s | ¬x < a ∧ ¬ x = a}.card) :=
      by rw[Finset.card_filter]
    _ = s.card - (1 + {x ∈ s | ¬x < a ∧ ¬ x = a}.card) := by simp[h]
    _ = s.card - (1 + {x ∈ s | x > a}.card) := by rw[Finset.filter_congr equiv₂]
    _ = s.card - 1 - {x ∈ s | x > a}.card := Nat.sub_add_eq s.card 1 {x ∈ s | x > a}.card

lemma l₄ (n i : ℕ) (h : i < n.d.length) : n.d[n.d.length-1-i] = n / n.d[i] :=
  let d := n.d
  have h₁ : d[i] ∈ n.divisors := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem h)
  have h₂ : n / d[i] ∈ n.divisors := l₁ d[i] n h₁
  have : n / d[i] ∈ d := (Finset.mem_sort (· ≤ ·)).mpr h₂
  let ⟨j, hj, hjj⟩ := List.getElem_of_mem this
  have : 0 < d[i] := Nat.pos_of_mem_divisors h₁
  have := calc
    j = {x ∈ n.divisors | x < d[j]}.card := Eq.symm (l₃ n j hj)
    _ = n.divisors.card - 1 - {x ∈ n.divisors | x > d[j]}.card := l₄' n.divisors d[j] (hjj ▸ h₂)
    _ = (n.divisors.sort (· ≤ ·)).length - 1 - {x ∈ n.divisors | x > d[j]}.card
          := by rw[Finset.length_sort (· ≤ ·)]
    _ = d.length - 1 - {x ∈ n.divisors | x > d[j]}.card        := by rfl
    _ = d.length - 1 - {x ∈ n.divisors | x > n / d[i]}.card    := by simp[hjj]
    _ = d.length - 1 - {x ∈ n.divisors | x < d[i]}.card        := by rw[l₂ n d[i] this]
    _ = d.length - 1 - i                                       := by rw[l₃ n i h]
  have : d[j] = d[d.length-1-i] := getElem_congr_idx this
  show d[d.length-1-i] = n / d[i] from Eq.trans (Eq.symm this) hjj

lemma l₅ (n i : ℕ) (h : i < n.d.length) : n.d[i] ≥ i+1 := by
  induction i
  case zero =>
    have := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem h)
    simp at this
    have := ne_zero_of_dvd_ne_zero this.right this.left
    simp
    exact Nat.one_le_iff_ne_zero.mpr this
  case succ j IH =>
    have : j < n.d.length := Nat.lt_of_succ_lt h
    have := IH this
    have hlt : j < j+1 := lt_add_one j
    have geq : n.d[j+1] ≥ n.d[j] := List.Sorted.rel_get_of_lt (d_sorted n) hlt
    have : n.d[j+1] = n.d[j] ↔ j+1 = j := List.Nodup.getElem_inj_iff (d_nodup n)
    have : n.d[j+1] ≠ n.d[j] := (Iff.ne this).mpr (Nat.succ_ne_self j)
    have jllen := calc
      j < j+1 := hlt
      _ < n.d.length := h
    calc n.d[j+1]
    _ ≥ n.d[j]+1 := Nat.lt_of_le_of_ne geq (Ne.symm this)
    _ ≥ j+2      := by simp[IH jllen]

lemma telescope (k : ℕ) (f : ℕ → ℚ) : ∑ i ∈ Finset.Icc 0 k, (f i - f (i+1)) = f 0 - f (k+1) :=
  let ι₁ := Finset.Icc 0 k
  let ι₂ := Finset.Icc 1 (k+1)
  let ι₃ := Finset.Icc 1 k
  calc ∑ i ∈ ι₁, (f i - f (i+1))
    _ = ∑ i ∈ ι₁, f i - ∑ i ∈ ι₁, f (i+1) := Finset.sum_sub_distrib f fun x ↦ f (x + 1)
    _ = ∑ i ∈ ι₁, f i - ∑ i ∈ ι₂, f i := by
      let f' : ℕ → ℚ := fun x ↦ f (x+1)
      let bij : ℕ → ℕ := fun x ↦ x+1
      have hi : ∀ a ∈ ι₁, bij a ∈ ι₂ := by
        intro a ha
        rw[Finset.mem_Icc] at ha; rw[Finset.mem_Icc]
        exact ⟨Nat.le_add_left 1 a, Nat.add_le_add_right ha.right 1⟩
      have i_inj : Set.InjOn bij ι₁ := by
        intro _ _ _ _ bijeq
        exact Nat.succ_inj.mp bijeq
      have i_surj : Set.SurjOn bij ι₁ ι₂ := by
        intro a ha
        have amem := Finset.mem_Icc.mp ha
        have mapsto : (a-1) + 1 = a := Nat.sub_add_cancel amem.left
        have : a-1 ∈ ι₁ := by
          rw[Finset.mem_Icc]
          exact ⟨Nat.zero_le (a - 1), Nat.sub_le_of_le_add amem.right⟩
        exact ⟨a-1, ⟨this, mapsto⟩⟩
      have h : ∀ a ∈ ι₁, f' a = f (bij a) := by intro a ha; rfl
      have := Finset.sum_nbij bij hi i_inj i_surj h
      rw[this]
    _ = f 0 - f (k+1) := by
      have rw₁ := calc ∑ i ∈ ι₁, f i
        _ = ∑ i ∈ insert 0 ι₃, f i := by
          have : insert 0 ι₃ = ι₁ := Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le k)
          rw[congrFun (congrArg Finset.sum this) fun i ↦ f i]
        _ = f 0 + ∑ i ∈ ι₃, f i := by
          have : 0 ∉ ι₃ := by rw[Finset.mem_Icc]; simp
          exact Finset.sum_insert this
      have rw₂ := calc ∑ i ∈ ι₂, f i
        _ = ∑ i ∈ insert (k+1) ι₃, f i := by
          have : insert (k+1) ι₃ = ι₂ := Finset.insert_Icc_right_eq_Icc_succ (Nat.le_add_left 1 k)
          rw [congrFun (congrArg Finset.sum this) fun i ↦ f i]
        _ = ∑ i ∈ ι₃, f i + f (k+1) := by
          have : k+1 ∉ ι₃ := by rw[Finset.mem_Icc]; simp
          rw[Rat.add_comm]
          exact Finset.sum_insert this
      rw[rw₁, rw₂]
      rw[tsub_eq_tsub_of_add_eq_add]
      rw[Rat.add_assoc]

theorem t1 (n : ℕ) (h : n > 0) : letI d := n.divisors.sort (· ≤ ·)
    ∑ i : Fin (d.length-1), d[i] * d[i.val+1] < n^2 :=
  let d := n.d
  let k := d.length - 1
  let ι := Fin k
  let f (i : ι) : ℕ := d[i] * d[i.val+1]
  let σ : Equiv.Perm ι := Fin.revPerm

  have (i : ι) : k-i ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr i.prop
  have h₁ (i : ι) := calc d[k-(i+1)+1]
    _ = d[k-i] := getElem_congr_idx (Nat.sub_one_add_one (this i))
    _ = n / d[i] := l₄ n i (Nat.lt_of_lt_pred i.prop)
  have (i : ι) : d[k-(i+1)] = n / d[i.val+1] := l₄ n (i+1) (Nat.add_lt_of_lt_sub i.prop)

  have ind₁ (i : ι) : i.val+1 < d.length :=
    have := calc
      1 ≤ i.val+1    := Nat.le_add_left 1 ↑i
      _ ≤ d.length-1 := i.prop
      _ ≤ d.length   := Nat.sub_le d.length 1
    calc i.val+1
      _ < k+1          := Nat.add_lt_add_right i.prop 1
      _ = d.length-1+1 := rfl
      _ = d.length     := Nat.sub_add_cancel this
  have ind₂ (i : ι) : i < d.length := Nat.lt_of_succ_lt (ind₁ i)
  let f₁ (i : ι) := d[k-(i+1)] * d[k-(i+1)+1]
  let f₂ (i : ι) := (n / d[i.val+1]) * (n / d[i])
  have rwsum : ∑ i, f i = ∑ i : ι, (n / d[i.val+1]) * (n / d[i]) :=
    have h₂ (i : ι) : f₁ i = f₂ i := Mathlib.Tactic.LinearCombination'.mul_pf (this i) (h₁ i)
    calc ∑ i, f i
      _ = ∑ i, f (σ i)                              := Eq.symm (Equiv.sum_comp σ f)
      _ = ∑ i : ι, (n / d[i.val+1]) * (n / d[i])    := Fintype.sum_congr f₁ f₂ h₂

  have : ((∑ i, f i : ℕ) : ℚ) < (n^2 : ℚ) :=
    let g₁ (i : ι) := (((n / d[i.val+1]) * (n / d[i]) : ℕ) : ℚ)
    have sumleq : ∀ i ∈ Finset.univ, g₁ i ≤ (n^2 * ((1 / (i+1)) - (1 / (i+2))) : ℚ) := by
      intro i iu
      have flip₁ : (n / d[i.val+1] : ℚ) ≤ (n / (i+2) : ℚ) := by
        have : d[i.val+1] ≥ i.val+2 := l₅ n (i.val+1) (ind₁ i)
        have := calc (d[i.val+1] : ℚ)
          _ ≥ ((i.val+2 : ℕ) : ℚ) := Rat.natCast_le_natCast.mpr this
          _ = (i.val+(2:ℕ) : ℚ)   := Rat.natCast_add (↑i) 2
          _ = (i.val+2 : ℚ)       := rfl
        have : (i.val+2 : ℚ) ≤ (d[i.val+1] : ℚ) := this
        refine div_le_div_of_nonneg_left ?_ ?_ this
        · exact Rat.natCast_nonneg
        · exact neg_lt_iff_pos_add.mp rfl
      have flip₂ : (n / d[i] : ℚ) ≤ (n / (i+1) : ℚ) := by
        have : d[i] ≥ i+1 := l₅ n i.val (ind₂ i)
        have := calc (d[i] : ℚ)
          _ ≥ ((i.val+1 : ℕ) : ℚ) := Rat.natCast_le_natCast.mpr this
          _ = (i.val+(1:ℕ) : ℚ)   := Rat.natCast_add (↑i) 1
          _ = (i.val+1 : ℚ)       := rfl
        have : (i.val+1 : ℚ) ≤ (d[i.val] : ℚ) := this
        refine div_le_div_of_nonneg_left ?_ ?_ this
        · exact Rat.natCast_nonneg
        · exact neg_lt_iff_pos_add.mp rfl
      have div₁ : d[i.val+1] ∣ n := by
        have := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem (ind₁ i))
        simp at this
        exact this.left
      have div₂ : d[i] ∣ n := by
        have := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem (ind₂ i))
        simp at this
        exact this.left
      exact calc (g₁ i)
        _ = (((n / d[i.val+1]) * (n / d[i]) : ℕ) : ℚ) := rfl
        _ = ((n / d[i.val+1] : ℕ) : ℚ) * ((n / d[i] : ℕ) : ℚ) :=
          by rw[Rat.natCast_mul (n / d[i.val+1]) (n / d[i])]
        _ = ((n / d[i.val+1]) * (n / d[i]) : ℚ) :=
          by rw[Rat.natCast_div n d[i.val+1] div₁, Rat.natCast_div n d[i] div₂]
        _ ≤ ((n / (i+2)) * (n / d[i]) : ℚ) := by
          refine Rat.mul_le_mul_of_nonneg_right flip₁ ?_
          refine Rat.div_nonneg ?_ ?_
          · exact Rat.natCast_nonneg
          · exact Rat.natCast_nonneg
        _ ≤ ((n / (i+2)) * (n / (i+1)) : ℚ) := by
          refine Rat.mul_le_mul_of_nonneg_left flip₂ ?_
          refine Rat.div_nonneg ?_ ?_
          · exact Rat.natCast_nonneg
          · refine add_nonneg ?_ rfl
            exact Rat.natCast_nonneg
        _ = (n^2 * ((1 / (i+1)) * (1 / (i+2))) : ℚ) := by
          rw[Rat.mul_comm]
          rw[div_eq_mul_one_div (n : ℚ) (i+2 : ℚ)]
          rw[div_eq_mul_one_div (n : ℚ) (i+1 : ℚ)]
          rw[←Rat.mul_assoc]
          rw[Rat.mul_comm (n * (1/(i+1)) : ℚ) (n : ℚ)]
          rw[←Rat.mul_assoc]
          rw[pow_two (n : ℚ)]
          rw[Rat.mul_assoc]
        _ = (n^2 * (1 / ((i+1) * (i+2))) : ℚ) :=
          by rw[div_mul_eq_div_mul_one_div 1 (i+1 : ℚ) (i+2 : ℚ)]
        _ = (n^2 * ((i+2-(i+1)) / ((i+1) * (i+2))) : ℚ) := by
          have : (i+2-(i+1) : ℚ) = (1 : ℚ) := by norm_num
          rw[this]
        _ = (n^2 * ((i+2) / ((i+1) * (i+2)) - (i+1) / ((i+1) * (i+2))): ℚ) := by
          rw[sub_div (i+2 : ℚ) (i+1 : ℚ) ((i+1) * (i+2) : ℚ)]
        _ = (n^2 * (1 / (i+1) - 1 / (i+2)): ℚ) := by field_simp

    calc ((∑ i, f i : ℕ) : ℚ)
      _ = ((∑ i : ι, (n / d[i.val+1]) * (n / d[i]) : ℕ) : ℚ) := congrArg Nat.cast rwsum
      _ = ∑ i : ι, (((n / d[i.val+1]) * (n / d[i]) : ℕ) : ℚ) := Nat.cast_sum Finset.univ f₂
      _ ≤ ∑ i : ι, (n^2 * ((1 / (i+1)) - (1/(i+2))) : ℚ)     := Finset.sum_le_sum sumleq
      _ = (n^2 : ℚ) * ∑ i : ι, ((1/(i+1)) - (1/(i+2)) : ℚ)   := by rw[Finset.mul_sum]
      _ = n^2 * ∑ i : ι, ((1/(i+1)) - (1/(i+2)) : ℚ)         := rfl
      _ = (n^2 * (1 - 1/(k+1)) : ℚ)                     := by
        let f' : ℕ → ℚ := fun i ↦ ((1/(i+1)) - (1/(i+2)) : ℚ)
        apply Or.elim (em (k = 0))
        · intro kz
          have : Finset.range k = ∅ := Finset.range_eq_empty_iff.mpr kz
          have := calc ∑ i : ι, f' i
            _ = ∑ i ∈ Finset.range k, f' i := Fin.sum_univ_eq_sum_range f' k
            _ = ∑ i ∈ ∅, f' i              := congrFun (congrArg Finset.sum this) fun i ↦ f' i
            _ = 0                          := rfl
          rw[this, kz]
          simp
        · intro knz
          have := calc ∑ i : ι, ((1/(i+1)) - (1/(i+2)) : ℚ)
            _ = ∑ i ∈ Finset.range k, ((1/(i+1)) - (1/(i+2)) : ℚ) :=
              by rw[Finset.sum_range (fun x ↦ ((1/(x+1)) - (1/(x+2)) : ℚ))]
            _ = ∑ i ∈ Finset.Icc 0 (k-1), ((1/(i+1)) - (1/(i+2)) : ℚ) := by
              have := Nat.range_eq_Icc_zero_sub_one k knz
              expose_names
              exact congrFun (congrArg Finset.sum this) fun i ↦ (1 / (i + 1) - 1 / (i + 2) : ℚ)
            _ = ∑ i ∈ Finset.Icc 0 (k-1), ((1/(i+1)) - (1/((i+1 : ℕ) + 1)) : ℚ) := by
              let j₁ : ℕ → ℚ := fun i ↦ ((1/(i+1)) - (1/(i+2)) : ℚ)
              let j₂ : ℕ → ℚ := fun i ↦ ((1/(i+1)) - (1/((i+1 : ℕ) + 1)) : ℚ)
              have : ∀ i ∈ Finset.Icc 0 (k-1), j₁ i = j₂ i := by
                intro i ih
                have : (i+2:ℚ) = ((i+1:ℕ)+1:ℚ) := by
                  norm_num
                  rw[Rat.add_assoc]
                  simp
                  norm_num
                unfold j₁ j₂
                rw[this]
              exact Finset.sum_congr rfl this
            _ = (1/((0:ℕ)+1)-1/((k-1+1:ℕ)+1):ℚ) := telescope (k-1) (fun x ↦ 1/((x:ℚ)+1))
            _ = (1-1/(k+1):ℚ) := by
              norm_num
              have : ((k-1:ℕ) :ℚ) = (k-1:ℚ) := Nat.cast_pred (Nat.zero_lt_of_ne_zero knz)
              rw[this]
              simp
          rw[this]
      _ < (n^2 : ℚ)                                          := by
        have h₁ : (n^2 : ℚ) > 0 := Rat.pow_pos (Rat.natCast_pos.mpr h)
        have h₂ : (1-1/(k+1) : ℚ) < 1 := by field_simp; simp
        exact mul_lt_of_lt_one_right h₁ h₂
  have : ∑ i, f i < n^2 := by
    have := Rat.natCast_lt_natCast.mp this
    rw[Nat.pow_two n]
    simp at this
    exact this
  this

end IMO_2002_4
