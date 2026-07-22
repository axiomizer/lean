import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Pairwise.Basic

set_option linter.style.header false
open Finset

def block_design (t k n : ℕ) (bd : Finset (Finset (Fin n))) : Prop :=
  (∀ b ∈ bd, #b = k) ∧ (∀ s : Finset (Fin n), #s = t → ∃! b ∈ bd, s ⊆ b)

open Classical in
noncomputable def fano_planes : Finset (Finset (Finset (Fin 7))) := {bd | block_design 2 3 7 bd}

noncomputable def parti (fixed : Finset (Finset (Fin 7))) (pair : Finset (Fin 7)) :=
  fun i ↦ {bd ∈ fano_planes | fixed ⊆ bd ∧ pair ∪ {i} ∈ bd}

def ι (fixed : Finset (Finset (Fin 7))) (pair : Finset (Fin 7)) :=
  univ \ (fixed.biUnion id ∪ pair)

lemma union (fixed : Finset (Finset (Fin 7))) (pair : Finset (Fin 7)) (hp : #pair = 2)
    (hint : ∀ f ∈ fixed, ∃! x, x ∈ f ∩ pair) :
    {bd ∈ fano_planes | fixed ⊆ bd} = (ι fixed pair).biUnion (parti fixed pair) := by
  unfold parti fano_planes; ext pl
  simp only [mem_filter, mem_univ, true_and, union_singleton, mem_biUnion]
  constructor
  · intro hpl
    obtain ⟨b, ⟨bha1, bha2⟩, _⟩ := hpl.1.2 pair hp
    have bcard := hpl.1.1 b bha1
    obtain ⟨a, ha⟩ : ∃ a, b = pair ∪ {a} := by
      suffices ∃ a, b \ pair = {a} by grind only [= subset_iff, = union_singleton, = mem_insert,
        = mem_union, = mem_singleton, = mem_sdiff]
      apply card_eq_one.mp
      grind only [= insert_eq_of_mem, = card_sdiff_of_subset, = mem_singleton,
        = card_insert_of_notMem, = card_singleton]
    replace ha := union_singleton a pair ▸ ha
    exists a; refine ⟨?_, hpl.1, hpl.2, ha ▸ bha1⟩; unfold ι
    simp only [mem_sdiff, mem_univ, mem_union, mem_biUnion, id_eq, not_or, not_exists, not_and,
      true_and]
    have anin : a ∉ pair := by grind only [= insert_eq_of_mem]
    refine ⟨?_, anin⟩; intro f hf; obtain ⟨x, hx⟩ := hint f hf
    obtain ⟨y, hy⟩ : ∃ y, pair = {x, y} := by
      have : #(pair \ {x}) = 1 := by grind only [= mem_inter, = card_sdiff, usr le_card_sdiff,
        = singleton_inter, = card_singleton]
      obtain ⟨y, hy⟩ := card_eq_one.mp this
      grind only [= mem_inter, usr card_sdiff_add_card_inter, usr card_union_add_card_inter,
        = union_singleton, = insert_eq_of_mem, = mem_insert, = mem_union, = mem_sdiff,
        = mem_singleton]
    by_contra c; have anx : a ≠ x := by grind only [= mem_insert]
    obtain ⟨B, hB⟩ := hpl.1.2 {a, x} (card_pair anx); simp only [and_imp] at hB
    have t := hB.2 b bha1 (by grind only [= subset_iff, = mem_insert, = mem_singleton])
    have := hB.2 f ((subset_iff.mp hpl.2) hf) (by grind only [= subset_iff, = insert_eq_of_mem,
      = mem_inter, = mem_insert, = mem_singleton, = card_singleton])
    rw[←t] at this
    grind only [= mem_insert, = card_insert_of_notMem, = insert_eq_of_mem, = mem_inter,
      = insert_inter, = inter_insert, = mem_singleton, = card_singleton, = singleton_inter]
  · intro ⟨_, _, h1, h2, _⟩; exact ⟨h1, h2⟩

lemma cardsum (fixed : Finset (Finset (Fin 7))) (pair : Finset (Fin 7)) (hp : #pair = 2) :
    ((ι fixed pair).biUnion (parti fixed pair)).card =
    ∑ u ∈ (ι fixed pair), ((parti fixed pair) u).card := by
  apply Finset.card_biUnion
  intro i hi j hj hij; unfold Function.onFun Disjoint parti
  simp only [bot_eq_empty, subset_empty]
  intro bds hbds1 hbds2
  by_contra! cont; obtain ⟨bd, hbd⟩ := cont
  have hbd2: bd ∈ fano_planes := by grind only [= subset_iff, = mem_filter]
  replace hbds1 : pair ∪ {i} ∈ bd := by grind only [= subset_iff, = mem_filter]
  replace hbds2 : pair ∪ {j} ∈ bd := by grind only [= subset_iff, = mem_filter]
  unfold fano_planes at hbd2; unfold block_design at hbd2
  simp only [mem_filter, mem_univ, true_and] at hbd2
  rcases (hbd2.2 pair hp) with ⟨w, hwa, hw⟩
  simp only [and_imp] at hw
  have hw1 := hw (pair ∪ {i}) hbds1 (by simp only [union_singleton, subset_insert])
  have hw2 := hw (pair ∪ {j}) hbds2 (by simp only [union_singleton, subset_insert])
  have := hw2 ▸ hw1; clear hw1 hw2 hw hwa hbd2 hbds1 hbds2 hbd bd w bds
  replace : i ∈ pair ∪ {j} := by grind only [= mem_union, = mem_singleton]
  have hdis : Disjoint (ι fixed pair) pair := by
    unfold ι Disjoint; grind only [= subset_iff, = mem_sdiff, = mem_union]
  have := disjoint_left.mp hdis hi
  grind only [= mem_union, = mem_singleton]

lemma img_cancel {α : Type} [DecidableEq α] (f : Equiv.Perm α) (S : Finset α) :
    image f (image f.symm S) = S := by
  ext x; constructor
  <;> simp only [mem_image, exists_exists_and_eq_and, Equiv.apply_symm_apply, exists_eq_right,
    imp_self]

lemma img_img_cancel {α : Type} [DecidableEq α] (f : Equiv.Perm α) (x : Finset (Finset α)) :
    image (image f) (image (image f.symm) x) = x := by
  have c := img_cancel f
  ext a; simp only [mem_image, exists_exists_and_eq_and]
  grind only

lemma mapsto (f : Equiv.Perm (Fin 7)) : Set.MapsTo (image (image f)) fano_planes fano_planes := by
  unfold fano_planes block_design; intro pl
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
  intro h1 h2; constructor
  · intro b hb; rw[←h1 b hb]; exact Finset.card_image_of_injective _ (Equiv.injective f)
  · intro pair hpair
    have : #(image f.symm pair) = 2 := by
      rw[←hpair]; exact Finset.card_image_of_injective _ (Equiv.injective f.symm)
    obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := h2 (image f.symm pair) this; simp only [and_imp] at ha3
    exists (image f a); simp only [and_imp, forall_exists_index, forall_apply_eq_imp_iff₂]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exists a
    · replace ha2 := image_subset_image (f := f) ha2
      exact (img_cancel f pair ▸ ha2)
    · intro b hb1 hb2; apply congrArg (image f ·)
      replace hb2 := image_subset_image (f := f.symm) hb2
      have := f.symm_symm ▸ img_cancel f.symm b
      exact ha3 b hb1 (this ▸ hb2)

lemma biject (fixed : Finset (Finset (Fin 7))) (pair : Finset (Fin 7))
    (w : Fin 7) (hw : w ∈ ι fixed pair) :
    ∑ u ∈ (ι fixed pair), #(parti fixed pair u) =
    #(ι fixed pair) * #{bd ∈ fano_planes | (fixed ∪ {pair ∪ {w}}) ⊆ bd} := by
  apply Finset.sum_eq_card_nsmul; unfold parti
  intro i hi
  let f : Equiv.Perm (Fin 7) := Equiv.swap w i
  have imfix : ∀ x, x ∉ ι fixed pair → f x = x := by
    intro x hx; unfold ι at hx hi hw
    grind only [= Equiv.swap_apply_def]
  have ipp : image f pair = pair := by
    unfold f; unfold ι at imfix hw hi
    grind only [usr card_image_iff, = mem_image, = mem_sdiff, ← mem_univ, = mem_union]
  have iff : ∀ x, x ∈ fixed → image f x = x := by
    unfold f; unfold ι at imfix hw hi
    grind only [= mem_sdiff, = mem_union, = mem_biUnion, = id.eq_1, = mem_image,
      = Equiv.swap_apply_def]
  apply card_nbij (image (image f))
  · intro bd
    simp only [coe_filter, Set.mem_setOf_eq, and_imp]
    intro hbd1 hbd2 hbd3; refine ⟨mapsto f hbd1, ?_⟩
    unfold fano_planes at hbd1; simp only [mem_filter, mem_univ, true_and] at hbd1
    intro x; simp only [union_singleton, mem_insert]; intro hx; simp only [mem_image]
    rcases hx with hx | hx
    · refine ⟨pair ∪ {i}, ⟨hbd3, ?_⟩⟩; subst hx
      grind only [= union_singleton, = mem_image, = insert_eq_of_mem, = mem_insert,
        = Equiv.swap_apply_def, = mem_union]
    · grind only [= subset_iff]
  · intro x _ y _ hxy
    exact image_injective (image_injective (Equiv.injective f)) hxy
  · intro bd; simp only [union_singleton, coe_filter, Set.mem_setOf_eq, Set.mem_image, and_imp]
    intro hbd1 hbd2
    refine ⟨image (image f.symm) bd, ?_⟩; and_intros
    · exact mapsto f.symm hbd1
    · intro fix hfix; simp only [mem_image]
      refine ⟨fix, ⟨by grind only [= subset_iff, = mem_insert], ?_⟩⟩
      grind only [= insert_eq_of_mem, = mem_image, = Equiv.swap_apply_def, = Equiv.symm_apply_apply,
        = insert_inter]
    · simp only [mem_image]
      refine ⟨insert w pair, ⟨by grind only [= subset_iff, = mem_insert], ?_⟩⟩
      have := img_cancel f.symm (insert i pair)
      rw[←this]; apply congrArg; rw[f.symm_symm]
      grind only [= insert_eq_of_mem, = mem_image, = Equiv.swap_apply_def, = mem_insert]
    · exact img_img_cancel f bd

lemma symmetry1 : #fano_planes = 5 * #{bd ∈ fano_planes | {{0, 1, 2}} ⊆ bd} := by
  have un := union ∅ {0, 1} rfl (by grind only [← notMem_empty])
  simp only [empty_subset, filter_true, Fin.isValue] at un
  have csum := cardsum ∅ {0, 1} rfl
  nth_rewrite 1 [un]; rw[csum]
  have bij := biject ∅ {0, 1} 2 (by unfold ι; decide)
  simp only [Fin.isValue, insert_union, singleton_union, empty_union] at bij
  rw[bij, show #(ι ∅ {0, 1}) = 5 from rfl]

lemma symmetry2 : #{bd ∈ fano_planes | {{0, 1, 2}} ⊆ bd} =
    3 * #{bd ∈ fano_planes | {{0, 1, 2}, {0, 3, 4}} ⊆ bd} := by
  have un := union {{0, 1, 2}} {0, 3} rfl ?_
  case refine_1 =>
    simp only [Fin.isValue, mem_singleton, mem_inter, mem_insert, forall_eq]; exists 0
  have csum := cardsum {{0, 1, 2}} {0, 3} rfl
  have bij := biject {{0, 1, 2}} {0, 3} 4 (by unfold ι; decide)
  simp only [Fin.isValue, insert_union, singleton_union] at bij
  rw[un, csum, bij, show #(ι {{0, 1, 2}} {0, 3}) = 3 from rfl]

lemma symmetry3 : #{bd ∈ fano_planes | {{0, 1, 2}, {0, 3, 4}} ⊆ bd} =
    2 * #{bd ∈ fano_planes | {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}} ⊆ bd} := by
  have un := union {{0, 1, 2}, {0, 3, 4}} {1, 3} rfl ?_
  case refine_1 =>
    simp only [Fin.isValue, mem_insert, mem_singleton, mem_inter, forall_eq_or_imp, forall_eq]
    refine ⟨⟨1, ?_⟩, ⟨3, ?_⟩⟩ <;> grind only
  have csum := cardsum {{0, 1, 2}, {0, 3, 4}} {1, 3} rfl
  have bij := biject {{0, 1, 2}, {0, 3, 4}} {1, 3} 5 (by unfold ι; decide)
  simp only [Fin.isValue, insert_union, singleton_union] at bij
  rw[un, csum, bij, show #(ι {{0, 1, 2}, {0, 3, 4}} {1, 3}) = 2 from rfl]

lemma find_pair {α : Type} [DecidableEq α] {S : Finset α} (hS : #S = 2) :
    ∃ a b : α, S = {a, b} := by
  obtain ⟨a, ha⟩ := card_pos.mp (Nat.lt_of_sub_eq_succ hS)
  obtain ⟨b, hb⟩ : (S \ {a}).Nonempty := by
    refine sdiff_nonempty_of_card_lt_card ?_; grind only [= card_singleton]
  exists a, b
  symm; apply eq_of_subset_of_card_le
  · grind only [= mem_sdiff, = subset_iff, = mem_insert, = mem_singleton]
  · grind only [= mem_sdiff, = card_insert_of_notMem, = mem_singleton, = card_singleton]

lemma forced_block {b1 b2 : Finset (Fin 7)} {bd : Finset (Finset (Fin 7))}
    (h : bd ∈ fano_planes) (i : Fin 7) (h1 : b1 ∈ bd) (h2 : b2 ∈ bd) (h3 : b1 ∩ b2 = {i}) :
    {i} ∪ (b1 ∪ b2)ᶜ ∈ bd := by
  unfold fano_planes at h; simp only [mem_filter, mem_univ, true_and] at h
  have : #(b1 ∪ b2)ᶜ = 2 := by
    have := Finset.card_add_card_compl (b1 ∪ b2)
    rw[Fintype.card_fin 7, card_union] at this
    grind[h.1 b1 h1, h.1 b2 h2]
  obtain ⟨j, k, hjk⟩ := find_pair this; rw[hjk]
  have inz {z : Fin 7} (hz : z ∈ (b1 ∪ b2)ᶜ): i ≠ z := by
    replace : z ∉ (b1 ∪ b2) := by exact mem_compl.mp hz
    replace : z ∉ b1 := by grind only [= mem_union]
    by_contra! c
    have con : z ∈ b1 ∩ b2 := by grind only [= mem_singleton]
    replace con : z ∈ b1 := mem_of_mem_filter z con
    exact this con
  have inj : i ≠ j := by
    apply inz
    have : (b1 ∪ b2)ᶜ = insert j {k} := by convert hjk
    grind only [= mem_insert]
  have ink : i ≠ k := by
    apply inz
    have : (b1 ∪ b2)ᶜ = insert j {k} := by convert hjk
    grind only [= mem_insert, = mem_singleton]
  have jnk : j ≠ k := by
    by_contra c
    suffices #{k} = 2 by grind only [= card_singleton]
    convert this ▸ congrArg Finset.card (Eq.symm hjk)
    rw[c]; simp only [mem_singleton, insert_eq_of_mem]
  obtain ⟨b3, ⟨hb3a, hb3b⟩, hb3c⟩ := h.2 {i, j} (by exact card_pair inj)
  convert hb3a
  obtain ⟨k', hk'⟩ : (b3 \ {i, j}).Nonempty := by
    have := h.1 b3 hb3a
    grind only [= insert_eq_of_mem, = sdiff_nonempty, = mem_singleton, = card_singleton,
      = card_insert_of_notMem]
  suffices k = k' by
    apply eq_of_subset_of_card_le
    · intro x; simp only [singleton_union, mem_insert, mem_singleton]
      grind only [= subset_iff, = mem_sdiff, = mem_insert, = mem_singleton]
    · rw[h.1 b3 hb3a]
      grind only [= singleton_union, = card_insert_of_notMem]
  suffices k' ∈ (b1 ∪ b2)ᶜ by
    rw[hjk] at this; simp only [mem_insert, mem_singleton] at this
    grind only [= mem_sdiff, = mem_insert, = mem_singleton]
  by_contra c
  simp only [compl_union, mem_inter, mem_compl, not_and, Decidable.not_not] at c
  replace c : k' ∈ b1 ∨ k' ∈ b2 := by grind only
  suffices ∃ bb, bb ∈ bd ∧ k' ∈ bb ∧ i ∈ bb ∧ j ∉ bb by
    obtain ⟨bb, hbb1, hbb2, hbb3, hbb4⟩ := this
    have : #{i, k'} = 2 := by grind only [= card_insert_of_notMem, = mem_sdiff,
      = mem_singleton, = card_singleton, = mem_insert]
    obtain ⟨w, hw1, hw2⟩ := h.2 {i, k'} this
    simp only [and_imp] at hw2
    have hw2a := hw2 bb hbb1 (by grind only [= subset_iff, = mem_sdiff, = mem_insert,
      = mem_singleton])
    have hw2b := hw2 b3 hb3a (by grind only [= subset_iff, = mem_sdiff, = mem_insert,
      = mem_singleton])
    rw[←hw2a] at hw2b
    grind only [= subset_iff, = mem_insert, = mem_singleton]
  rcases c with c | c
  · exists b1
    refine ⟨h1, c, ?_, ?_⟩
    · have : i ∈ b1 ∩ b2 := by grind only [= mem_singleton]
      exact mem_of_mem_filter i this
    · have : j ∈ (b1 ∪ b2)ᶜ := by
        rw[hjk]; simp only [mem_insert, mem_singleton, true_or]
      have : j ∉ (b1 ∪ b2) := by exact mem_compl.mp this
      grind only [= mem_union]
  · exists b2
    refine ⟨h2, c, ?_, ?_⟩
    · have : i ∈ b1 ∩ b2 := by grind only [= mem_singleton]
      exact mem_of_mem_inter_right this
    · have : j ∈ (b1 ∪ b2)ᶜ := by
        rw[hjk]; simp only [mem_insert, mem_singleton, true_or]
      have : j ∉ (b1 ∪ b2) := by exact mem_compl.mp this
      grind only [= mem_union]

def singular : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

lemma forced_helper {pair : Finset (Fin 7)} (hpair : #pair = 2) :
    ∃! b ∈ singular, pair ⊆ b := by
  suffices suff : #{b ∈ singular | pair ⊆ b} = 1 by
    have this2 : 0 < #{b ∈ singular | pair ⊆ b} := Nat.lt_of_sub_eq_succ suff
    obtain ⟨b, hb⟩ := card_pos.mp this2; simp only [mem_filter] at hb
    exists b; simp only [and_imp]; refine ⟨hb, ?_⟩
    intro y hy1 hy2
    suffices {y, b} ⊆ {b ∈ singular | pair ⊆ b} by
      replace := card_le_card this
      rw[suff] at this; grind only [= card_insert_of_notMem, = mem_singleton, = card_singleton]
    grind only [= subset_iff, = insert_eq_of_mem, = mem_filter, = mem_insert, = mem_singleton]
  unfold singular
  obtain ⟨i, j, hij⟩ := find_pair hpair
  have inj : i ≠ j := by grind only [= insert_eq_of_mem, = card_insert_of_notMem,
    = card_singleton, = mem_singleton]
  rw[hij]
  have idis : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by grind only
  have jdis : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by grind only
  rcases idis with c | c | c | c | c | c | c
  all_goals
    rcases jdis with d | d | d | d | d | d | d
    all_goals rw[c, d] at inj; rw[c, d]
    all_goals try contradiction
    all_goals decide

lemma forced : #{bd ∈ fano_planes | {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}} ⊆ bd} = 1 := by
  suffices {bd ∈ fano_planes | {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}} ⊆ bd} = {singular} by
    rw[this, card_singleton]
  unfold singular
  ext bd; simp only [Fin.isValue, mem_filter, mem_singleton]; constructor
  case mpr =>
    intro hbd; constructor
    · unfold fano_planes; simp only [mem_filter, mem_univ, true_and]
      constructor
      · subst hbd; intro b hb; simp only [mem_insert, mem_singleton] at hb
        grind only [= card_insert_of_notMem, = mem_insert, = mem_singleton, = card_singleton]
      · intro pair hpair
        convert forced_helper hpair
        unfold singular; exact hbd
    · grind only [= subset_iff, = mem_insert, = mem_singleton]
  case mp =>
    intro ⟨hbd1, hbd2⟩
    have m1 : {0, 1, 2} ∈ bd := by grind only [= subset_iff, = mem_insert]
    have m2 : {0, 3, 4} ∈ bd := by grind only [= subset_iff, = mem_insert]
    have m3 : {1, 3, 5} ∈ bd := by grind only [= subset_iff, = mem_insert, = mem_singleton]
    have m4 : {0, 5, 6} ∈ bd := by convert forced_block hbd1 0 m1 m2 (by decide); decide
    have m5 : {1, 4, 6} ∈ bd := by convert forced_block hbd1 1 m1 m3 (by decide); decide
    have m6 : {2, 3, 6} ∈ bd := by convert forced_block hbd1 3 m2 m3 (by decide); decide
    have m7 : {2, 4, 5} ∈ bd := by convert forced_block hbd1 2 m1 m6 (by decide); decide
    ext x; constructor
    · intro hx; unfold fano_planes at hbd1
      simp only [mem_filter, mem_univ, true_and] at hbd1
      have := hbd1.1 x hx
      obtain ⟨i, hi⟩ := card_pos.mp (Nat.lt_of_sub_eq_succ this)
      have hpair : #(x \ {i}) = 2 := by grind only [= card_sdiff_of_subset, = card_sdiff,
        usr le_card_sdiff, = singleton_subset_iff, = card_singleton]
      obtain ⟨w, hw⟩ := hbd1.2 (x \ {i}) hpair
      simp only [sdiff_le_iff, sup_eq_union', singleton_union, and_imp] at hw
      obtain ⟨x', hx'⟩ := forced_helper hpair; simp only [sdiff_le_iff, sup_eq_union',
        singleton_union, and_imp] at hx'
      have hw1 := hw.2 x hx (by simp only [subset_insert])
      have x'inbd : x' ∈ bd := by
        have := hx'.1.1; unfold singular at this
        simp only [Fin.isValue, mem_insert, mem_singleton] at this
        grind only [= subset_iff, = mem_insert, = mem_singleton]
      have hw2 := hw.2 x' x'inbd hx'.1.2
      rw[hw1, ←hw2]
      convert hx'.1.1; unfold singular; simp only [Fin.isValue]
    · intro hx; simp only [Fin.isValue, mem_insert, mem_singleton] at hx
      rcases hx with hx | hx | hx | hx | hx | hx | hx
      <;> rw[hx] <;> assumption

theorem fano_enum : #fano_planes = 30 := by rw[symmetry1, symmetry2, symmetry3, forced]
