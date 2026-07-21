import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Pairwise.Basic

open Finset Classical

def block_design (t k n : ℕ) (bd : Finset (Finset (Fin n))) : Prop :=
  (∀ b ∈ bd, #b = k) ∧ (∀ s : Finset (Fin n), #s = t → ∃! b ∈ bd, s ⊆ b)

noncomputable def fano_planes : Finset (Finset (Finset (Fin 7))) := {bd | block_design 2 3 7 bd}

noncomputable def parti (fixed : Finset (Finset (Fin 7))) (pair : Finset (Fin 7)) :=
  fun i ↦ {bd ∈ fano_planes | fixed ⊆ bd ∧ pair ∪ {i} ∈ bd}

def ι' (fixed : Finset (Finset (Fin 7))) (pair : Finset (Fin 7)) :=
  univ \ (fixed.biUnion id ∪ pair)

lemma union (fixed : Finset (Finset (Fin 7))) (pair : Finset (Fin 7)) (hp : #pair = 2)
    (hint : ∀ f ∈ fixed, ∃! x, x ∈ f ∩ pair) :
    {bd ∈ fano_planes | fixed ⊆ bd} = (ι' fixed pair).biUnion (parti fixed pair) := by
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
    exists a; refine ⟨?_, hpl.1, hpl.2, ha ▸ bha1⟩; unfold ι'
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
    ((ι' fixed pair).biUnion (parti fixed pair)).card =
    ∑ u ∈ (ι' fixed pair), ((parti fixed pair) u).card := by
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
  have hdis : Disjoint (ι' fixed pair) pair := by
    unfold ι' Disjoint; grind only [= subset_iff, = mem_sdiff, = mem_union]
  have := disjoint_left.mp hdis hi
  grind only [= mem_union, = mem_singleton]

lemma img_cancel {α : Type} [DecidableEq α] (f : Equiv.Perm α) (S : Finset α) :
    image f (image f.symm S) = S := by
  ext x; constructor
  <;> simp only [mem_image, exists_exists_and_eq_and, Equiv.apply_symm_apply, exists_eq_right,
    imp_self]
  --have := Finset.image_preimage_of_bijective S f.bijective

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
    (w : Fin 7) (hw : w ∈ ι' fixed pair) :
    ∑ u ∈ (ι' fixed pair), #(parti fixed pair u) =
    #(ι' fixed pair) * #{bd ∈ fano_planes | (fixed ∪ {pair ∪ {w}}) ⊆ bd} := by
  apply Finset.sum_eq_card_nsmul; unfold parti
  intro i hi
  let f : Equiv.Perm (Fin 7) := Equiv.swap w i
  have imfix : ∀ x, x ∉ ι' fixed pair → f x = x := by
    intro x hx; unfold ι' at hx hi hw
    grind only [= Equiv.swap_apply_def]
  have ipp : image f pair = pair := by
    unfold f; unfold ι' at imfix hw hi
    grind only [usr card_image_iff, = mem_image, = mem_sdiff, ← mem_univ, = mem_union]
  have iff : ∀ x, x ∈ fixed → image f x = x := by
    unfold f; unfold ι' at imfix hw hi
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
  have bij := biject ∅ {0, 1} 2 (by unfold ι'; decide)
  simp only [Fin.isValue, insert_union, singleton_union, empty_union] at bij
  rw[bij, show #(ι' ∅ {0, 1}) = 5 from rfl]

lemma symmetry2 : #{bd ∈ fano_planes | {{0, 1, 2}} ⊆ bd} =
    3 * #{bd ∈ fano_planes | {{0, 1, 2}, {0, 3, 4}} ⊆ bd} := by
  have un := union {{0, 1, 2}} {0, 3} rfl ?_
  case refine_1 =>
    simp only [Fin.isValue, mem_singleton, mem_inter, mem_insert, forall_eq]; exists 0
  have csum := cardsum {{0, 1, 2}} {0, 3} rfl
  have bij := biject {{0, 1, 2}} {0, 3} 4 (by unfold ι'; decide)
  simp only [Fin.isValue, insert_union, singleton_union] at bij
  rw[un, csum, bij, show #(ι' {{0, 1, 2}} {0, 3}) = 3 from rfl]

lemma symmetry3 : #{bd ∈ fano_planes | {{0, 1, 2}, {0, 3, 4}} ⊆ bd} =
    2 * #{bd ∈ fano_planes | {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}} ⊆ bd} := by
  have un := union {{0, 1, 2}, {0, 3, 4}} {1, 3} rfl ?_
  case refine_1 =>
    simp only [Fin.isValue, mem_insert, mem_singleton, mem_inter, forall_eq_or_imp, forall_eq]
    refine ⟨⟨1, ?_⟩, ⟨3, ?_⟩⟩ <;> grind only
  have csum := cardsum {{0, 1, 2}, {0, 3, 4}} {1, 3} rfl
  have bij := biject {{0, 1, 2}, {0, 3, 4}} {1, 3} 5 (by unfold ι'; decide)
  simp only [Fin.isValue, insert_union, singleton_union] at bij
  rw[un, csum, bij, show #(ι' {{0, 1, 2}, {0, 3, 4}} {1, 3}) = 2 from rfl]

lemma forced : #{bd ∈ fano_planes | {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}} ⊆ bd} = 1 := by
  suffices {bd ∈ fano_planes | {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}} ⊆ bd} =
      {{{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}} by
    rw[this, card_singleton]
  ext bd; simp only [Fin.isValue, mem_filter, mem_singleton]; constructor
  case mpr =>
    intro hbd; constructor
    · unfold fano_planes block_design; simp only [mem_filter, mem_univ, true_and]
      constructor
      · subst hbd; intro b hb; simp only [mem_insert, mem_singleton] at hb
        grind only [= card_insert_of_notMem, = mem_insert, = mem_singleton, = card_singleton]
      · intro pair hpair
        sorry
    · grind only [= subset_iff, = mem_insert, = mem_singleton]
  case mp =>
    intro ⟨h1, h2⟩; unfold fano_planes block_design at h1
    simp only [mem_filter, mem_univ, true_and] at h1
    have h5 : {0, 5, 6} ∈ bd := by
      obtain ⟨b, hb1, hb2⟩ := h1.2 {0, 5} rfl
      suffices b = {0, 5, 6} from this ▸ hb1.1
      sorry
    sorry

theorem fano_enum : #fano_planes = 30 := by rw[symmetry1, symmetry2, symmetry3, forced]
