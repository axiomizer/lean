import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Pairwise.Basic

open Finset Classical

def block_design (t k n : ℕ) (bd : Finset (Finset (Fin n))) : Prop :=
  (∀ b ∈ bd, #b = k) ∧ (∀ s : Finset (Fin n), #s = t → ∃! b ∈ bd, s ⊆ b)

noncomputable def fano_planes : Finset (Finset (Finset (Fin 7))) := {bd | block_design 2 3 7 bd}

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

lemma symmetry1 : #fano_planes = 5 * #{bd ∈ fano_planes | {0, 1, 2} ∈ bd} := by
  let ι : Finset (Fin 7) := {i : Fin 7 | 1 < i}
  let map := (fun i ↦ {bd ∈ fano_planes | {0, 1, i} ∈ bd})
  have split1 : fano_planes = ι.biUnion map := by
    unfold ι map fano_planes; ext pl
    simp only [mem_filter, mem_univ, true_and, Fin.isValue, mem_biUnion]
    constructor
    · intro hpl
      obtain ⟨b, ⟨bha1, bha2⟩, bhb⟩ := hpl.2 {0, 1} rfl
      have bcard := hpl.1 b bha1
      obtain ⟨a, ha⟩ : ∃ a, b = {0, 1, a} := by
        suffices ∃ a, b \ {0, 1} = {a} by grind only [= subset_iff, = insert_eq_of_mem,
          = mem_singleton, = mem_insert, = mem_sdiff]
        apply card_eq_one.mp
        grind only [= insert_eq_of_mem, = card_sdiff_of_subset, = mem_singleton,
          = card_insert_of_notMem, = card_singleton]
      exists a; refine ⟨?_, hpl, ha ▸ bha1⟩
      grind only [= insert_eq_of_mem, = card_insert_of_notMem, = mem_filter, = mem_insert,
        = mem_singleton, ← mem_univ, = card_singleton]
    · intro ⟨_, _, ha2, _⟩; exact ha2
  have disj1 : (ι.biUnion map).card = ∑ u ∈ ι, (map u).card := by
    apply Finset.card_biUnion
    intro i hi j hj hij
    unfold Function.onFun Disjoint map; simp only [Fin.isValue, bot_eq_empty, subset_empty]
    intro bds hbds1 hbds2
    by_contra! cont; obtain ⟨bd, hbd⟩ := cont
    have hbd2: bd ∈ fano_planes := by grind only [= mem_biUnion, = mem_coe, = subset_iff]
    replace hbds1 : {0, 1, i} ∈ bd := by grind only [= subset_iff, = mem_filter]
    replace hbds2 : {0, 1, j} ∈ bd := by grind only [= subset_iff, = mem_filter]
    unfold fano_planes at hbd2; unfold block_design at hbd2
    simp only [mem_filter, mem_univ, true_and] at hbd2
    rcases (hbd2.2 {0, 1} rfl) with ⟨w, hwa, hw⟩
    simp only [Fin.isValue, and_imp] at hw
    have hw1 := hw {0, 1, i} hbds1 (by simp only [Fin.isValue, singleton_subset_iff, mem_insert,
      mem_singleton, true_or, insert_subset_insert])
    have hw2 := hw {0, 1, j} hbds2 (by simp only [Fin.isValue, singleton_subset_iff, mem_insert,
      mem_singleton, true_or, insert_subset_insert])
    have := hw2 ▸ hw1; clear hw1 hw2 hw hwa hbd2 hbds1 hbds2 hbd bd w bds
    replace : i ∈ ({0, 1, j} : Finset (Fin 7)) := by grind only [= mem_insert, = mem_singleton]
    replace : i = j := by grind only [= mem_coe, = mem_insert, = mem_filter, = mem_singleton]
    exact hij this
  rw[←split1] at disj1; rw[disj1]
  have bij1 : ∑ u ∈ ι, #(map u) = #ι * #{bd ∈ fano_planes | {0, 1, 2} ∈ bd} := by
    apply Finset.sum_eq_card_nsmul
    intro i hi; unfold map
    let f : Equiv.Perm (Fin 7) := Equiv.swap 2 i
    apply card_nbij (image (image f))
    · intro bd; simp only [Fin.isValue, coe_filter, Set.mem_setOf_eq, mem_image, and_imp]
      intro hbd1 hbd2; constructor
      · exact mapsto f hbd1
      · refine ⟨{0, 1, i}, hbd2, ?_⟩
        simp only [Fin.isValue, image_insert, image_singleton]; ext x
        grind only [= mem_biUnion, = mem_filter, = mem_insert, = insert_eq_of_mem,
          = Equiv.swap_apply_def, = mem_singleton]
    · intro x _ y _ hxy
      exact image_injective (image_injective (Equiv.injective f)) hxy
    · intro bd hbd; simp only [Fin.isValue, coe_filter, Set.mem_setOf_eq] at hbd
      simp only [Fin.isValue, coe_filter, Set.mem_image, Set.mem_setOf_eq]
      refine ⟨image (image f.symm) bd, ?_⟩; and_intros
      · exact mapsto f.symm hbd.1
      · simp only [Fin.isValue, mem_image]
        refine ⟨{0, 1, 2}, hbd.2, ?_⟩
        rw[←img_cancel f.symm {0, 1, i}]
        suffices {0, 1, 2} = image f {0, 1, i} by
          rw[f.symm_symm]; exact congrArg (image f.symm ·) this
        simp only [Fin.isValue, image_insert, image_singleton]
        grind only [= mem_biUnion, = mem_filter, = insert_eq_of_mem, = Equiv.swap_apply_def,
          = mem_singleton, = mem_insert]
      · exact img_img_cancel f bd
  rw[bij1, show #ι = 5 from rfl]

lemma symmetry2 : #{bd ∈ fano_planes | {0, 1, 2} ∈ bd} =
    3 * #{bd ∈ fano_planes | {0, 1, 2} ∈ bd ∧ {0, 3, 4} ∈ bd} := by
  sorry

lemma symmetry3 : #{bd ∈ fano_planes | {0, 1, 2} ∈ bd ∧ {0, 3, 4} ∈ bd} =
    2 * #{bd ∈ fano_planes | {0, 1, 2} ∈ bd ∧ {0, 3, 4} ∈ bd ∧ {1, 3, 5} ∈ bd} := by
  sorry

lemma forced : #{bd ∈ fano_planes | {0, 1, 2} ∈ bd ∧ {0, 3, 4} ∈ bd ∧ {1, 3, 5} ∈ bd} = 1 := by
  suffices {bd ∈ fano_planes | {0, 1, 2} ∈ bd ∧ {0, 3, 4} ∈ bd ∧ {1, 3, 5} ∈ bd} =
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
    · grind only [= mem_insert]
  case mp =>
    intro ⟨h1, h2, h3, h4⟩; unfold fano_planes block_design at h1
    simp only [mem_filter, mem_univ, true_and] at h1
    have h5 : {0, 5, 6} ∈ bd := by
      obtain ⟨b, hb1, hb2⟩ := h1.2 {0, 5} rfl
      suffices b = {0, 5, 6} from this ▸ hb1.1
      sorry
    sorry

theorem fano_enum : #fano_planes = 30 := by rw[symmetry1, symmetry2, symmetry3, forced]
