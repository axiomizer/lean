import Mathlib

section
open Set Function Equiv
def orbit {α : Type} (σ : Perm α) (x : α) :=
  {y | ∃ n : ℕ, y = σ^[n] x ∨ y = (σ.symm)^[n] x}

lemma o_trans {α : Type} {σ : Perm α} {x y z : α}
  (p₁ : x ∈ orbit σ y) (p₂ : y ∈ orbit σ z) : x ∈ orbit σ z :=
  have combine {n₁ n₂ : ℕ} {γ : Perm α} (hxy : x = γ^[n₁] y) (hyz : y = γ^[n₂] z) :
    x = γ^[n₁+n₂] z := by simp[hxy, hyz, iterate_add_apply γ]
  have cancel₁ {n₁ n₂ : ℕ} {γ : Perm α} (hcmp : n₁ ≥ n₂) (hxy : x = γ^[n₁] y)
    (hyz : y = γ.symm^[n₂] z) : x = γ^[n₁-n₂] z := calc
      x = γ^[n₁-n₂+n₂] (γ.symm^[n₂] z)       := by rw[hxy, hyz, Nat.sub_add_cancel hcmp]
      _ = γ^[n₁-n₂] (γ^[n₂] (γ.symm^[n₂] z)) := by rw[iterate_add_apply]
      _ = γ^[n₁-n₂] z                        := by rw[RightInverse.iterate γ.right_inv' n₂]
  have cancel₂ {n₁ n₂ : ℕ} {γ : Perm α} (hcmp : n₂ ≥ n₁) (hxy : x = γ^[n₁] y)
    (hyz : y = γ.symm^[n₂] z) : x = γ.symm^[n₂-n₁] z :=
    have hinv := RightInverse.iterate γ.right_inv' n₁; calc
      x = γ^[n₁] (γ.symm^[n₁+(n₂-n₁)] z) := by rw[hxy, hyz, Nat.add_sub_of_le hcmp]
      _ = γ.symm^[n₂-n₁] z               := by rw[iterate_add_apply, hinv]
  let ⟨n₁, h₁⟩ := p₁; let ⟨n₂, h₂⟩ := p₂; Or.elim h₁
    (fun oxp => Or.elim h₂
      (fun oyp => ⟨n₁+n₂, Or.inl (combine oxp oyp)⟩)
      (fun oyn => Or.elim (le_total n₂ n₁)
        (fun hng => ⟨n₁-n₂, Or.inl (cancel₁ hng oxp oyn)⟩)
        (fun hnl => ⟨n₂-n₁, Or.inr (cancel₂ hnl oxp oyn)⟩)))
    (fun oxn => Or.elim h₂
      (fun oyp => Or.elim (le_total n₁ n₂)
        (fun hng => ⟨n₂-n₁, Or.inl (cancel₂ hng oxn oyp)⟩)
        (fun hnl => ⟨n₁-n₂, Or.inr (cancel₁ hnl oxn oyp)⟩))
      (fun oyn => ⟨n₁+n₂, Or.inr (combine oxn oyn)⟩))

lemma o_symm {α : Type} {σ : Perm α} {x y : α} (p₁ : x ∈ orbit σ y) : y ∈ orbit σ x :=
  have opp {n : ℕ} {γ : Perm α} (h : x = γ^[n] y) : y = γ.symm^[n] x :=
    by rw [h, LeftInverse.iterate γ.left_inv' n y]
  let ⟨n₁, h⟩ := p₁; Or.elim h
    (fun hh => ⟨n₁, Or.inr (opp hh)⟩)
    (fun hh => ⟨n₁, Or.inl (opp hh)⟩)

theorem t1 {α : Type} (σ : Perm α) (x y : α) :
    (orbit σ x ∩ orbit σ y).Nonempty → (orbit σ x) = (orbit σ y) :=
  fun h => let ⟨_, sox, soy⟩ := nonempty_def.mp h; Subset.antisymm
    (fun _ => fun ox => o_trans ox (o_trans (o_symm sox) soy))
    (fun _ => fun oy => o_trans oy (o_trans (o_symm soy) sox))
end
