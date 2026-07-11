variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  ⟨λ h => ⟨h.right, h.left⟩, λ h => ⟨h.right, h.left⟩⟩
example : p ∨ q ↔ q ∨ p :=
  have h₁ := λ h => h.elim (λ hp => Or.inr hp) (λ hq => Or.inl hq)
  have h₂ := λ h => h.elim (λ hq => Or.inr hq) (λ hp => Or.inl hp)
  ⟨h₁, h₂⟩


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  have h₁ : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
    λ h => And.intro h.left.left ((And.intro h.left.right) h.right)
  have h₂ : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
    λ h => And.intro (And.intro h.left h.right.left) h.right.right
  Iff.intro h₁ h₂
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  have h₁ : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
    λ h => h.elim
      (λ hh => hh.elim (λ hhh => Or.inl hhh) (λ hhh => Or.inr (Or.inl hhh)))
      (λ hh => Or.inr (Or.inr hh))
  have h₂ : p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
    λ h => h.elim
      (λ hh => Or.inl (Or.inl hh))
      (λ hh => hh.elim (λ hhh => Or.inl (Or.inr hhh)) (λ hhh => Or.inr hhh))
  ⟨h₁, h₂⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have h₁ : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    λ h => h.right.elim
      (λ hq => Or.inl ⟨h.left, hq⟩)
      (λ hr => Or.inr ⟨h.left, hr⟩)
  have h₂ : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) :=
    λ h => h.elim
      (λ hpq => ⟨hpq.left, Or.inl hpq.right⟩)
      (λ hpr => ⟨hpr.left, Or.inr hpr.right⟩)
  ⟨h₁, h₂⟩
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  have h₁ : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) :=
    λ h => h.elim
      (λ hp => ⟨Or.inl hp, Or.inl hp⟩)
      (λ hqr => ⟨Or.inr hqr.left, Or.inr hqr.right⟩)
  have h₂ : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) :=
    λ h => h.left.elim
      (λ hp => Or.inl hp)
      (λ hq => h.right.elim (λ hp => Or.inl hp) (λ hr => Or.inr ⟨hq, hr⟩))
  ⟨h₁, h₂⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  have h₁ := λ h => (λ hpq => h hpq.left hpq.right)
  have h₂ := λ h => (λ hp => (λ hq => h ⟨hp, hq⟩))
  ⟨h₁, h₂⟩
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  have h₁ := λ h => (⟨λ hp => h (Or.inl hp), λ hq => h (Or.inr hq)⟩)
  have h₂ := λ h => (λ hpq => hpq.elim (λ hp => h.left hp) (λ hq => h.right hq))
  ⟨h₁, h₂⟩
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  have h₁ := λ h => ⟨λ hp => h (Or.inl hp), λ hq => h (Or.inr hq)⟩
  have h₂ := λ h => (λ hpq => hpq.elim (λ hp => h.left hp) (λ hq => h.right hq))
  ⟨h₁, h₂⟩
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ h => (λ hpq => h.elim (λ hnp => hnp hpq.left) (λ hnq => hnq hpq.right))
example : ¬(p ∧ ¬p) :=
  λ h => h.right h.left
example : p ∧ ¬q → ¬(p → q) :=
  λ h => (λ hpq => h.right (hpq h.left))
example : ¬p → (p → q) :=
  λ h => (λ hp => False.elim (h hp))
example : (¬p ∨ q) → (p → q) :=
  λ h => (λ hp => h.elim (λ hnp => False.elim (hnp hp)) (λ hq => hq))
example : p ∨ False ↔ p :=
  have h₁ := λ h => h.elim (λ hp => hp) (λ hf => False.elim hf)
  have h₂ := λ h => Or.inl h
  ⟨h₁, h₂⟩
example : p ∧ False ↔ False :=
  have h₁ := λ h => h.right
  have h₂ := λ h => ⟨False.elim h, h⟩
  ⟨h₁, h₂⟩
example : (p → q) → (¬q → ¬p) :=
  λ h => λ hnq => λ hp => hnq (h hp)

section open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  have h₁ : q → ((p → q) ∨ (p → r)) :=
    λ hq => Or.inl λ _ => hq
  have h₂ : r → ((p → q) ∨ (p → r)) :=
    λ hr => Or.inr λ _ => hr
  λ h => Or.elim (em p)
    (λ hp => (h hp).elim (λ hq => h₁ hq) (λ hr => h₂ hr))
    (λ hnp => Or.inl λ hp => False.elim (hnp hp))
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ h => Or.elim (em p)
    (λ hp => Or.inr (λ hq => h ⟨hp, hq⟩))
    (λ hnp => Or.inl hnp)
example : ¬(p → q) → p ∧ ¬q :=
  λ h => Or.elim (em p)
    (λ hp => Or.elim (em q) (λ hq => False.elim (h (λ _ => hq))) (λ hnq => ⟨hp, hnq⟩))
    (λ hnp => False.elim (h (λ hp => False.elim (hnp hp))))
example : (p → q) → (¬p ∨ q) :=
  λ h => Or.elim (em p)
    (λ hp => Or.inr (h hp))
    (λ hnp => Or.inl hnp)
example : (¬q → ¬p) → (p → q) :=
  λ h => λ hp => (Or.elim (em q) (λ hq => hq) (λ hnq => False.elim ((h hnq) hp)))
example : p ∨ ¬p :=
  em p
example : (((p → q) → p) → p) :=
  Or.elim (em p)
    (λ hp => λ _ => hp)
    (λ hnp => λ hpqp => False.elim (hnp (hpqp (λ hp => False.elim (hnp hp)))))

end

example : ¬(p ↔ ¬p) :=
  have h₁ : (p ↔ ¬p) → ¬p := λ h => λ hp => Iff.mp h hp hp
  λ h => (h₁ h) (Iff.mpr h (h₁ h))
