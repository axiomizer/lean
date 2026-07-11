section
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    have h₁ := λ h => ⟨λ hx => (h hx).left, λ hx => (h hx).right⟩
    have h₂ := λ h => λ hx => ⟨h.left hx, h.right hx⟩
    ⟨h₁, h₂⟩
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    λ h => λ haxpx => λ hx => (h hx) (haxpx hx)
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    λ h => λ hx => h.elim (λ hh => Or.inl (hh hx)) (λ hh => Or.inr (hh hx))
end

section
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ _ : α, r) ↔ r) :=
    λ h => ⟨λ hax => hax h, λ hr => λ _ => hr⟩

  section open Classical
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
      have h₁ := λ hax => Or.elim (em r)
        (λ hr => Or.inr hr)
        (λ hnr => Or.inl (λ hx => Or.elim (hax hx)
          (λ hpx => hpx) (λ hr => False.elim (hnr hr))))
      have h₂ := λ h => Or.elim h
        (λ haxpx => λ hx => Or.inl (haxpx hx))
        (λ hr => λ _ => Or.inr hr)
      ⟨h₁, h₂⟩
  end

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    have h₁ := λ h => λ hr => λ hx => ((h hx) hr)
    have h₂ := λ h => λ hx => λ hr => ((h hr) hx)
    ⟨h₁, h₂⟩
end

section
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    have h₁ := λ hsbb => Iff.mp (h barber) hsbb hsbb
    h₁ ((Iff.mpr (h barber)) h₁)
end

section
  def even (n : Nat) : Prop := ∃ k : Nat, n = 2*k

  def prime (n : Nat) : Prop := ¬(∃ a b : Nat, a > 1 ∧ b > 1 ∧ a*b = n)

  def infinitely_many_primes : Prop := ∀ n : Nat, ∃ p : Nat, p > n ∧ prime p

  def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃ k : Nat, k > 0 ∧ n = 2^k+1

  def infinitely_many_Fermat_primes : Prop := ∀ n : Nat, ∃ p : Nat, p > n ∧ Fermat_prime p

  def goldbach_conjecture : Prop :=
    ∀ n : Nat, even n ∧ n > 2 → ∃ p₁ p₂ : Nat, prime p₁ ∧ prime p₂ ∧ p₁ + p₂ = n

  def Goldbach's_weak_conjecture : Prop :=
    ∀ n : Nat, ¬even n ∧ n > 5 →
      ∃ p₁ p₂ p₃ : Nat, prime p₁ ∧ prime p₂ ∧ prime p₃ ∧ p₁ + p₂ + p₃ = n

  def Fermat's_last_theorem : Prop :=
    ∀ a b c n : Nat, a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 2 → ¬(a^n + b^n = c^n)
end

section open Classical
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : (∃ _ : α, r) → r := λ ⟨_, hr⟩ => hr
  example (a : α) : r → (∃ _ : α, r) := λ hr => ⟨a, hr⟩
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    have h₁ := λ ⟨hx, px, hr⟩ => ⟨⟨hx, px⟩, hr⟩
    have h₂ := λ ⟨⟨hx, px⟩, hr⟩ => ⟨hx, px, hr⟩
    ⟨h₁, h₂⟩
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    have h₁ := λ ⟨hx, hpq⟩ => hpq.elim (λ px => Or.inl ⟨hx, px⟩) (λ qx => Or.inr ⟨hx, qx⟩)
    have h₂ := λ h => h.elim (λ ⟨hx, px⟩ => ⟨hx, Or.inl px⟩) (λ ⟨hx, qx⟩ => ⟨hx, Or.inr qx⟩)
    ⟨h₁, h₂⟩

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    have h₁ := λ h => λ ⟨hx, hnpx⟩ => hnpx (h hx)
    have h₂ := λ h => λ hx => Or.elim (em (p hx))
      (λ phx => phx)
      (λ nphx => False.elim (h ⟨hx, nphx⟩))
    ⟨h₁, h₂⟩
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    have h₁ := λ ⟨hx, px⟩ => λ h => h hx px
    have h₂ : ¬(∃ x, p x) → ∀ x, ¬ p x :=
      λ h => λ hx => λ px => h ⟨hx, px⟩
    have h₃ := λ h => Or.elim (em (∃ x, p x))
      (λ hh => hh)
      (λ nexpx => False.elim (h (h₂ nexpx)))
    ⟨h₁, h₃⟩
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    have h₁ := λ h => λ hx => λ px => h ⟨hx, px⟩
    have h₂ := λ h => λ ⟨hx, px⟩ => h hx px
    ⟨h₁, h₂⟩
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    have h₁ : ¬(∃ x, ¬ p x) → ∀ x, p x :=
      λ h => λ hx => Or.elim (em (p hx))
        (λ px => px)
        (λ npx => False.elim (h ⟨hx, npx⟩))
    have h₂ := λ h => Or.elim (em (∃ x, ¬ p x))
      (λ exnpx => exnpx)
      (λ nexnpx => False.elim (h (h₁ nexnpx)))
    have h₃ := λ ⟨hx, npx⟩ => λ axpx => npx (axpx hx)
    ⟨h₂, h₃⟩

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    have h₁ := λ h => λ ⟨hx, px⟩ => h hx px
    have h₂ := λ h => λ hx => λ px => h ⟨hx, px⟩
    ⟨h₁, h₂⟩
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    have h₁ := λ ⟨hx, pxtr⟩ => λ axpx => pxtr (axpx hx)
    have h₂ : ¬(∃ x, p x → r) → ∀ x, p x :=
      λ h => λ hx => Or.elim (em (p hx))
        (λ px => px)
        (λ npx => False.elim (h ⟨hx, λ px => False.elim (npx px)⟩))
    have h₃ := λ h => Or.elim (em r)
      (λ hr => ⟨a, λ _ => hr⟩)
      (λ hnr => Or.elim (em (∃ x, p x → r))
        (λ hh => hh)
        (λ nex => False.elim (hnr (h (h₂ nex)))))
    ⟨h₁, h₃⟩
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    have h₁ := λ ⟨hx, rtpx⟩ => λ hr => ⟨hx, rtpx hr⟩
    have h₂ := λ h => Or.elim (em r)
      (λ hr => let ⟨hx, px⟩ := (h hr); ⟨hx, λ _ => px⟩)
      (λ hnr => ⟨a, λ hr => False.elim (hnr hr)⟩)
    ⟨h₁, h₂⟩
end
