variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  ⟨
    (λ h : p ∧ q => ⟨h.2, h.1⟩),
    (λ h : q ∧ p => ⟨h.2, h.1⟩)
  ⟩

theorem t1 : p ∨ q ↔ q ∨ p :=
  ⟨
    (λ hpq : p ∨ q => hpq.elim (λ hp : p => Or.inr hp) (λ hq : q => Or.inl hq)),
    (λ hqp : q ∨ p => hqp.elim (λ hq : q => Or.inr hq) (λ hp : p => Or.inl hp))
  ⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨
    (λ h : (p ∧ q) ∧ r => ⟨h.1.1, ⟨h.1.2, h.2⟩⟩),
    (λ h : p ∧ (q ∧ r) => ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
  ⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨
    (
      λ h : (p ∨ q) ∨ r =>
      h.elim
        (
          λ hpq : p ∨ q =>
          hpq.elim (λ hp : p => Or.inl hp) (λ hq : q => Or.inr (Or.inl hq))
        )
        (λ hr : r => Or.inr (Or.inr hr))
    ),
    (
      λ h : p ∨ (q ∨ r) =>
      h.elim
        (λ hp : p => Or.inl (Or.inl hp))
        (
          λ hqr : q ∨ r =>
          hqr.elim (λ hq : q => Or.inl (Or.inr hq)) (λ hr : r => Or.inr hr)
        )
    )
  ⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨
    (
      λ h : p ∧ (q ∨ r) =>
      h.2.elim (λ hq : q => Or.inl ⟨h.1, hq⟩) (λ hr : r => Or.inr ⟨h.1, hr⟩)
    ),
    (
      λ h : (p ∧ q) ∨ (p ∧ r) =>
      h.elim
        (λ hpq : p ∧ q => ⟨hpq.1, Or.inl hpq.2⟩)
        (λ hpr : p ∧ r => ⟨hpr.1, Or.inr hpr.2⟩)
    )
  ⟩


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨
    (
      λ h : p ∨ (q ∧ r) =>
      h.elim
        (λ hp : p => ⟨Or.inl hp, Or.inl hp⟩)
        (λ hqr : q ∧ r => ⟨Or.inr hqr.1, Or.inr hqr.2⟩)
    ),
    (
      λ h : (p ∨ q) ∧ (p ∨ r) =>
      h.1.elim
        (λ hp : p => Or.inl hp)
        (
          λ hq : q =>
          h.2.elim (λ hp : p => Or.inl hp) (λ hr : r => Or.inr ⟨hq, hr⟩)
        )
    )
  ⟩

-- other properties

-- Importation / Exportation
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨
    (
      λ h : p → (q → r) =>
      λ hpq : p ∧ q =>
      h (hpq.1) (hpq.2)
    ),
    (
      λ h : p ∧ q → r =>
      λ hp : p => λ hq : q => h ⟨hp, hq⟩
    )
  ⟩

-- ?
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨
    (
      λ h : (p ∨ q) → r =>
        ⟨
          (λ hp : p => h (Or.inl hp)),
          (λ hq : q => h (Or.inr hq))
        ⟩
    ),
    (
      λ h : (p → r) ∧ (q → r) =>
      λ hpq : p ∨ q =>
      hpq.elim (λ hp : p => h.1 hp) (λ hq : q => h.2 hq)
    )
  ⟩

-- De Morgan's Theorem
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨
    (
      λ h : ¬(p ∨ q) =>
      ⟨
        λ hp : p => h (Or.inl hp),
        λ hq : q => h (Or.inr hq)
      ⟩
    ),
    (
      λ h : ¬p ∧ ¬q =>
      λ hpq : p ∨ q =>
      hpq.elim (λ hp : p => h.1 hp) (λ hq : q => h.2 hq)
    )
  ⟩

-- De Morgan's Theorem
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ h : ¬p ∨ ¬q =>
  λ hpq : p ∧ q =>
  h.elim
    (λ hp : ¬p => hp hpq.1)
    (λ hq : ¬q => hq hpq.2)

-- Law of Non-Contradiction
example : ¬(p ∧ ¬p) :=
  λ hpq : p ∧ ¬p => hpq.2 hpq.1

-- ?
example : p ∧ ¬q → ¬(p → q) :=
  λ hpq : p ∧ ¬q =>
  λ h : p → q => hpq.2 (h hpq.1)

-- ?
example : ¬p → (p → q) :=
  λ hnp : ¬p => λ hp : p => absurd hp hnp

-- Material Implication
example : (¬p ∨ q) → (p → q) :=
  λ h : ¬p ∨ q =>
  λ hp : p =>
  h.elim (λ hnp : ¬p => absurd hp hnp) (λ hq : q => hq)

-- ?
example : p ∨ False ↔ p :=
  ⟨
    λ h : p ∨ False => h.elim (λ hp : p => hp) False.elim,
    λ h : p => Or.inl h
  ⟩

-- ?
example : p ∧ False ↔ False :=
  ⟨λ h : p ∧ False => h.2, False.elim⟩

-- Transposition
example : (p → q) → (¬q → ¬p) :=
  λ h : p → q =>
  λ hq : ¬q =>
  λ hp : p => absurd (h hp) hq

-- ?
example : ¬(p ↔ ¬p) :=
  λ ⟨h₁, h₂⟩ =>
  let hp : p := h₂ (λ hp: p => absurd hp (h₁ hp))
  absurd hp (h₁ hp)

open Classical

variable (p q r : Prop)

-- Composition of disjunction
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ h : p → q ∨ r =>
  (em p).elim
    (
      λ hp : p => (h hp).elim
        (λ hq : q => Or.inl (λ _ : p => hq))
        (λ hr : r => Or.inr (λ _ : p => hr))
    )
    (
      λ hnp : ¬p =>
        Or.inr (λ hp : p => absurd hp hnp)
    )

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ h : ¬(p ∧ q) =>
  (em p).elim
    (λ hp : p => Or.inr (λ hq : q => h ⟨hp, hq⟩))
    (λ hnp : ¬p => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  λ h : ¬(p → q) =>
  (em q).elim
    (λ hq : q => absurd (λ _ : p => hq) h)
    (
      λ hnq : ¬q =>
        (em p).elim
          (λ hp : p => ⟨hp, hnq⟩)
          (λ hnp : ¬p => absurd (λ hp : p => absurd hp hnp) h)
    )

example : (p → q) → (¬p ∨ q) :=
  λ h : p → q =>
  (em p).elim
    (λ hp : p => Or.inr (h hp))
    (λ hnp : ¬p => Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  λ h : ¬q → ¬p =>
  λ hp : p =>
  (em q).elim
    (λ hq : q => hq)
    (λ hnq : ¬q => absurd hp (h hnq))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  λ h : (p → q) → p =>
  (em p).elim
    (λ hp : p => hp)
    (λ hnp : ¬p => h (λ hp : p => absurd hp hnp))
