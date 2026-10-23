import GLang.Elaboration.Uniqueness

open GLang

example (s₀ s₁ s₂ : Space) (f x : Term) :
    (Term.appL s₀ s₁ f x).erase = (Term.appI s₂ f x).erase ∧
    (Term.appI s₂ f x).erase = (Term.appN f x).erase := ⟨rfl, rfl⟩

example (s₀ s₁ s₂ : Space) (e : Term) :
    (Term.pinvT s₀ s₁ e).erase = (Term.pinvD s₂ e).erase := rfl

example (s a b : Space) (e : Term) :
    (Term.llam s a e).erase = (Term.llam s b e).erase := rfl

example : (Term.zero .empty).erase ≠ (Term.zero .real).erase := by
  simp [Term.erase, Space.erase]

example (e : Term) :
    (Term.llam .empty .real e).erase ≠ (Term.llam .real .real e).erase := by
  simp [Term.erase, Space.erase]

-- Erasure also removes hidden parameters inside an explicitly retained space.
example (a b c d : Space) (e : Term) :
    (Term.zero (.ker a b e)).erase = (Term.zero (.ker c d e)).erase := rfl

-- Equal application erasures cannot conceal two well-typed application variants.
example {Δ ε a b c f x τ₁ τ₂} (hwf : InductiveCtxWF Δ ε)
    (h₁ : HasType Δ ε (.appL a b f x) τ₁)
    (h₂ : HasType Δ ε (.appI c f x) τ₂) : False := by
  have he := (HasType.annotation_unique hwf h₁ h₂ rfl).1
  cases he

example {Δ ε a b c e τ₁ τ₂} (hwf : InductiveCtxWF Δ ε)
    (h₁ : HasType Δ ε (.pinvT a b e) τ₁)
    (h₂ : HasType Δ ε (.pinvD c e) τ₂) : False := by
  have he := (HasType.annotation_unique hwf h₁ h₂ rfl).1
  cases he

-- Formation recovers both hidden parameters of a fundamental subspace.
example {ε a b c d e} (h₁ : SValid ε (.ker a b e))
    (h₂ : SValid ε (.ker c d e)) : a = c ∧ b = d := by
  have he := SValid.annotation_unique h₁ h₂ rfl
  cases he
  exact ⟨rfl, rfl⟩

#print axioms SValid.erase_unique
#print axioms TValid.erase_unique
#print axioms SubType.erase_unique
#print axioms HasType.erase_unique
#print axioms HasType.annotation_unique
#print axioms HasType.denot_eq_of_erase_eq
