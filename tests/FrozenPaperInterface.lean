import GLang.Paper

open GLang

example (hc : Operational.ContextHistory Δ ε Γv Ψ)
    (ht : TValid ε T k) (he : Operational.Unchecked.EvalT Ψ T Tv) :
    ∃ kv, Nonempty (RuntimeValue.ValTValid Γv Tv kv) ∧
      ValTy.fv Tv ⊆ Ψ.keyNames :=
  (PaperOperationalResults.preservation hc).1 ht he

example (hc : Operational.ContextHistory Δ ε Γv Ψ)
    (ht : HasType Δ ε t (Basis.tof b)) (hb : Basis.BasisValid ε b)
    (he : Operational.Unchecked.OpStep Ψ t b v) :
    Nonempty (RuntimeValue.ValHasType Γv v (ValExpr.inferType v)) ∧
      (∃ kv, Nonempty (RuntimeValue.ValTValid Γv (ValExpr.inferType v) kv)) ∧
      ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ Ψ.keyNames :=
  (PaperOperationalResults.preservation hc).2.1 ht hb he

-- Conversion preservation retains both independent realizations. It does not
-- impose equality of value spaces to obtain the matrix-typing conclusion.
example (hc : Operational.ContextHistory Δ ε Γv Ψ)
    (hb : Basis.BasisValid ε b₀)
    (he : Operational.Unchecked.EvalBB Ψ b₀ v b₁) :
    ∃ s₀ s₁ sv₀ sv₁,
      Nonempty (RuntimeValue.ValHasType Γv v (.space (.tprod sv₀ sv₁))) ∧
      ValExpr.inferType v = .space (.tprod sv₀ sv₁) ∧
      Operational.Unchecked.EvalS Ψ s₀ sv₀ ∧
      Operational.Unchecked.EvalS Ψ s₁ sv₁ ∧
      ValExpr.fv v ⊆ Ψ.keyNames :=
  (PaperOperationalResults.preservation hc).2.2 hb he

-- Requested bases are arbitrary valid bases of the same source space.
example (hc : Operational.ContextHistory Δ ε Γv Ψ)
    (h₀ : Basis.BasisValid ε b₀) (h₁ : Basis.BasisValid ε b₁)
    (ht₀ : Basis.tof b₀ = .space s) (ht₁ : Basis.tof b₁ = .space s) :
    ∃ v, Operational.Cob ε Ψ b₀ v b₁ :=
  (PaperOperationalResults.progress hc).2.2 h₀ h₁ ht₀ ht₁

-- Progress still returns exact inference at arbitrary dependent result types.
example (hc : Operational.ContextHistory Δ ε Γv Ψ)
    (ht : HasType Δ ε t (Basis.tof b)) (hb : Basis.BasisValid ε b) :
    ∃ v Tv, Operational.Term Δ ε Ψ t b v Tv ∧ ValExpr.inferType v = Tv :=
  (PaperOperationalResults.progress hc).2.1 ht hb

example (hρ : RuntimeValue.PartialEnvWF PartialDirectOracle.oracle Γv ρ)
    (ht : RuntimeValue.ValHasType Γv v Tv) :
    ValExpr.inferType v = Tv :=
  (PaperValueResults.valueSoundness ρ hρ ht).2.1

-- Type agreement supplies the semantic basis/frame, not only its dimensions.
example (hc : Adequacy.PartialDirect.Consistent Δ ε Ψ Γv σ ρ)
    (he : Operational.TyAt ε Ψ b Tv) :
    Adequacy.Direct.BasisAt σ [] (Basis.tof b) (denotBasis σ b) :=
  (PaperAdequacyResults.typeAdequacy hc he).2

-- The term result includes success and full type agreement at that same trace.
example (hc : Adequacy.PartialDirect.Consistent Δ ε Ψ Γv σ ρ)
    (he : Operational.Term Δ ε Ψ t b v Tv) :
    ∃ w, denotValB_partial PartialDirectOracle.oracle ρ [] [] v = .ok w ∧
      PartialAdequacy.Agree PartialDirectOracle.oracle σ ρ [] [] []
        (Basis.tof b) Tv (denotBasis σ b) (denotTerm σ t) w ∧
      PaperAdequacyResults.TypeAgreement σ ρ (Basis.tof b) Tv (denotBasis σ b) :=
  PaperAdequacyResults.termAdequacy hc he

open Lean Elab Command in
elab "check_frozen_paper_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``PaperValueResults.valueSoundness,
      ``PaperOperationalResults.preservation, ``PaperOperationalResults.progress,
      ``PaperAdequacyResults.typeAdequacy, ``PaperAdequacyResults.termAdequacy,
      ``PaperAdequacyResults.cobAdequacy, ``PaperAdequacyResults.progressAndAdequacy] do
    for ax in ← Lean.collectAxioms decl do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo "Frozen-paper soundness, preservation, progress, and adequacy: foundations only."

check_frozen_paper_axioms
