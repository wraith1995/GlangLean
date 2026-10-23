import GLang.Proofs.Value.Presentation.PaperValueNamedSubstitution

open GLang GLang.PaperValueDomains
noncomputable section

-- The original dependent FFS codomain observes the actual substituted matrix.
-- No environment well-formedness or oracle-substitution certificate is assumed.
example (ρ : ValEnvSem) (v : ValValSem)
    (he : denotValB_semS directOracle ρ [] []
      (.zero (.tprod .real .real)) = .ok v) :
    RawTypePresentation directOracle
      (.space (.ffs .kernel (.tprod .real .real) (.bvar 0)))
      (ValTy.instantiate (.zero (.tprod .real .real))
        (.space (.ffs .kernel (.tprod .real .real) (.bvar 0))))
      ⟨ρ,[.space (.tprod .real .real)],[v]⟩ ⟨ρ,[],[]⟩ := by
  apply original_type_instantiation (ε := ∅)
    (hu := ValHasType.zero (.tprod .real .real))
    (hc := by intro x τ h; simp at h) (hv := by intro x τ h; simp at h) (he := he)
  exact .piTy ∅ (.space (.tprod .real .real))
    (fun x _ => .space (.ffs .real .real (.var (by simp))))

example (ε : ValCtx) (d c : ValTy) (body u : ValExpr)
    (hf : ValHasType ε (.vlam d c body) (.piTy d c))
    (hu : ValHasType ε u d) (hc : ContextLocallyClosed ε) (hv : ValCtxValid ε)
    (ρ : ValEnvSem) (v : ValValSem) (err : DimError)
    (he : denotValB_semS directOracle ρ [] [] u = .ok v)
    (hb : denotValB_semS directOracle ρ [d] [v] body = .error err) :
    denotValB_semS directOracle ρ [] [] (ValExpr.instantiate u body) = .error err := by
  rw [← original_typed_beta_evaluation hf hu hc hv ρ v he]
  exact hb

open Lean Elab Command
elab "check_named_substitution_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``GLang.Matrix.exists_gsvd]
  for n in [``original_numeric_substitution_result, ``namedSpaceSubstitution,
      ``namedTypeSubstitution, ``namedExprSubstitution,
      ``original_type_instantiation, ``original_typed_beta_evaluation] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected original typed substitution axiom in {n}: {ax}"
  logInfo "Original typed semantic substitution: foundations and existing GSVD only."
check_named_substitution_axioms
