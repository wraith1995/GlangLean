import GLang.Proofs.Value.Presentation.PaperValueOriginalLambda

open GLang GLang.PaperValueDomains

-- Original cofinite body evidence suffices even when the result type has
-- arbitrary dependent FFS annotations and arbitrary arrow nesting.
example (ε : ValCtx) (c : ValTy) (body : ValExpr) (L : Finset VName)
    (ih : ∀ x, x ∉ L → ∀ ρ ρ',
      ContextRelated directOracle (Finmap.insert x (.space .real) ε) ρ ρ' →
      PartialRel (RuntimeRelated directOracle (ValTy.openVar x (.space .real) c)
        ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
        (denotValB_semS directOracle ρ [] [] (ValExpr.openVar x (.space .real) body))
        (denotValB_semS directOracle ρ' [] [] (ValExpr.openVar x (.space .real) body)))
    (ρ ρ' : ValEnvSem) (hctx : ContextRelated directOracle ε ρ ρ') :
    PartialRel (RuntimeRelated directOracle (.piTy (.space .real) c)
      ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
      (denotValB_semS directOracle ρ [] [] (.vlam (.space .real) c body))
      (denotValB_semS directOracle ρ' [] [] (.vlam (.space .real) c body)) :=
  original_lambda_step ε (.space .real) c body L (.space .real) (.space .real)
    ih ρ ρ' hctx trivial

#print axioms spaceAgreement_openPush
#print axioms typeCoherent_openPush
#print axioms original_lambda_step
#print axioms original_pi_step
