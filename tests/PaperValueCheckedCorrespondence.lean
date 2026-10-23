import GLang.Proofs.Value.Presentation.PaperValueCheckedCorrespondence

open GLang GLang.PaperValueDomains

-- The actual inferred-type checked evaluator, at arbitrary dependent type.
example {ε : ValCtx} {e : ValExpr} {τ : ValTy} (he : ValHasType ε e τ)
    (ρ : ValEnvSem)
    (h : PartialRel (RuntimeRelated directOracle τ ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩)
      (denotValB_semS directOracle ρ [] [] e) (denotValB_semS directOracle ρ [] [] e)) :
    PartialRel (RuntimeRelated directOracle τ ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩)
      (denotValB_semSChecked directOracle ρ [] [] e)
      (denotValB_semSChecked directOracle ρ [] [] e) :=
  denot_checked_related he he directOracle _ _ h

#print axioms runtime_normalize_checked_right
#print axioms recheck_related_right
#print axioms recheck_related
#print axioms denot_checked_related
#print axioms denot_checked_related_right
