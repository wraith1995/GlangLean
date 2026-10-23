import GLang.Proofs.Value.Presentation.PaperValueLocalClosure

open GLang GLang.PaperValueDomains

-- Empty original contexts require no additional local-closure premise.
example {s : ValSpace} (h : ValSValid ∅ s) : ValSpace.lc s :=
  originalSpace_lc h (by intro x t hx; simpa using hx)
example {τ : ValTy} {k : ValKind} (h : ValTValid ∅ τ k) : ValTy.lc τ :=
  originalType_lc h (by intro x t hx; simpa using hx)
example {e : ValExpr} {τ : ValTy} (h : ValHasType ∅ e τ) : ValExpr.lc e ∧ ValTy.lc τ :=
  originalExpr_lc h (by intro x t hx; simpa using hx)

#print axioms originalSpace_lc
#print axioms originalType_lc
#print axioms originalExpr_lc
