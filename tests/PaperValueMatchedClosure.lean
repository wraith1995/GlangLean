import GLang.Proofs.Value.Presentation.PaperValueMatchedClosure

open GLang GLang.PaperValueDomains

-- Original judgments and original context validity suffice. No explicit
-- declaration-closure, annotation-agreement, or dependency-order premise.
example {ε : ValCtx} (hc : ValCtxValid ε) {τ : ValTy} {k : ValKind}
    (ht : ValTValid ε τ k) : ValTy.lc τ := validType_lc hc ht
example {ε : ValCtx} (hc : ValCtxValid ε) {e : ValExpr} {τ : ValTy}
    (ht : ValHasType ε e τ) : ValExpr.lc e := (validExpr_lc hc ht).1
example {ε : ValCtx} (hc : ValCtxValid ε) {x : VName} {τ : ValTy}
    (hx : ε.lookup x = some τ) : ValTy.lc τ := validContext_lc hc x τ hx

#print axioms matchedType_lc
#print axioms validType_lc
#print axioms validContext_lc
#print axioms validSpace_lc
#print axioms validExpr_lc
