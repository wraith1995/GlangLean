import GLang.Proofs.Value.Presentation.PaperValueTypedQueries

open GLang GLang.PaperValueDomains

-- Every actual query annotation carries original validity, including
-- dimensions introduced in canonical FSV output, with no simple-space filter.
example {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (h : ValHasType ε e τ) (hp : ArrayPrimitive e) (hc : ValCtxValid ε)
    (Γ : List ValTy) :
    ∀ s ∈ primitiveQuerySpaces Γ e, Nonempty (ValSValid ε s) :=
  original_primitive_query_valid h hp hc Γ

#print axioms original_primitive_operand_typed
#print axioms original_primitive_query_valid
