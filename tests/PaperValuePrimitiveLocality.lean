import GLang.Proofs.Value.Presentation.PaperValuePrimitiveLocality

open GLang GLang.PaperValueDomains

-- No equality of either environments or oracle callbacks is required for
-- addition at a fixed real space once its immediate operands agree.
example (orc : FFSOracleSem) (w w' : World) (a b : ValExpr)
    (hg : w.types = w'.types)
    (ha : denotValB_semS orc w.env w.types w.values a =
      denotValB_semS orc w'.env w'.types w'.values a)
    (hb : denotValB_semS orc w.env w.types w.values b =
      denotValB_semS orc w'.env w'.types w'.values b) :
    denotValB_semS orc w.env w.types w.values (.vadd .real a b) =
      denotValB_semS orc w'.env w'.types w'.values (.vadd .real a b) := by
  apply arrayPrimitive_eval_congr_local orc _ w w' (by trivial) hg
  · intro s hs
    simp [primitiveQuerySpaces, primitiveInputSpaces,
      ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx] at hs
    subst s
    trivial
  · intro e he
    simp [primitiveOperands] at he
    rcases he with rfl | rfl
    · exact ha
    · exact hb

#print axioms arrayPrimitive_eval_congr_local
