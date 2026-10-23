import GLang.Proofs.Value.Queries.ValueQueryDependencies

/-! Finite query dependencies of explicit value constructors. -/
namespace GLang.ValueQueryDependencies

/-- An explicit reshape uses the operand and its two annotated types. -/
theorem Finite.reshap {Γ : List ValTy} {e : ValExpr} {target source : ValTy}
    (he : Finite (.expr Γ e)) (ht : Finite (.type Γ target))
    (hs : Finite (.type Γ source)) :
    Finite (.expr Γ (.reshap e target source)) := by
  apply Finite.intro
  simpa only [children, exprChildren, ValExpr.inferTypeCtx, ValExpr.inferSpaceCtx,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ht (And.intro ht.spaceOf (And.intro he (And.intro ht hs)))

/-- A matrix shape check preserves finiteness of its operand dependencies. -/
theorem Finite.reshapBase {Γ : List ValTy} {e : ValExpr} {s : ValSpace}
    (he : Finite (.expr Γ e)) (hs : Finite (.space Γ s)) :
    Finite (.expr Γ (.reshapBase e s)) := he.reshap hs.space hs.space

end GLang.ValueQueryDependencies
