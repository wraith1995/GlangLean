import GLang.Proofs.Value.Binding.ValueSubstitution
import GLang.Proofs.Value.Typing.ValueInfer

/-! Inference obligations for semantic named substitution follow from the
original syntactic substitution theorem, including dependent annotations. -/
namespace GLang

theorem ValHasType.inferType_subst {x : VName} {u : ValExpr} {ε : ValCtx}
    {τx : ValTy} {e : ValExpr} {τ : ValTy}
    (sd : ValSubstData x u ε τx) (h : ValHasType ε e τ)
    (Γ Γ' : List ValTy) :
    ValExpr.inferTypeCtx Γ' (ValExpr.subst x u e) =
      ValTy.subst x u (ValExpr.inferTypeCtx Γ e) := by
  rw [ValExpr.inferTypeCtx_eq_of_typed h,
    ValExpr.inferTypeCtx_eq_of_typed (h.subst sd)]

theorem ValHasType.inferSpace_subst {x : VName} {u : ValExpr} {ε : ValCtx}
    {τx : ValTy} {e : ValExpr} {s : ValSpace}
    (sd : ValSubstData x u ε τx) (h : ValHasType ε e (.space s))
    (Γ Γ' : List ValTy) :
    ValExpr.inferSpaceCtx Γ' (ValExpr.subst x u e) =
      ValSpace.subst x u (ValExpr.inferSpaceCtx Γ e) := by
  rw [ValExpr.inferSpaceCtx_eq_of_typed h]
  have hs : ValHasType (ValCtx.substMap x u (ε.erase x))
      (ValExpr.subst x u e) (.space (ValSpace.subst x u s)) := by
    simpa only [ValTy.subst] using h.subst sd
  exact ValExpr.inferSpaceCtx_eq_of_typed hs

end GLang
