import GLang.Value.ExpressionDenotation

/-! Derived SVD selectors and checked-domain membership. -/
namespace GLang

/-- Uniform derived selector equation for the four SVD blocks. -/
theorem denotValB_partial_canonicalFSV (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (which : ValFFSProp) (e a b : ValExpr) :
    denotValB_partial orc ρ Γ Δ (.canonicalFSV which e a b) =
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ a, ValExpr.inferSpaceCtx Γ b, ValExpr.inferSpaceCtx Γ (.canonicalFSV which e a b)] fun q =>
        ValValSem.bindArrays3 (denotValB_partial orc ρ Γ Δ e)
          (denotValB_partial orc ρ Γ Δ a) (denotValB_partial orc ρ Γ Δ b)
          fun ae aa ab =>
            match ValExpr.inferSpaceCtx Γ e with
            | .tprod s0 s1 =>
                let d0 := ValSpace.dof q s0
                let d1 := ValSpace.dof q s1
                match ValueCanonicalFSV.eval which d0 d1 ae aa ab with
                | .error err => .error err
                | .ok r =>
                    if r.rows * r.cols =
                        ValSpace.dof q (ValExpr.inferSpaceCtx Γ (.canonicalFSV which e a b)) then
                      .ok (.array r.flatten)
                    else .error .mismatch
            | _ => .error .mismatch := by
  cases which <;> simp only [ValExpr.canonicalFSV, denotValB_partial] <;> rfl

/-- Every successful checked evaluation belongs to the partially interpreted
type, including all its argument-dependent result fibers. -/
theorem denotValB_partialCheckedAt_sound (orc : PartialFFSOracleSem)
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (τ : ValTy) (e : ValExpr) :
    PartialValType.ResultContains (denotValTyPartial orc ρ Γ Δ τ)
      (denotValB_partialCheckedAt orc ρ Γ Δ τ e) := by
  unfold denotValB_partialCheckedAt
  cases denotValB_partial orc ρ Γ Δ e with
  | error err => exact PartialValType.resultContains_error _ _
  | ok v =>
      simp only []
      cases hv : τ.carrierFromVal v with
      | error err => exact PartialValType.resultContains_error _ _
      | ok a => exact checkValTyPartial_sound orc ρ Γ Δ τ a

end GLang
