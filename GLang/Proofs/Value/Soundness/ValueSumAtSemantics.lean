import GLang.Proofs.Value.Typing.ValueSumAt
import GLang.Value.Supporting.TotalDimensionSemantics

namespace GLang

private theorem denot_vsum_nil (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (index : ValSpace) :
    denotValB_semS orc ρ Γ Δ (.vsum index []) =
      if ValSpace.dof (orc ρ Γ Δ) index = 0 then
        .ok (.arrayOf 0 fun _ => 0) else .error .mismatch := by
  rw [denotValB_semS]
  dsimp only
  have hm : (([] : List ValExpr).take (ValSpace.dof (orc ρ Γ Δ) index)).attach.map
      (fun e => denotValB_semS orc ρ Γ Δ e.1) = [] := by simp
  rw [hm]
  by_cases hi : ValSpace.dof (orc ρ Γ Δ) index = 0 <;>
    simp [hi, ValExpr.inferSpaceCtx, ValueShape.family, ValValSem.sequenceArrays]

theorem denotValB_semS_sumAt (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem)
    (index target : ValSpace) (es : List ValExpr) :
    denotValB_semS orc ρ Γ Δ (ValExpr.sumAt index es target) =
      denotValB_semS orc ρ Γ Δ (ValExpr.reshapBase (.vsum index es) target) := by
  cases es with
  | cons head tail => rfl
  | nil =>
    simp only [ValExpr.sumAt, List.isEmpty_nil, ↓reduceIte, ValExpr.reshapBase]
    conv_lhs => rw [denotValB_semS]
    conv_rhs => rw [denotValB_semS]
    simp only [denot_vsum_nil]
    by_cases hi : ValSpace.dof (orc ρ Γ Δ) index = 0 <;>
      simp [hi, reshapDenotSemS, reshapArrayBetweenS, ValValSem.arrayOf]

end GLang
