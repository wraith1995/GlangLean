import GLang.Proofs.Value.Soundness.ValueSumAtSemantics
import GLang.Proofs.Value.DenotationChecks

namespace GLang

private theorem partial_vsum_nil (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (index : ValSpace) :
    denotValB_partial orc ρ Γ Δ (.vsum index []) =
      match index.dofPartial (orc ρ Γ Δ) with
      | .error err => .error err
      | .ok n => if n = 0 then .ok (.arrayOf 0 fun _ => 0) else .error .mismatch := by
  rw [denotValB_partial]
  simp only [ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, ValTy.spaceOf]
  cases hd : index.dofPartial (orc ρ Γ Δ) with
  | error err =>
    simp [PartialValueEval.withDimensions, PartialValueEval.dimensions, hd,
      bind, Except.bind]
  | ok n =>
    have hn := PartialValueEval.dof_numbers (orc ρ Γ Δ) index n hd
    have hg : PartialValueEval.dimensions (orc ρ Γ Δ) [index, .empty] = .ok () := by
      simp [PartialValueEval.dimensions, hd, ValSpace.dofPartial,
        ValSpace.shpOfPartial, bind, Except.bind, pure, Except.pure]
    rw [PartialValueEval.withDimensions, hg]
    dsimp only
    have hm : (([] : List ValExpr).take
        (ValSpace.dof (PartialValueEval.numbers (orc ρ Γ Δ)) index)).attach.map
        (fun e => denotValB_partial orc ρ Γ Δ e.1) = [] := by simp
    rw [hm]
    by_cases hz : n = 0 <;>
      simp [hn, hz, ValExpr.inferSpaceCtx, ValueShape.family, ValValSem.sequenceArrays]

/-- The corrected compiler sum annotation preserves all partial evaluation
results, including dimension errors and incorrectly sized empty outputs. -/
theorem denotValB_partial_sumAt (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem)
    (index target : ValSpace) (es : List ValExpr) :
    denotValB_partial orc ρ Γ Δ (ValExpr.sumAt index es target) =
      denotValB_partial orc ρ Γ Δ (ValExpr.reshapBase (.vsum index es) target) := by
  cases es with
  | cons head tail => rfl
  | nil =>
    simp only [ValExpr.sumAt, List.isEmpty_nil, ↓reduceIte, ValExpr.reshapBase]
    conv_lhs => rw [denotValB_partial]
    conv_rhs => rw [denotValB_partial]
    simp only [partial_vsum_nil]
    cases hi : index.dofPartial (orc ρ Γ Δ) with
    | error err => rfl
    | ok n =>
      by_cases hz : n = 0
      · cases ht : target.dofPartial (orc ρ Γ Δ) <;>
          simp [hz, PartialValueEval.reshapeInferred, PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray,
            ht, ValSpace.dofPartial, ValSpace.shpOfPartial, bind, Except.bind, pure, Except.pure,
            ValValSem.arrayOf]
      · simp [hz]

end GLang
