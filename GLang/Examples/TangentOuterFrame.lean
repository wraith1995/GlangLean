import GLang.Examples.TangentMovingFrame

namespace GLang

/-- Opening a dimension annotation leaves its finite assembly bound unchanged. -/
@[simp] theorem ValSpace.dofUB_openRec (x : Nat) (u : ValExpr) :
    ∀ s : ValSpace, ValSpace.dofUB (ValSpace.openRec x u s) = ValSpace.dofUB s
  | .empty => rfl
  | .real => rfl
  | .dsum s₀ s₁ => by
      simp only [ValSpace.openRec, ValSpace.dofUB, ValSpace.dofUB_openRec x u s₀,
        ValSpace.dofUB_openRec x u s₁]
  | .tprod s₀ s₁ => by
      simp only [ValSpace.openRec, ValSpace.dofUB, ValSpace.dofUB_openRec x u s₀,
        ValSpace.dofUB_openRec x u s₁]
  | .ffs .kernel (.tprod s₀ s₁) e => by
      simp only [ValSpace.openRec, ValSpace.dofUB, ValSpace.dofUB_openRec x u s₀]
  | .ffs .cokernel (.tprod s₀ s₁) e => by
      simp only [ValSpace.openRec, ValSpace.dofUB, ValSpace.dofUB_openRec x u s₀]
  | .ffs .image (.tprod s₀ s₁) e => by
      simp only [ValSpace.openRec, ValSpace.dofUB, ValSpace.dofUB_openRec x u s₁]
  | .ffs .coimage (.tprod s₀ s₁) e => by
      simp only [ValSpace.openRec, ValSpace.dofUB, ValSpace.dofUB_openRec x u s₁]
  | .ffs p .empty e => by cases p <;> rfl
  | .ffs p .real e => by cases p <;> rfl
  | .ffs p (.dsum s₀ s₁) e => by
      cases p <;>
        simp only [ValSpace.openRec, ValSpace.dofUB, ValSpace.dofUB_openRec x u s₀,
          ValSpace.dofUB_openRec x u s₁]
  | .ffs p (.ffs q s e₀) e => by
      cases p <;> simp only [ValSpace.openRec, ValSpace.dofUB] <;>
        exact ValSpace.dofUB_openRec x u (.ffs q s e₀)

namespace Examples.TangentCoordinates

/-- Assembly commutes with opening, including the dimension-indexed finite list. -/
theorem functionalColumns_openRec (k : Nat) (u : ValExpr) (sv : ValSpace)
    (f : Nat → ValExpr) :
    ValExpr.openRec k u (functionalColumns sv (fun i => f i.val)) =
      functionalColumns (ValSpace.openRec k u sv) (fun i => ValExpr.openRec k u (f i.val)) := by
  unfold functionalColumns
  simp only [ValExpr.openRec_sumAt, List.map_ofFn, Function.comp_def,
    ValExpr.openRec, ValTy.openRec, ValSpace.openRec]
  congr 1
  rw [List.ofFn_congr (ValSpace.dofUB_openRec k u sv).symm]
  rfl

/-- Tensor-valued assembly commutes with opening. -/
theorem tensorColumns_openRec (k : Nat) (u : ValExpr) (dom cod : ValSpace)
    (f : Nat → ValExpr) :
    ValExpr.openRec k u (tensorColumns dom cod (fun i => f i.val)) =
      tensorColumns (ValSpace.openRec k u dom) (ValSpace.openRec k u cod)
        (fun i => ValExpr.openRec k u (f i.val)) := by
  unfold tensorColumns
  simp only [ValExpr.openRec_sumAt, List.map_ofFn, Function.comp_def,
    ValExpr.openRec, ValTy.openRec, ValSpace.openRec]
  congr 1
  rw [List.ofFn_congr (ValSpace.dofUB_openRec k u dom).symm]
  rfl

/-- Opening the point in the whole emitted dual tensor opens only its dimensions. -/
theorem dualEvalCode_openRec (k : Nat) (u : ValExpr) (sv : ValSpace) :
    ValExpr.openRec k u (dualEvalCode sv) = dualEvalCode (ValSpace.openRec k u sv) := by
  unfold dualEvalCode
  rw [tensorColumns_openRec k u sv sv (fun i => functionalColumns sv
    (fun j => pairingCode sv (.delta i sv) (.delta j.val sv)))]
  apply congrArg (tensorColumns (ValSpace.openRec k u sv) (ValSpace.openRec k u sv))
  funext i
  rw [functionalColumns_openRec k u sv
    (fun j => pairingCode sv (.delta i.val sv) (.delta j sv))]
  rfl

def movingDualFrame : Basis :=
  .frame pointBasis (dualEvalBasis (tangentBasis (.appN (.var "f") (.bvar 0))))

def parameterCall (arg : ValExpr) : ValExpr :=
  .reshap (.appV (.var "f" (.piTy (.space pointSV) (.space parameterSV)))
    (.reshap arg (.space pointSV) (.space pointSV)))
    (.space parameterSV) (.space parameterSV)

/-- Complete emitted nonlinear function, including all binder/result reshapes. -/
def movingDualCode : ValExpr :=
  let s := tangentSV (parameterCall (.bvar 0))
  let out := ValTy.space (.tprod s s)
  .vlam (.space pointSV) out (.reshap (dualEvalCode s) out out)

private theorem parameterCall_open (y : Name) :
    ValExpr.openVar y (.space pointSV) (parameterCall (.bvar 0)) =
      parameterCall (.var y (.space pointSV)) := rfl

private theorem movingDualBasis_open (y : Name) :
    Basis.openVar y (dualEvalBasis (tangentBasis (.appN (.var "f") (.bvar 0)))) =
      dualEvalBasis (tangentBasis (.appN (.var "f") (.var y))) := rfl

theorem movingDualFrame_op {Γ : NLCtx} {Ψ : EvalCtx}
    (hΓ : Γ.lookup "f" = some Examples.Paper.fTy)
    (hf : Ψ.lookup ("f", .frame pointBasis parameterBasis) =
      some (.var "f" (.piTy (.space pointSV) (.space parameterSV)))) :
    ValExpr.OpStep Ψ Examples.Paper.ev movingDualFrame movingDualCode := by
  unfold Examples.Paper.ev movingDualFrame movingDualCode
  refine ValExpr.OpStep.nllam rfl rfl (.space (.dsum .real .real))
    (Ψ.avoid ∪ {"f"}) (fun y hy => ?_) (fun y hy => ?_)
  · have hyavoid : y ∉ Ψ.avoid := fun h => hy (Finset.mem_union_left _ h)
    have hyf : y ≠ "f" := fun h => hy (Finset.mem_union_right _ (by simp [h]))
    let Ψy := Ψ.extend y pointBasis (.var y (.space pointSV))
    have hfun : ValExpr.OpStep Ψy (.var "f") (.frame pointBasis parameterBasis)
        (.var "f" (.piTy (.space pointSV) (.space parameterSV))) :=
      opStep_wk (.var hf) ((EvalCtx.avoid_spec hyavoid).1 pointBasis)
    have hcall : ValExpr.OpStep Ψy (.appN (.var "f") (.var y)) parameterBasis
        (parameterCall (.var y (.space pointSV))) := by
      exact .appN_val hfun (.var (Finmap.lookup_insert _))
        (.space (.tprod (.dual (.dsum .real .real)) (.dsum (.dsum .real .real) .real)))
    have hsource : HasType ∅ (Finmap.insert y (.space Examples.Paper.R2) Γ)
        (.appN (.var "f") (.var y))
        (.space (.tprod (.dual Examples.Paper.R2) Examples.Paper.R3)) :=
      Examples.Paper.castTy
        (.app_nonlinear (.var_nlin (by rw [Finmap.lookup_insert_of_ne _ (Ne.symm hyf)]; exact hΓ))
          (.var_nlin (Finmap.lookup_insert _)))
        (Examples.Paper.fTy_cod_instantiate (.var y))
    rw [Examples.Paper.evOuter_openVar, movingDualBasis_open]
    simpa only [ValExpr.openVar, dualEvalCode_openRec, tangentSV, ValSpace.openRec,
      ValExpr.openRec, ValTy.openRec, parameterCall, pointSV, parameterSV, ambientSV,
      ↓reduceIte] using tangentDualEval_op hsource hcall
  · have hyavoid : y ∉ Ψ.avoid := fun h => hy (Finset.mem_union_left _ h)
    let Ψy := Ψ.extend y pointBasis (.var y (.space pointSV))
    have hfun : ValExpr.OpStep Ψy (.var "f") (.frame pointBasis parameterBasis)
        (.var "f" (.piTy (.space pointSV) (.space parameterSV))) :=
      opStep_wk (.var hf) ((EvalCtx.avoid_spec hyavoid).1 pointBasis)
    have hcall : ValExpr.OpStep Ψy (.appN (.var "f") (.var y)) parameterBasis
        (parameterCall (.var y (.space pointSV))) := by
      exact .appN_val hfun (.var (Finmap.lookup_insert _))
        (.space (.tprod (.dual (.dsum .real .real)) (.dsum (.dsum .real .real) .real)))
    have hs := tangentSpace_eval hcall
    exact .space (.tprod (.dual (.dual hs)) (.dual hs))

/-- The actual moving frame is source-valid for the same parameterization
context that types `Examples.Paper.ev`. -/
theorem movingDualFrame_valid {Γ : NLCtx}
    (hΓ : Γ.lookup "f" = some Examples.Paper.fTy) :
    Basis.BasisValid Γ movingDualFrame := by
  refine .frame {"f"} (.dsum .one .one rfl rfl) (fun y hy => ?_)
  simp only [Finset.mem_singleton] at hy
  rw [movingDualBasis_open]
  apply dualEvalBasis_valid _ rfl
  apply tangentBasis_valid
  exact Examples.Paper.castTy
    (.app_nonlinear (.var_nlin (by rw [Finmap.lookup_insert_of_ne _ (Ne.symm hy)]; exact hΓ))
      (.var_nlin (Finmap.lookup_insert _)))
    (Examples.Paper.fTy_cod_instantiate (.var y))

end Examples.TangentCoordinates
end GLang
