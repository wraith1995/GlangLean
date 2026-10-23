import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectAssembly
import GLang.Proofs.Value.Runtime.RuntimeValueEmbedding
import Lean

open GLang
namespace GLang.PartialDirectTests
noncomputable section
set_option maxRecDepth 4096

private def matrixSpace : ValSpace := .tprod .real .real
private def badMatrix : ValExpr := .mtm 1 1 .empty .real
  (.zero matrixSpace) (.zero matrixSpace)
private def badSpace : ValSpace := .ffs .kernel matrixSpace badMatrix

-- The failing witness is originally typed, so this is not just a malformed
-- untyped input test.
def badMatrix_typed : ValHasType ∅ badMatrix (.space matrixSpace) :=
  .mtm .empty .real (.zero (.tprod .real .real)) (.zero (.tprod .real .real))

theorem badMatrix_error (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) :
    denotValB_partial orc ρ Γ Δ badMatrix = .error .mismatch := by
  simp [badMatrix, matrixSpace, denotValB_partial, PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred, PartialValueEval.withDimensions,
    PartialValueEval.dimensions, ValSpace.dofPartial, ValSpace.shpOfPartial,
    bind, pure, Except.bind, Except.pure, ValValSem.bindArrays, ValValSem.bindArray,
    ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, ValExpr.inferSpaceCtx,
    ValValSem.arrayOf]

theorem bad_query (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (p : ValFFSProp) :
    PartialDirectOracle.oracle ρ Γ Δ p matrixSpace badMatrix = .error .mismatch := by
  unfold PartialDirectOracle.oracle
  rw [PartialDirectOracle.query_eq]
  simp [PartialDirectOracle.step, badMatrix_error, matrixSpace,
    ValSpace.shpOfPartial, ValSpace.dofPartial,
    bind, pure, Except.bind, Except.pure]

theorem failed_dim (ρ : ValEnvSem) :
    Adequacy.Partial.dimOf ρ [] [] badSpace = .error .mismatch := by
  simp [Adequacy.Partial.dimOf, badSpace, ValSpace.dofPartial,
    ValSpace.shpOfPartial, bad_query, bind, Except.bind]

theorem failed_zero (ρ : ValEnvSem) :
    Adequacy.Partial.evalVal ρ [] [] (.zero badSpace) = .error .mismatch := by
  simp [Adequacy.Partial.evalVal, denotValB_partial, PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred, ValExpr.inferSpaceCtx,
    PartialValueEval.withDimensions, PartialValueEval.dimensions, badSpace,
    ValSpace.dofPartial, ValSpace.shpOfPartial, bad_query, bind, Except.bind]

-- A zero-dimensional factor cannot erase the other factor's failure.
example (ρ : ValEnvSem) :
    Adequacy.Partial.dimOf ρ [] [] (.tprod .empty badSpace) = .error .mismatch := by
  simp [Adequacy.Partial.dimOf, badSpace, ValSpace.dofPartial, ValSpace.shpOfPartial,
    bad_query, bind, pure, Except.bind, Except.pure]

-- Lambda creation suspends its failing body. Applying it exposes the error.
private def delayed : ValExpr := .vlam (.space .real) (.space badSpace) (.zero badSpace)

example (ρ : ValEnvSem) :
    ∃ T f, Adequacy.Partial.evalVal ρ [] [] delayed = .ok (.fn T f) := by
  simp [Adequacy.Partial.evalVal, delayed, denotValB_partial, PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred, denotValTyPartial,
    ValSpace.dofPartial, ValSpace.shpOfPartial]

example (ρ : ValEnvSem) :
    Adequacy.Partial.evalVal ρ [] [] (.appV delayed (.rlit 1)) =
      .error .mismatch := by
  simp [Adequacy.Partial.evalVal, delayed, denotValB_partial, PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred, denotValTyPartial,
    PartialValueEval.withDimensions, PartialValueEval.dimensions,
    PartialValueEval.decodeDomain, PartialValueEval.checkResult, checkValTyPartial,
    PartialValType.check, ValExpr.inferTypeCtx, ValTy.domain,
    ValTy.carrierFromVal, ValTy.carrierToVal, ValValSem.applyTyped,
    ValSpace.dofPartial, ValSpace.shpOfPartial, ValExpr.inferSpaceCtx,
    ValValSem.arrayOf, badSpace, bad_query, bind, pure, Except.bind, Except.pure, PartialValType.space]

-- A nested query hidden in the witness must also fail. The outer parent is
-- a perfectly ordinary 1-by-1 shape, so an outer-only wrapper would miss it.
private def nestedWitness : ValExpr :=
  .reshap (.zero badSpace) (.space matrixSpace) (.space badSpace)

theorem nested_query (ρ : ValEnvSem) :
    PartialDirectOracle.oracle ρ [] [] .kernel matrixSpace nestedWitness =
      .error .mismatch := by
  have hs : RuntimeValue.ValSValid ∅ badSpace :=
    .ffs .real .real badMatrix_typed.runtime
  have ht : RuntimeValue.ValHasType ∅ nestedWitness (.space matrixSpace) :=
    .reshap (.zero hs) (.space hs) (.space (.tprod .real .real))
  have hf := (RuntimeValue.validExpr_queryFinite
    (show RuntimeValue.ValCtxValid ∅ from by intro x t h; simp at h) ht).1
  apply PartialDirectLocality.oracle_operand_error _ _ _ _ _ _ _ (.ffs (.tprod .real .real) hf)
  simp [nestedWitness, denotValB_partial, PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred, PartialValueEval.withDimensions,
    PartialValueEval.dimensions, ValExpr.inferSpaceCtx, badSpace,
    ValSpace.dofPartial, ValSpace.shpOfPartial, bad_query,
    bind, pure, Except.bind, Except.pure]

theorem zero_matrix_kernel (ρ : ValEnvSem) :
    PartialDirectOracle.oracle ρ [] [] .kernel matrixSpace (.zero matrixSpace) = .ok 1 := by
  have hz : denotAsMatrix 1 1 (FlatArray.ofFn 1 (fun _ => 0)).get = 0 := by
    ext i j
    simp [denotAsMatrix, FlatArray.get, FlatArray.ofFn]
  have hf : ValueQueryDependencies.Finite (.space [] (.ffs .kernel matrixSpace (.zero matrixSpace))) :=
    .ffs (.tprod .real .real) (RuntimeValue.validExpr_queryFinite
      (show RuntimeValue.ValCtxValid ∅ from by intro x t h; simp at h)
      (RuntimeValue.ValHasType.zero (.tprod .real .real))).1
  rw [PartialDirectLocality.oracle_eq _ _ _ _ _ _ hf]
  simp [matrixSpace, denotValB_partial, PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred,
    PartialValueEval.withDimensions, PartialValueEval.dimensions,
    ValExpr.inferSpaceCtx, ValSpace.dofPartial, ValSpace.shpOfPartial,
    ValValSem.arrayOf, ffsDimensionPartial, ffsOperandRankPartial,
    bind, pure, Except.bind, Except.pure, hz, ffsDim]

-- A binder-local matrix witness reads the actual pushed argument.
theorem bound_zero_kernel (ρ : ValEnvSem) :
    PartialDirectOracle.oracle ρ [.space matrixSpace]
      [.array (FlatArray.ofFn 1 (fun _ => 0))] .kernel matrixSpace (.bvar 0) = .ok 1 := by
  have hz : denotAsMatrix 1 1 (FlatArray.ofFn 1 (fun _ => 0)).get = 0 := by
    ext i j
    simp [denotAsMatrix, FlatArray.get, FlatArray.ofFn]
  have hf : ValueQueryDependencies.Finite (.space [.space matrixSpace]
      (.ffs .kernel matrixSpace (.bvar 0))) := by
    apply ValueQueryDependencies.Finite.ffs (.tprod .real .real)
    apply ValueQueryDependencies.Finite.intro
    simpa [ValueQueryDependencies.children, ValueQueryDependencies.exprChildren,
      ValExpr.inferTypeCtx, ValExpr.inferSpaceCtx, ValTy.spaceOf] using
      And.intro (ValueQueryDependencies.Finite.tprod
        (Γ := [.space matrixSpace]) .real .real).space
        (ValueQueryDependencies.Finite.tprod (Γ := [.space matrixSpace]) .real .real)
  rw [PartialDirectLocality.oracle_eq _ _ _ _ _ _ hf]
  simp [matrixSpace, denotValB_partial, PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred,
    ValSpace.dofPartial, ValSpace.shpOfPartial, StrictValueAccess.lookup,
    ffsDimensionPartial, ffsOperandRankPartial,
    bind, pure, Except.bind, Except.pure, hz, ffsDim]

-- The constructed binder bridge transports a dependent matrix witness from
-- the pushed argument to a fresh named variable, without a caller oracle law.
theorem named_zero_kernel (ρ : ValEnvSem) :
    PartialDirectOracle.oracle
      (ρ.update "matrix" (.array (FlatArray.ofFn 1 (fun _ => 0)))) [] []
      .kernel matrixSpace (.var "matrix" (.space matrixSpace)) = .ok 1 := by
  have bridge := PartialDirectOpenPush.oracle_openPush
    (rho := ρ) (y := "matrix") (sigmaV := .space matrixSpace)
    (w := .array (FlatArray.ofFn 1 (fun _ => 0))) (G := []) (D := [])
    (p := .kernel) (s := matrixSpace) (e := .bvar 0)
    rfl (.space (.tprod .real .real))
    (by simp [matrixSpace, ValTy.fv, ValSpace.fv]) (by simp [ValTyCtxFresh])
    (by simp [matrixSpace, ValSpace.fv]) (by simp [ValExpr.fv])
  simpa [matrixSpace, ValTy.closePrefix, ValSpace.openRec, ValExpr.openRec]
    using bridge.trans (bound_zero_kernel ρ)

-- A delayed body which uses the bound argument preserves the complete result
-- across the same bridge, even when the supplied matrix has malformed storage.
theorem malformed_named_zero (ρ : ValEnvSem) :
    Adequacy.Partial.evalVal (ρ.update "matrix" (.array FlatArray.empty)) [] []
      (.zero (.ffs .kernel matrixSpace (.var "matrix" (.space matrixSpace)))) =
    Adequacy.Partial.evalVal ρ [.space matrixSpace] [.array FlatArray.empty]
      (.zero (.ffs .kernel matrixSpace (.bvar 0))) := by
  have bridge := PartialDirectOpenPush.eval_openPush ρ "matrix" (.space matrixSpace)
    (.array FlatArray.empty) [] [] (.zero (.ffs .kernel matrixSpace (.bvar 0)))
    rfl (.space (.tprod .real .real))
    (by simp [matrixSpace, ValTy.fv, ValSpace.fv]) (by simp [ValTyCtxFresh])
    (by simp [matrixSpace, ValExpr.fv, ValSpace.fv])
  simpa [matrixSpace, ValTy.closePrefix, ValSpace.openRec, ValExpr.openRec] using bridge

example (ρ : ValEnvSem) :
    Adequacy.Partial.evalValCheckedAt ρ [] [] (.space badSpace) (.rlit 1) =
      .error .mismatch := by
  simp [Adequacy.Partial.evalValCheckedAt, denotValB_partialCheckedAt,
    denotValB_partial, PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred, PartialValueEval.withDimensions, PartialValueEval.dimensions,
    ValExpr.inferSpaceCtx, ValSpace.dofPartial, ValSpace.shpOfPartial,
    ValValSem.arrayOf, ValTy.carrierFromVal, checkValTyPartial,
    denotValTyPartial, badSpace, bad_query,
    bind, pure, Except.bind, Except.pure]

-- Bad matrix storage must not be padded before the rank query.
example : PartialDirectOracle.oracle (fun _ => .array FlatArray.empty) [] [] .kernel
    matrixSpace (.var "m" (.space matrixSpace)) = .error .mismatch := by
  unfold PartialDirectOracle.oracle
  rw [PartialDirectOracle.query_eq]
  simp [PartialDirectOracle.step, matrixSpace, ValSpace.shpOfPartial,
    ValSpace.dofPartial, denotValB_partial, PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred, ffsDimensionPartial, ffsOperandRankPartial,
    bind, pure, Except.bind, Except.pure, FlatArray.empty]

-- Ordinary scalar evaluation remains successful.
example (ρ : ValEnvSem) (r : ℝ) :
    ∃ a, Adequacy.Partial.evalVal ρ [] [] (.rlit r) = .ok (.array a) := by
  simp [Adequacy.Partial.evalVal, denotValB_partial, PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred, PartialValueEval.withDimensions,
    PartialValueEval.dimensions, ValExpr.inferSpaceCtx, ValSpace.dofPartial,
    ValSpace.shpOfPartial, ValValSem.arrayOf, bind, pure, Except.bind, Except.pure]

end
end GLang.PartialDirectTests

open Lean Elab Command
elab "check_partial_direct_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``GLang.PartialDirectTests.bad_query, ``GLang.PartialDirectTests.failed_dim,
      ``GLang.PartialDirectTests.failed_zero, ``GLang.PartialDirectTests.nested_query,
      ``GLang.PartialDirectTests.zero_matrix_kernel, ``GLang.PartialDirectTests.bound_zero_kernel,
      ``GLang.PartialValueEval.withDimensions_error, ``GLang.PartialDirectOracle.query_eq,
      ``GLang.Adequacy.Partial.evalValCheckedAt_sound,
      ``GLang.ValueQueryDependencies.OracleAgreement.eval, ``GLang.PartialDirectLocality.guarded_child,
      ``GLang.PartialDirectLocality.oracle_eq,
      ``GLang.PartialDirectLocality.oracle_operand_error,
      ``GLang.PartialDirectLocality.oracle_shape_error,
      ``GLang.PartialDirectLocality.oracle_matrix,
      ``GLang.PartialDirectFv.oracle_fresh, ``GLang.PartialDirectFv.eval_fresh,
      ``GLang.PartialDirectFv.checked_fresh,
      ``GLang.PartialValueTransport.check_heq,
      ``GLang.PartialDirectOpenPush.reshape_eq, ``GLang.PartialDirectOpenPush.eval_open,
      ``GLang.PartialDirectOpenPush.oracle_openPush,
      ``GLang.PartialDirectOpenPush.checked_openPush,
      ``GLang.PartialDirectTests.named_zero_kernel,
      ``GLang.PartialDirectTests.malformed_named_zero] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected partial direct semantics axiom {n}: {ax}"
  logInfo "Connected partial evaluator/oracle rejects failed witnesses with no new axioms."
check_partial_direct_axioms
