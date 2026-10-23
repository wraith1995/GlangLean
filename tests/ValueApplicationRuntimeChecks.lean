import GLang.Proofs.Adequacy.Partial.Evaluation.PartialRuntimeChecks
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectOracle

namespace GLang
open PartialValueEval

private noncomputable def emptyArray : ValValSem := .arrayOf 0 (fun _ => 0)
private noncomputable def scalarArray : ValValSem := .arrayOf 1 (fun _ => 0)
private noncomputable def badScalarFunction : ValValSem :=
  .fn FlatArray (fun _ => .ok emptyArray)

example (ρ : ValEnvSem) :
    applyChecked PartialDirectOracle.oracle ρ [] [] (.space .real) (.space .real)
      (.ok badScalarFunction) (.ok scalarArray) = .error .mismatch := by
  simp [applyChecked, checkResult, checkRuntime, checkValTyPartial,
    denotValTyPartial, PartialValType.check, PartialValType.space, ValTy.carrierEl, ValSpace.dofPartial, ValSpace.shpOfPartial,
    badScalarFunction, scalarArray, emptyArray, ValTy.carrierFromVal,
    ValValSem.applyTyped, ValValSem.arrayOf, FlatArray.ofFn, Except.map,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

example (ρ : ValEnvSem) (f : ValValSem) :
    applyChecked PartialDirectOracle.oracle ρ [] [] (.space .real) (.space .real)
      (.ok f) (.ok emptyArray) = .error .mismatch := by
  simp [applyChecked, checkResult, checkValTyPartial, denotValTyPartial,
    PartialValType.check, PartialValType.space, ValTy.carrierEl, ValSpace.dofPartial, ValSpace.shpOfPartial,
    emptyArray, ValTy.carrierFromVal, ValValSem.arrayOf, FlatArray.ofFn,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

-- A returned function retains a check: its bad scalar result fails when called.
example (ρ : ValEnvSem) :
    ∃ f, checkResult PartialDirectOracle.oracle ρ [] []
      (.piTy (.space .real) (.space .real)) (.ok badScalarFunction) = .ok f ∧
      f (FlatArray.ofFn 1 (fun _ => 0)) = .error .mismatch := by
  simp [checkResult, checkValTyPartial, denotValTyPartial,
    PartialValType.check, PartialValType.space, PartialValType.piTy, ValTy.carrierEl, ValSpace.dofPartial, ValSpace.shpOfPartial,
    badScalarFunction, emptyArray, ValTy.carrierFromVal,
    ValValSem.arrayOf, FlatArray.ofFn, Except.map,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

end GLang

open Lean Elab Command
elab "check_runtime_boundary_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``GLang.PartialValueEval.applyChecked_sound,
      ``GLang.PartialValueEval.checkResult_related,
      ``GLang.PartialAdequacy.ResultAgree.checkRuntime,
      ``GLang.PartialAdequacy.applyChecked_agree] do
    for ax in ← Lean.collectAxioms name do
      unless permitted.contains ax do
        throwError "Unexpected runtime-boundary axiom in {name}: {ax}"
  logInfo "Runtime membership, recursive relation, and source agreement axiom gates pass."
check_runtime_boundary_axioms

namespace GLang
-- The explicit result reshape rejects a compiled application whose inferred
-- empty-array result cannot represent the requested scalar.
example (ρ : ValEnvSem) :
    denotValB_partial PartialDirectOracle.oracle ρ [] []
      (.applyAt (.vlam (.space .real) (.space .empty) (.zero .empty))
        (.rlit 1) (.space .real)) = .error .mismatch := by
  simp [ValExpr.applyAt, ValExpr.applyValue, denotValB_partial,
    PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred, PartialValueEval.applyChecked,
    PartialValueEval.checkResult, PartialValueEval.checkRuntime,
    checkValTyPartial, denotValTyPartial, PartialValType.check,
    PartialValType.space, ValTy.carrierEl, ValTy.carrierFromVal,
    ValValSem.applyTyped, ValExpr.inferType, ValExpr.inferTypeCtx, ValTy.domain,
    ValTy.applyCodomain, ValTy.substBound, ValSpace.substBound, ValExpr.substBound, ValSpace.dof,
    PartialValueEval.withDimensions, PartialValueEval.dimensions,
    ValExpr.inferSpaceCtx, ValSpace.dofPartial, ValSpace.shpOfPartial,
    ValValSem.arrayOf, FlatArray.ofFn, Except.map,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
end GLang

namespace GLang

example (ρ : ValEnvSem) :
    denotValB_partial PartialDirectOracle.oracle ρ [] []
      (.applyAt
        (.applyAt
          (.vlam (.space .real) (.piTy (.space .real) (.space .empty))
            (.vlam (.space .real) (.space .empty) (.zero .empty)))
          (.rlit 1) (.piTy (.space .real) (.space .real)))
        (.rlit 1) (.space .real)) = .error .mismatch := by
  simp [ValExpr.applyAt, ValExpr.applyValue, denotValB_partial,
    PartialValueEval.applyDomainChecked, PartialValueEval.applyBetween,
    PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, PartialValueEval.reshapeInferred, PartialValueEval.applyChecked,
    PartialValueEval.checkResult, PartialValueEval.checkRuntime,
    checkValTyPartial, denotValTyPartial, PartialValType.check,
    PartialValType.space, PartialValType.piTy, ValTy.carrierEl,
    ValTy.carrierFromVal, ValTy.carrierToVal,
    ValValSem.applyTyped, ValExpr.inferType, ValExpr.inferTypeCtx, ValTy.domain,
    ValTy.applyCodomain, ValTy.substBound, ValSpace.substBound, ValExpr.substBound, ValSpace.dof,
    PartialValueEval.withDimensions, PartialValueEval.dimensions,
    ValExpr.inferSpaceCtx, ValSpace.dofPartial, ValSpace.shpOfPartial,
    ValValSem.arrayOf, FlatArray.ofFn, Except.map,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
end GLang
