import GLang.Examples.TangentOuterFrame
import Lean

open GLang GLang.Examples.TangentCoordinates

-- Actual closed derivation of the dual-evaluation tensor on a plane.
example : ValExpr.OpStep ∅ (dualEval Examples.Paper.R2) (dualEvalBasis pointBasis)
    (dualEvalCode pointSV) :=
  dualEval_op (b := pointBasis) rfl (SValid.lc (Examples.Paper.svR2 (ε := ∅))) (.dsum .real .real)

-- Actual outer nonlinear-frame derivation with a stored parameterization function.
example : ValExpr.OpStep
    (Finmap.singleton ("f", Basis.frame pointBasis parameterBasis)
      (ValExpr.var "f" (.piTy (.space pointSV) (.space parameterSV))))
    Examples.Paper.ev movingDualFrame movingDualCode :=
  movingDualFrame_op (Γ := Examples.Paper.εf)
    Finmap.lookup_singleton_eq Finmap.lookup_singleton_eq

-- The degenerate domain is covered by the same ordinary rules.
example : ValExpr.OpStep ∅ (dualEval .empty) (dualEvalBasis .empty)
    (dualEvalCode .empty) := dualEval_op (b := .empty) rfl .empty .empty

private def e₀ : Term := .dsumE (.real 1) (.real 0)
private def e₁ : Term := .dsumE (.real 0) (.real 1)
private def d₀ : ValExpr := .dsumE (.rlit 1) (.rlit 0)
private def d₁ : ValExpr := .dsumE (.rlit 0) (.rlit 1)

-- Complete, closed projection + four projected generators + RREF lowering.
-- In particular the first generator is zero; completion must skip it.
example : ValExpr.OpStep ∅ (projectedArea Examples.Paper.R2 e₀ e₁)
    (projectedAreaBasis pointBasis e₀ e₁)
    (measuredAreaCode pointSV d₀ d₁ d₀ d₁) := by
  have h₀ : ValExpr.OpStep ∅ e₀ pointBasis d₀ :=
    .dsumE (.rlit 1) (.rlit 0) rfl rfl
  have h₁ : ValExpr.OpStep ∅ e₁ pointBasis d₁ :=
    .dsumE (.rlit 0) (.rlit 1) rfl rfl
  exact measuredArea_op (b := pointBasis) rfl (SValid.lc (Examples.Paper.svR2 (ε := ∅)))
    ⟨trivial, trivial⟩ (.dsum .real .real) h₀ h₁ h₀ h₁

-- The source image basis is formed from a cokernel basis, not an arbitrary
-- two-dimensional domain basis.
example (f : Term) :
    tangentBasis f = .image (.proj (.coker Examples.Paper.R2 Examples.Paper.R3 f)
      pointBasis ambientBasis) := rfl

-- Foundation-only closure includes the actual area projection, completion,
-- moving-basis conversion, source formation and coordinate algebra.
open Lean Elab Command in
elab "check_tangent_coordinate_axioms" : command => do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``dualEval_op, ``antiSym_op, ``curry_op, ``antiSymLinear_op,
      ``projectedArea_op, ``measuredArea_op, ``tangentBasis_cob,
      ``tangentMeasuredArea_op, ``tangentDualEval_op,
      ``tangentMeasuredArea_wellFormed, ``tangentDualEval_wellFormed,
      ``delta_pairing, ``normalized_tensor_area, ``movingDualFrame_op,
      ``movingDualFrame_valid, ``ValSpace.dofUB_openRec] do
    let axioms ← Lean.collectAxioms n
    for ax in axioms do
      unless standard.contains ax do
        throwError "Unexpected project assumption in {n}: {ax}"
    logInfo m!"{n}: {axioms}"

check_tangent_coordinate_axioms
