import GLang.Value.Dimensions
import GLang.Metatheory
import Lean

open GLang GLang.V2
noncomputable section

-- Public source progress needs only the ordinary operational history.
example : ∃ v τ, Operational.Term ∅ ∅ ∅ (.real 0) .one v τ ∧
    ValExpr.inferType v = τ ∧ ValExpr.inferSpaceCtx [] v = ValTy.spaceOf τ :=
  Metatheory.progress Operational.TypedContext.empty (.real_lit 0) .one

-- FFS failure is an error for all four operations, including kernel and
-- coimage, whose totalized rank-zero formulas would otherwise be nonzero.
example (p : ValFFSProp) :
    ffsDimensionPartial p (.ok [1, 1]) (.error .mismatch) = .error .mismatch := rfl

-- Shape and dimension failures propagate through sums and products.
example (p : ValFFSProp) (s : ValSpace) (e : ValExpr) :
    ValSpace.dofPartial (fun _ _ _ => .error .mismatch)
      (.tprod (.dsum .real (.ffs p s e)) .real) = .error .mismatch := by
  simp [ValSpace.dofPartial, ValSpace.shpOfPartial, bind, pure, Except.bind, Except.pure]

-- Malformed storage cannot be read as a padded 1-by-1 matrix.
example : ffsOperandRankPartial (.ok [1, 1]) (.ok (.array FlatArray.empty)) =
    .error .mismatch := by
  apply ffsOperandRankPartial_wrong_length
  decide

-- A successful zero-dimensional matrix is still a matrix; it is not confused
-- with the preceding failure case.
example : ffsOperandRankPartial (.ok [0, 1]) (.ok (.array FlatArray.empty)) = .ok 0 := by
  rw [ffsOperandRankPartial_matrix 0 1 _ (by rfl)]
  have hz : denotAsMatrix 0 1 FlatArray.empty.get = 0 := by
    ext i
    exact Fin.elim0 i
  rw [hz, Matrix.rank_zero]

def badMatrix : ValExpr := .mtm 1 1 .empty .real
  (.zero (.tprod .real .real)) (.zero (.tprod .real .real))

example (ρ : ValEnvSem) :
    ffsDimensionPartial .kernel (.ok [1, 1])
      (denotValB_semS directOracle ρ [] [] badMatrix) = .error .mismatch := by
  have hbad : denotValB_semS directOracle ρ [] [] badMatrix = .error .mismatch := by
    simp [badMatrix, denotValB_semS, ValValSem.bindArrays, ValValSem.bindArray,
      ValValSem.arrayOf, ValueShape.mtm, ValExpr.inferSpaceCtx]
  rw [hbad]
  rfl

open Lean Elab Command
elab "check_boundary_repair_axioms" : command => do
  let foundations := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ValSpace.shpOfPartial_success, ``ValSpace.dofPartial_success,
      ``ffsDimensionPartial_error, ``ffsOperandRankPartial_wrong_length,
      ``ffsDimensionPartial_matrix, ``Metatheory.progress] do
    for ax in ← Lean.collectAxioms n do
      unless foundations.contains ax do
        throwError "Unexpected boundary primitive axiom {n}: {ax}"
  logInfo "Partial dimension errors and ordinary-history progress add no axioms."
check_boundary_repair_axioms
