import GLang.Proofs.Value.Presentation.PaperValuePrimitiveSized
import Lean

open GLang GLang.PaperValueDomains

-- Primitive coverage includes every numerical family, including the active
-- prefix sum and paired singular-vector selectors.
example (a b c : ValExpr) :
    primitiveOperands (.gsvdV a b c) = [a, b, c] := rfl
example (s : ValSpace) (es : List ValExpr) :
    primitiveOperands (.vsum s es) = es := rfl
example (a : ValExpr) : primitiveOperands (.svds a) = [a] := rfl

-- Failed operand computations are compared too; no successful-evaluation
-- premise weakens the congruence statement.
example (orc : FFSOracleSem) (w w' : World) (a : FlatArray) (s : ValSpace) :
    ¬ PartialRel (RuntimeRelated orc (.space s) w w')
      (.error DimError.mismatch) (.ok (.array a)) := by
  simp [PartialRel]

open Lean Elab Command
elab "check_primitive_extensionality_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``arrayPrimitive_eval_congr, ``base_results_eq,
      ``arrayPrimitive_eval_congr_of_related, ``arrayPrimitive_sized,
      ``arrayPrimitive_related_of_eval_eq] do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected primitive correspondence assumption in {n}: {ax}"
  logInfo "Primitive congruence: standard foundations only."

check_primitive_extensionality_axioms
