import GLang.Proofs.Value.Presentation.PaperValueReshapeExtensionality
import Lean

open GLang GLang.PaperValueDomains

-- A function reshape defers its domain check until application; a zero-length
-- target argument cannot silently become a scalar source argument.
example (orc : FFSOracleSem) (w : World) :
    (reshapDenotSemS orc w.env w.types w.values
      (.fn FlatArray (fun _ => .ok (.array (FlatArray.zeros 1))))
      (.piTy (.space .empty) (.space .real))
      (.piTy (.space .real) (.space .real))).bind
        (fun f => f.applyTyped FlatArray.empty) = .error .mismatch := by
  simp [Except.bind, ValTypeSem.El, reshapDenotSemS, ValValSem.applyTyped, denotValTyS,
    ValValSem.fromElChecked, reshapDenotSemBetweenS, reshapArrayBetweenS,
    FlatArray.empty, FlatArray.ofFn]

open Lean Elab Command
elab "check_reshape_extensionality_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let live := [``eval_reshape_space_related, ``eval_reshape_firstOrder_related]
  for n in [``reshape_between_space_related, ``reshape_space_related,
      ``reshape_firstOrder_related] ++ live do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax || (live.contains n && ax == ``GLang.Matrix.exists_gsvd) do
        throwError "Unexpected reshape bridge assumption in {n}: {ax}"
  logInfo "Reshape conversions use foundations only; expression evaluator bridges add at most existing GSVD existence."

check_reshape_extensionality_axioms
