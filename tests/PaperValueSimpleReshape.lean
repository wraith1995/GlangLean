import GLang.Proofs.Value.Presentation.PaperValueSimpleReshape
import Lean

open GLang GLang.PaperValueDomains

-- The higher-order domain includes a callback whose domain is itself an arrow.
-- Both source and target can independently contain such nested function types.
example (a b c d : SimpleTy) (orc : FFSOracleSem) (w w' : World)
    (v v' : ValValSem) (h : (SimpleTy.arrow (.arrow a b) c).runtimeRel v v') :
    PartialRel (SimpleTy.arrow (.arrow b a) d).runtimeRel
      (reshapDenotSemS orc w.env w.types w.values v
        (SimpleTy.arrow (.arrow b a) d).toValTy (SimpleTy.arrow (.arrow a b) c).toValTy)
      (reshapDenotSemS orc w'.env w'.types w'.values v'
        (SimpleTy.arrow (.arrow b a) d).toValTy (SimpleTy.arrow (.arrow a b) c).toValTy) :=
  SimpleTy.reshape_related _ _ orc w w' v v' h

-- A kind mismatch remains an error, even if the target is a nested arrow.
example (orc : FFSOracleSem) (w : World) (a b c : SimpleTy) :
    reshapDenotSemS orc w.env w.types w.values (.array (FlatArray.zeros 1))
      (SimpleTy.arrow (.arrow a b) c).toValTy (SimpleTy.space .real).toValTy =
      .error .mismatch := by
  simp only [SimpleTy.toValTy, reshapDenotSemS]

open Lean Elab Command
elab "check_simple_reshape_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``SimpleTy.reshape_between_related, ``SimpleTy.reshape_related,
      ``SimpleTy.eval_reshape_related] do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax ||
          (n == ``SimpleTy.eval_reshape_related && ax == ``GLang.Matrix.exists_gsvd) do
        throwError "Unexpected simple reshape assumption in {n}: {ax}"
  logInfo "Arbitrary-order simple reshape uses foundations only; live expression wrapper adds at most existing GSVD existence."

check_simple_reshape_axioms
