import GLang.Proofs.Value.Presentation.PaperValueRawReshape
open GLang GLang.PaperValueDomains

-- Higher-order reshape transports arbitrary raw callbacks. No extensional
-- input relation, success assumption, or desired evaluation equality is used.
example (orc : FFSOracleSem) (w u : World) (td tc sd sc td' tc' sd' sc' : ValTy)
    (ht : RawTypePresentation orc (.piTy td tc) (.piTy td' tc') w u)
    (hs : RawTypePresentation orc (.piTy sd sc) (.piTy sd' sc') w u)
    (v : ValValSem) :
    reshapDenotSemBetweenS orc w.env w.types w.values w.types w.values v
      (.piTy td tc) (.piTy sd sc) =
    reshapDenotSemBetweenS orc u.env u.types u.values u.types u.values v
      (.piTy td' tc') (.piTy sd' sc') :=
  rawPresentation_reshape orc _ _ _ _ w.env u.env
    w.types u.types w.types u.types w.values u.values w.values u.values ht hs v

open Lean Elab Command
elab "check_raw_presentation_axioms" : command => do
  let foundation := #[``propext, ``Classical.choice, ``Quot.sound]
  let generic := [``presentation_fromEl, ``presentation_fromElChecked,
    ``presentation_toElDomainChecked,
    ``RawTypePresentation.fromEl, ``RawTypePresentation.toPresentation,
    ``rawPresentation_reshape]
  let live := [``presentation_eval_appV, ``rawPresentation_eval_reshape, ``presentation_eval_vlam_open, ``presentation_pi_open,
    ``rawPresentation_openPush, ``rawPresentation_pi_open]
  for n in generic ++ live do
    unless (← getConstInfo n) matches .thmInfo _ do
      throwError "Expected theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless foundation.contains ax || (live.contains n && ax == ``GLang.Matrix.exists_gsvd) do
        throwError "Unexpected presentation axiom in {n}: {ax}"
  logInfo "Raw presentation/conversion/reshape transport uses foundations; live opening adds at most existing GSVD existence."
check_raw_presentation_axioms
