import GLang.Artifact
import Lean

open GLang Lean Meta Elab Command

private def headlines : List Lean.Name :=
  [``Metatheory.surfaceElaborationUnique, ``Metatheory.surfaceTypingUnique,
   ``Metatheory.sourceSoundness, ``Metatheory.valueSoundness,
   ``Metatheory.preservation, ``Metatheory.progress,
   ``Metatheory.checkedProgressAdequacy, ``Metatheory.termAdequacy,
   ``Metatheory.cobAdequacy, ``Metatheory.dimensionAdequacy,
   ``PaperSourceResults.sourceSoundness, ``PaperSourceResults.innerProduct,
   ``PaperBasisResults.sourceBasisSoundness, ``PaperBasisResults.standardBasisSoundness,
   ``PaperValueResults.valueSoundness, ``PaperOperationalResults.preservation,
   ``PaperOperationalResults.progress, ``PaperAdequacyResults.typeAdequacy,
   ``PaperAdequacyResults.termAdequacy, ``PaperAdequacyResults.cobAdequacy,
   ``PaperAdequacyResults.progressAndAdequacy]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for n in headlines do
    unless (← getConstInfo n) matches .thmInfo _ do
      throwError "Public theorem missing: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  logInfo m!"{headlines.length} public theorems: standard foundations only."
