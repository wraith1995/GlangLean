import GLang.Metatheory
import Lean

open Lean Elab Command

/-- Integration gate: canonical source bases and syntactic metatheory introduce
no project axiom, including the full numerical adequacy closures. -/
elab "check_public_canonical_fsv_axioms" : command => do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let pure := [``GLang.Metatheory.surfaceElaborationUnique,
    ``GLang.Metatheory.surfaceTypingUnique,
    ``GLang.Metatheory.sourceSoundness,
    ``GLang.Metatheory.sourceBasisSoundness,
    ``GLang.Metatheory.standardBasisSoundness,
    ``GLang.Metatheory.basisAdequacy,
    ``GLang.Metatheory.preservation, ``GLang.Metatheory.progress]
  let numerical := [``GLang.Metatheory.valueSoundness,
    ``GLang.Metatheory.valueTermSoundness,
    ``GLang.Metatheory.valueDenotationCorrespondence,
    ``GLang.Metatheory.spaceAdequacy,
    ``GLang.Metatheory.termAdequacy, ``GLang.Metatheory.cobAdequacy,
    ``GLang.Metatheory.dimensionAdequacy, ``GLang.Metatheory.checkedProgressAdequacy]
  for n in pure ++ numerical do
    let axioms ← Lean.collectAxioms n
    for ax in axioms do
      unless standard.contains ax do
        throwError "Unexpected project assumption in {n}: {ax}"
    logInfo m!"{n}: {axioms}"

check_public_canonical_fsv_axioms
