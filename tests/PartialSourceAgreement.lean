import GLang.Proofs.Adequacy.Partial.Source.PartialSourceHistory
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceReification
import GLang.Proofs.Adequacy.Partial.Functions.PartialSourceFunctions
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialApplicationTransport
import Lean

open GLang GLang.PartialAdequacy

-- An oracle failure cannot satisfy source agreement by inventing dimension
-- zero, even when the supplied array and source basis are both empty.
example (σ : DEnv) (ρ : ValEnvSem) (s : Space) (B : BasisDenot) (x : DVal) :
    ¬ PartialAdequacy.Agree (fun _ _ _ _ _ _ => .error .mismatch) σ ρ [] [] []
      (.space s) (.space (.ffs .kernel .real (.rlit 0))) B x (.array FlatArray.empty) := by
  simp [PartialAdequacy.Agree, ValSpace.dofPartial, ValSpace.shpOfPartial,
    bind, Except.bind]

open Lean Elab Command
elab "check_partial_source_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``GLang.PartialAdequacy.Agree.decode,
      ``GLang.PartialAdequacy.applyBetween_agree,
      ``GLang.PartialAdequacy.lambda_result,
      ``GLang.PartialAdequacy.Agree.normalize,
      ``GLang.PartialAdequacy.Agree.stack_transport,
      ``GLang.PartialAdequacy.reificationClaim_holds,
      ``GLang.PartialAdequacy.DimsAt.complete,
      ``GLang.PartialAdequacy.History.lookup_current_result,
      ``GLang.PartialAdequacy.History.worldExtendNLAt,
      ``GLang.PartialAdequacy.History.ctxTele] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected partial source agreement axiom {n}: {ax}"
  logInfo "Partial source history and arbitrary-order reification have no new axioms."
check_partial_source_axioms
