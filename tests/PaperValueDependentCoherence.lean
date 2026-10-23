import GLang.Proofs.Value.Presentation.PaperValueDependentCoherence
import Lean
open GLang GLang.PaperValueDomains Lean Elab Command
elab "check_dependent_coherence_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``World.carrier_eq, ``related_fiber_transport,
      ``runtime_fiber_transport, ``runtime_fiber_transport_iff,
      ``FiberAgreement.symm, ``TypeCoherent.fiber_transport] do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected dependent coherence assumption in {n}: {ax}"
  logInfo "Full dependent fibre transport uses foundations only."
check_dependent_coherence_axioms
