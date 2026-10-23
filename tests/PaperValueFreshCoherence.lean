import GLang.Proofs.Value.Presentation.PaperValueFreshCoherence
import GLang.Proofs.Value.Presentation.PaperValueOracleExtensionality
import Lean
open GLang GLang.PaperValueDomains

-- Production freshness works at arbitrary dependent types and actual stacks;
-- there is no constant-oracle hypothesis or evaluator-invariance certificate.
example (τ : ValTy) (w w' : World) (x : VName) (v v' : ValValSem)
    (hG : ValTyCtxFresh x w.types) (hG' : ValTyCtxFresh x w'.types)
    (hx : x ∉ ValTy.fv τ) :
    FiberAgreement directOracle τ w w' (w.update x v) (w'.update x v') :=
  FiberAgreement.fresh directOracle_spec.fvIrrel τ w w' x v v' hG hG' hx

open Lean Elab Command
elab "check_fresh_correspondence_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``SpaceOracleAgreement.fresh, ``FiberAgreement.fresh,
      ``ContextRelated.update] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "Unexpected freshness assumption {n}: {ax}"
  logInfo "Dependent freshness/context extension use foundations only."
check_fresh_correspondence_axioms
