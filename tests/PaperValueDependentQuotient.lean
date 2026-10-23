import GLang.Proofs.Value.Presentation.PaperValueDependentQuotient
import Lean
open GLang GLang.PaperValueDomains
open Lean Elab Command

elab "check_dependent_quotient_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``dependentPER, ``coherentFamily_classMap_roundtrip,
      ``dependentFibre_coherent, ``dependentApply_representative,
      ``coherentFamily_checkedResultClass_eq] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected dependent quotient assumption {n}: {ax}"
  logInfo "Full dependent quotient application is representative-independent using only foundations."
check_dependent_quotient_axioms

example (orc : FFSOracleSem) (τ : ValTy) (w : World)
    (hc : TypeCoherent orc τ w w) (err : DimError)
    (a : (dependentPER orc τ w hc).Support) :
    (Quotient.mk _ ⟨Except.error err,rfl⟩ : (dependentPER orc τ w hc).result.Domain) ≠
      Quotient.mk _ ⟨Except.ok a.val,a.property⟩ :=
  (dependentPER orc τ w hc).result_error_ne_ok err a
