import GLang.Proofs.Value.Presentation.PaperValueOracleSubstitution
import Lean
open GLang GLang.PaperValueDomains
open Lean Elab Command
elab "check_oracle_substitution_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``SubstSpaceAgreement.shapes, ``directOracle_eq_of_substitution_step] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected production substitution assumption {n}: {ax}"
  logInfo "Production FFS substitution inherits only the existing GSVD axiom."
check_oracle_substitution_axioms
