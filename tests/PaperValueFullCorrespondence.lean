import GLang.Proofs.Value.Presentation.PaperValueFullCorrespondence
import Lean
open GLang GLang.PaperValueDomains GLang.PaperValueResults

example {ε : ValCtx} {e : ValExpr} {τ : ValTy} (ρ : ValEnvSem)
    (hρ : EnvWF ε ρ) (he : ValHasType ε e τ) :
    TypeCoherent directOracle τ ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩ ∧
    PartialRel (RuntimeRelated directOracle τ ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩)
      (denotValB_semS directOracle ρ [] [] e) (denotValB_semS directOracle ρ [] [] e) :=
  valueDomainSoundness ρ hρ he

open Lean Elab Command
elab "check_full_correspondence_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``valueDomainSoundness, ``valueCheckedDomainSoundness,
      ``valueClass, ``valueClass_family_eq, ``valueClass_raw_eq] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected full original correspondence assumption {n}: {ax}"
  logInfo "Full original value-domain correspondence inherits only existing GSVD existence."
check_full_correspondence_axioms
