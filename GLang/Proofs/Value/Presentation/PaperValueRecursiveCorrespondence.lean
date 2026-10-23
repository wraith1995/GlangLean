import GLang.Proofs.Value.Presentation.PaperValueDomainEquivalence
import GLang.Proofs.Value.Presentation.PaperValueFullCorrespondence

/-! The actual checked evaluator interpreted in recursive mathematical domains.
This is a representation of its result, not a replacement evaluator. -/
namespace GLang.PaperValueResults
open PaperValueDomains

/-- Original typing in a valid environment gives a mathematical value: a sized
array, or an arbitrary dependent partial function between recursive domains,
or an explicit error. -/
noncomputable def valueDenotation {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : EnvWF ε ρ) (he : ValHasType ε e τ) :
    Except DimError (recursiveDomain directOracle τ ⟨ρ,[],[]⟩
      (valueDomainSoundness ρ hρ he).1).Carrier :=
  recursiveResultEquiv directOracle τ ⟨ρ,[],[]⟩ (valueDomainSoundness ρ hρ he).1
    (valueClass ρ hρ he)

/-- Raw and checked evaluation give the same recursive mathematical value. -/
theorem valueDenotation_raw_eq {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : EnvWF ε ρ) (he : ValHasType ε e τ) :
    recursiveResultEquiv directOracle τ ⟨ρ,[],[]⟩ (valueDomainSoundness ρ hρ he).1
      (checkedResultClass directOracle τ ⟨ρ,[],[]⟩ (valueDomainSoundness ρ hρ he).1
        (denotValB_semS directOracle ρ [] [] e) (valueDomainSoundness ρ hρ he).2) =
      valueDenotation ρ hρ he :=
  congrArg (recursiveResultEquiv directOracle τ ⟨ρ,[],[]⟩ (valueDomainSoundness ρ hρ he).1)
    (valueClass_raw_eq ρ hρ he)

/-- Failure is preserved with its original error code. -/
theorem valueDenotation_error {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : EnvWF ε ρ) (he : ValHasType ε e τ) (err : DimError)
    (herr : denotValB_semSChecked directOracle ρ [] [] e = .error err) :
    valueDenotation ρ hρ he = .error err := by
  unfold valueDenotation valueClass checkedResultClass
  simp only [herr, Except.bind]
  rfl

end GLang.PaperValueResults
