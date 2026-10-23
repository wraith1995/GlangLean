import GLang.Public.PaperValueResults

namespace GLang.PaperPartialValueSoundnessTests
open PartialValueDomains PaperValueDomains

-- The exported statement retains actual partial type errors and full recursive
-- result relatedness, including arbitrarily nested function input types.
example {ε : ValCtx} {e : ValExpr} {d c t : ValTy} (ρ : ValEnvSem)
    (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : ValHasType ε e (.piTy (.piTy d c) t)) :
    PartialRel (PartialRelated (.piTy (.piTy d c) t)
      (denotValTyPartial PartialDirectOracle.oracle ρ [] [] (.piTy (.piTy d c) t))
      (denotValTyPartial PartialDirectOracle.oracle ρ [] [] (.piTy (.piTy d c) t)))
      (denotValB_partialCheckedAt PartialDirectOracle.oracle ρ [] [] (.piTy (.piTy d c) t) e)
      (denotValB_partialCheckedAt PartialDirectOracle.oracle ρ [] [] (.piTy (.piTy d c) t) e) :=
  (PaperValueResults.valueSoundness ρ hρ.runtime he.runtime).2.2

-- The exported theorem recovers the exact type, including dependent functions.
example {ε : ValCtx} {e : ValExpr} {τ : ValTy} (ρ : ValEnvSem)
    (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ) (he : ValHasType ε e τ) :
    ValExpr.inferType e = τ :=
  (PaperValueResults.valueSoundness ρ hρ.runtime he.runtime).2.1

-- Shape failure is preserved by the exported dimension equation.
example {ε : ValCtx} {e : ValExpr} {τ : ValTy} (ρ : ValEnvSem)
    (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ) (he : ValHasType ε e τ)
    (s : ValSpace) (err : DimError)
    (hs : ValSpace.shpOfPartial (PartialDirectOracle.oracle ρ [] []) s = .error err) :
    ValSpace.dofPartial (PartialDirectOracle.oracle ρ [] []) s = .error err := by
  rw [(PaperValueResults.valueSoundnessExtended ρ hρ.runtime he.runtime).2.2.1 s, hs]
  rfl

end GLang.PaperPartialValueSoundnessTests

open Lean Elab Command
elab "check_paper_partial_value_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in ← Lean.collectAxioms ``GLang.PaperValueResults.valueSoundness do
    unless permitted.contains ax do
      throwError "Unexpected paper partial-value axiom: {ax}"
  logInfo "Paper value wrapper uses the actual partial higher-order theorem; axiom gate passes."
check_paper_partial_value_axioms
