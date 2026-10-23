import GLang.Proofs.Value.Presentation.PaperValueEnvironment
import GLang.Public.PaperValueDomainResults
import GLang.Metatheory

namespace GLang.PaperValueResults
open PartialValueDomains PaperValueDomains

theorem valueSoundnessExtended {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : RuntimeValue.PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : RuntimeValue.ValHasType ε e τ) :
    (∃ k, Nonempty (RuntimeValue.ValTValid ε τ k)) ∧
    ValExpr.inferType e = τ ∧
    (∀ s : ValSpace, ValSpace.dofPartial (PartialDirectOracle.oracle ρ [] []) s = (do
      let shape ← ValSpace.shpOfPartial (PartialDirectOracle.oracle ρ [] []) s
      pure (shape.foldr (· * ·) 1))) ∧
    PartialRel (PartialRelated τ (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ)
      (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ))
      (denotValB_partialCheckedAt PartialDirectOracle.oracle ρ [] [] τ e)
      (denotValB_partialCheckedAt PartialDirectOracle.oracle ρ [] [] τ e) ∧
    partialRecursiveResultEquiv τ _ (RuntimeValue.partialValueDomainSoundness ρ hρ he).1
      (Quotient.mk _ ⟨(denotValB_partial PartialDirectOracle.oracle ρ [] [] e).bind τ.carrierFromVal,
        partial_extract_results (RuntimeValue.partialValueDomainSoundness ρ hρ he).2⟩) =
      RuntimeValue.partialValueDenotation ρ hρ he := by
  obtain ⟨hctx⟩ := hρ.1
  exact ⟨by obtain ⟨k,hk⟩ := he.regular hctx; exact ⟨k,⟨hk⟩⟩,
    RuntimeValue.ValHasType.inferType_eq_of_typed he,
    fun s => Metatheory.valueShapeSoundness _ s,
    RuntimeValue.partialValueCheckedDomainSoundness ρ hρ he,
    RuntimeValue.partialValueDenotation_raw_eq ρ hρ he⟩

theorem valueSoundness {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : RuntimeValue.PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : RuntimeValue.ValHasType ε e τ) :
    (∃ k, Nonempty (RuntimeValue.ValTValid ε τ k)) ∧
    ValExpr.inferType e = τ ∧
    PartialRel (PartialRelated τ (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ)
      (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ))
      (denotValB_partialCheckedAt PartialDirectOracle.oracle ρ [] [] τ e)
      (denotValB_partialCheckedAt PartialDirectOracle.oracle ρ [] [] τ e) := by
  obtain ⟨hk, hinfer, _, hmember, _⟩ := valueSoundnessExtended ρ hρ he
  exact ⟨hk, hinfer, hmember⟩

/-- The operational creation history used by public progress. -/
abbrev ContextWF := Operational.ContextHistory
end GLang.PaperValueResults
