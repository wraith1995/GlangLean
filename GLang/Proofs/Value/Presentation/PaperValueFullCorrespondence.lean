import GLang.Proofs.Value.Presentation.PaperValueOriginalFamily
import GLang.Proofs.Value.Presentation.PaperValueDependentQuotient
import GLang.Public.PaperValueResults
import GLang.Proofs.Value.Presentation.PaperValueCheckedCorrespondence

/-! Full original-typing correspondence with supported dependent value domains.
No separate fragment typing judgment or evaluator-invariance premise is used. -/
namespace GLang.PaperValueResults
open PaperValueDomains

theorem valueDomainSoundness {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : EnvWF ε ρ) (he : ValHasType ε e τ) :
    TypeCoherent directOracle τ ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩ ∧
    PartialRel (RuntimeRelated directOracle τ ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩)
      (denotValB_semS directOracle ρ [] [] e) (denotValB_semS directOracle ρ [] [] e) := by
  obtain ⟨hctx⟩ := hρ.1
  obtain ⟨k,ht⟩ := he.regular hctx
  refine ⟨?_,?_⟩
  · exact (originalType_coherent_family ht hctx (fun _ : Unit => ρ)
      (fun _ _ => hρ.2) () ()).toCoherent directOracle τ _ _
  · exact originalExpr_related_family he hctx (fun _ : Unit => ρ)
      (fun _ _ => hρ.2) () ()

/-- The same domain theorem for the actual checked evaluator used by the
headline metatheory, including its ordinary decoder and checked reification. -/
theorem valueCheckedDomainSoundness {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : EnvWF ε ρ) (he : ValHasType ε e τ) :
    PartialRel (RuntimeRelated directOracle τ ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩)
      (denotValB_semSChecked directOracle ρ [] [] e)
      (denotValB_semSChecked directOracle ρ [] [] e) :=
  denot_checked_related he he directOracle _ _ (valueDomainSoundness ρ hρ he).2

/-- The actual checked interpretation as a member of the full dependent
quotient domain, derived directly from original typing. -/
noncomputable def valueClass {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : EnvWF ε ρ) (he : ValHasType ε e τ) :
    (dependentPER directOracle τ ⟨ρ,[],[]⟩ (valueDomainSoundness ρ hρ he).1).result.Domain :=
  checkedResultClass directOracle τ ⟨ρ,[],[]⟩ (valueDomainSoundness ρ hρ he).1
    (denotValB_semSChecked directOracle ρ [] [] e) (valueCheckedDomainSoundness ρ hρ he)

/-- Original type validity supplies coherence across any supported family of
related environments. This proof is used to identify their result quotients. -/
theorem valueFamilyCoherent {I : Type} {ε : ValCtx} {τ : ValTy} {k : ValKind}
    (ht : ValTValid ε τ k) (hc : ValCtxValid ε) (ρ : I → ValEnvSem)
    (hρ : ∀ i j, EnvironmentsRelated directOracle ε (ρ i) (ρ j)) :
    ∀ i j, TypeCoherent directOracle τ ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩ :=
  fun i j => (originalType_coherent_family ht hc ρ hρ i j).toCoherent directOracle τ _ _

/-- Changing supported environment representatives preserves the actual checked
quotient result, with canonical transport of dependent fibres. -/
theorem valueClass_family_eq {I : Type} {ε : ValCtx} {e : ValExpr} {τ : ValTy} {k : ValKind}
    (he : ValHasType ε e τ) (ht : ValTValid ε τ k) (hc : ValCtxValid ε)
    (ρ : I → ValEnvSem) (hρ : ∀ i j, EnvironmentsRelated directOracle ε (ρ i) (ρ j))
    (i j : I) :
    coherentFamily_resultMap directOracle τ (fun i => ⟨ρ i,[],[]⟩)
      (valueFamilyCoherent ht hc ρ hρ) i j
      (valueClass (ρ i) ⟨⟨hc⟩,hρ i i⟩ he) =
        valueClass (ρ j) ⟨⟨hc⟩,hρ j j⟩ he := by
  exact coherentFamily_checkedResultClass_eq directOracle τ (fun i => ⟨ρ i,[],[]⟩)
    (valueFamilyCoherent ht hc ρ hρ) (fun i => denotValB_semSChecked directOracle (ρ i) [] [] e)
    (fun i j => denot_checked_related he he directOracle _ _
      (originalExpr_related_family he hc ρ hρ i j)) i j

/-- The headline checked evaluator and raw denotation determine the same
mathematical value, including errors and dependent higher-order results. -/
theorem valueClass_raw_eq {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : EnvWF ε ρ) (he : ValHasType ε e τ) :
    checkedResultClass directOracle τ ⟨ρ,[],[]⟩ (valueDomainSoundness ρ hρ he).1
      (denotValB_semS directOracle ρ [] [] e) (valueDomainSoundness ρ hρ he).2 =
        valueClass ρ hρ he :=
  checkedResultClass_eq directOracle τ _ (valueDomainSoundness ρ hρ he).1 _ _
    (valueDomainSoundness ρ hρ he).2 (valueCheckedDomainSoundness ρ hρ he)
    (denot_checked_related_right he directOracle _ _ (valueDomainSoundness ρ hρ he).2)

end GLang.PaperValueResults
