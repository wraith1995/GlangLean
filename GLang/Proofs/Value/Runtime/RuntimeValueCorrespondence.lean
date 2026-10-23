import GLang.Proofs.Value.Runtime.RuntimeValueOriginalFamily
import GLang.Proofs.Value.Partial.PartialValueCheckedRelation

/-! Full original-typing correspondence for the live partial evaluator and
its checked structural interpretation. Recursive dependent function domains
include explicit errors at the type and every result fibre. -/
namespace GLang.RuntimeValue
open PartialValueDomains
open PaperValueDomains PaperValueDomains.ExtensionalQuotient

/-- Formation of declarations and membership of their runtime bindings. -/
def PartialEnvWF (orc : PartialFFSOracleSem) (ε : ValCtx) (ρ : ValEnvSem) : Prop :=
  Nonempty (ValCtxValid ε) ∧ PartialEnvironmentsRelated orc ε ρ ρ

theorem PartialEnvWF.empty (orc : PartialFFSOracleSem) (ρ : ValEnvSem) : PartialEnvWF orc ∅ ρ :=
  ⟨⟨fun _ _ h => by simp at h⟩, fun _ _ h => by simp at h⟩

/-- Original typing and recursive membership of declared environment values
supply coherence and a self-related actual partial computation. -/
theorem partialValueDomainSoundness {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : ValHasType ε e τ) :
    PartialCoherent τ (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ)
      (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ) ∧
    PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle τ ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle ρ [] [] e)
      (denotValB_partial PartialDirectOracle.oracle ρ [] [] e) := by
  obtain ⟨hc⟩ := hρ.1
  have hr := partial_originalExpr_result_family he hc (fun _ : Unit => ρ) (fun _ _ => hρ.2) () ()
  exact ⟨hr.2.toCoherent _ _ _ _,hr.1⟩

/-- The actual checked computation belongs to the same full recursive PER. -/
theorem partialValueCheckedDomainSoundness {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : ValHasType ε e τ) :
    PartialRel (PartialRelated τ (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ)
      (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ))
      (denotValB_partialCheckedAt PartialDirectOracle.oracle ρ [] [] τ e)
      (denotValB_partialCheckedAt PartialDirectOracle.oracle ρ [] [] τ e) := by
  rw [checked_eq_validate]
  exact validate_related τ _ _ (partialValueDomainSoundness ρ hρ he).1 _ _
    (partial_extract_results (partialValueDomainSoundness ρ hρ he).2)

noncomputable def partialValueClass {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : ValHasType ε e τ) :
    (partialPER τ (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ)
      (partialValueDomainSoundness ρ hρ he).1).result.Domain :=
  Quotient.mk _ ⟨denotValB_partialCheckedAt PartialDirectOracle.oracle ρ [] [] τ e,
    partialValueCheckedDomainSoundness ρ hρ he⟩

/-- The live checked evaluator represented as a sized array or an arbitrary
recursive dependent partial function, with explicit error throughout. -/
noncomputable def partialValueDenotation {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : ValHasType ε e τ) :
    Except DimError (partialRecursiveDomain τ (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ)
      (partialValueDomainSoundness ρ hρ he).1).Carrier :=
  partialRecursiveResultEquiv τ _ (partialValueDomainSoundness ρ hρ he).1 (partialValueClass ρ hρ he)

/-- Raw and checked evaluation represent exactly the same recursive value. -/
theorem partialValueDenotation_raw_eq {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : ValHasType ε e τ) :
    partialRecursiveResultEquiv τ _ (partialValueDomainSoundness ρ hρ he).1
      (Quotient.mk _ ⟨(denotValB_partial PartialDirectOracle.oracle ρ [] [] e).bind τ.carrierFromVal,
        partial_extract_results (partialValueDomainSoundness ρ hρ he).2⟩) =
      partialValueDenotation ρ hρ he :=
  congrArg (partialRecursiveResultEquiv τ _ (partialValueDomainSoundness ρ hρ he).1)
    (checked_class_eq PartialDirectOracle.oracle ρ [] [] τ e
      (partialValueDomainSoundness ρ hρ he).1
      (partial_extract_results (partialValueDomainSoundness ρ hρ he).2))

/-- Runtime errors retain their original error code. -/
theorem partialValueDenotation_error {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : ValHasType ε e τ) (err : DimError)
    (herr : denotValB_partialCheckedAt PartialDirectOracle.oracle ρ [] [] τ e = .error err) :
    partialValueDenotation ρ hρ he = .error err := by
  unfold partialValueDenotation partialValueClass
  simp only [herr]
  rfl

/-- Type failures, including failed dimensions, have no successful carrier. -/
theorem partialValueDenotation_type_error {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : ValHasType ε e τ) (err : DimError)
    (herr : denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ = .error err) :
    partialValueDenotation ρ hρ he = .error err := by
  apply partialValueDenotation_error ρ hρ he err
  rw [checked_eq_validate,herr]
  rfl

/-- Canonical transport of result classes between a coherent type family. -/
noncomputable def partialFamilyResultEquiv (τ : ValTy) {I : Type}
    (T : I → Except DimError (PartialValType τ))
    (hc : ∀ i j, PartialCoherent τ (T i) (T j)) (i j : I) :
    (partialPER τ (T i) (hc i i)).result.Domain ≃
      (partialPER τ (T j) (hc j j)).result.Domain :=
  PER.domainEquiv _ _ (by
    intro r s
    cases r <;> cases s <;> simp only [ExtensionalQuotient.PER.result,PartialRel]
    exact (partialFamily_laws τ T hc).transport i i j j _ _)

/-- Related original environments give the same checked result class under
canonical transport; recursive mathematical-domain equivalences preserve it. -/
theorem partialValueClass_family_eq {I : Type} {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (he : ValHasType ε e τ) (hc : ValCtxValid ε)
    (ρ : I → ValEnvSem)
    (hρ : ∀ i j, PartialEnvironmentsRelated PartialDirectOracle.oracle ε (ρ i) (ρ j))
    (i j : I) :
    partialFamilyResultEquiv τ (fun i => denotValTyPartial PartialDirectOracle.oracle (ρ i) [] [] τ)
      (fun i j => (partial_originalExpr_result_family he hc ρ hρ i j).2.toCoherent _ _ _ _) i j
      (partialValueClass (ρ i) ⟨⟨hc⟩,hρ i i⟩ he) =
      partialValueClass (ρ j) ⟨⟨hc⟩,hρ j j⟩ he := by
  apply Quotient.sound
  have hco := fun i j => (partial_originalExpr_result_family he hc ρ hρ i j).2.toCoherent
    PartialDirectOracle.oracle τ _ _
  have hval := validate_related τ _ _ (hco i j) _ _
    (partial_extract_results (partial_originalExpr_related_family he hc ρ hρ i j))
  rw [←checked_eq_validate,←checked_eq_validate] at hval
  change PartialRel (PartialRelated τ
    (denotValTyPartial PartialDirectOracle.oracle (ρ j) [] [] τ)
    (denotValTyPartial PartialDirectOracle.oracle (ρ j) [] [] τ))
    (denotValB_partialCheckedAt PartialDirectOracle.oracle (ρ i) [] [] τ e)
    (denotValB_partialCheckedAt PartialDirectOracle.oracle (ρ j) [] [] τ e)
  cases hi : denotValB_partialCheckedAt PartialDirectOracle.oracle (ρ i) [] [] τ e <;>
    cases hj : denotValB_partialCheckedAt PartialDirectOracle.oracle (ρ j) [] [] τ e <;>
    simp only [hi,hj,PartialRel] at hval ⊢
  exact ((partialFamily_laws τ (fun i => denotValTyPartial PartialDirectOracle.oracle (ρ i) [] [] τ) hco).transport
    i j j j _ _).1 hval

end GLang.RuntimeValue
