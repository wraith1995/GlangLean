import GLang.Proofs.Preservation.Context
import GLang.Proofs.Value.Runtime.RuntimeValueCorrespondence
import GLang.Proofs.Preservation.IndexedPreservation

namespace GLang.Operational
open PartialValueDomains PaperValueDomains

/-- The indexed operational context supplies formation; semantic consistency
only needs to supply the relation on its declared runtime bindings. -/
theorem TypedContext.valueEnvWF (h : TypedContext Δ Γ Γv Ψ) (ρ : ValEnvSem)
    (hρ : PartialEnvironmentsRelated PartialDirectOracle.oracle Γv ρ ρ) :
    RuntimeValue.PartialEnvWF PartialDirectOracle.oracle Γv ρ :=
  ⟨h.valueContextValid, hρ⟩

/-- The lookup cases of indexed preservation and value-domain soundness.
The entry is typed at its own inferred type, even when another basis-specific
representation of the same source variable has a different annotation. -/
theorem TypedContext.lookup_sound (h : TypedContext Δ Γ Γv Ψ)
    (hl : EvalCtx.lookup Ψ (x,b) = some v) (ρ : ValEnvSem)
    (hρ : PartialEnvironmentsRelated PartialDirectOracle.oracle Γv ρ ρ) :
    Nonempty (RuntimeValue.ValHasType Γv v (ValExpr.inferType v)) ∧
    (∃ k, Nonempty (RuntimeValue.ValTValid Γv (ValExpr.inferType v) k)) ∧
    PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle (ValExpr.inferType v)
      ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle ρ [] [] v)
      (denotValB_partial PartialDirectOracle.oracle ρ [] [] v) := by
  obtain ⟨hv⟩ := h.lookup_typed hl
  obtain ⟨hc⟩ := h.valueContextValid
  obtain ⟨k,hk⟩ := hv.regular hc
  exact ⟨⟨hv⟩, ⟨k,⟨hk⟩⟩,
    (RuntimeValue.partialValueDomainSoundness ρ (h.valueEnvWF ρ hρ) hv).2⟩

/-- The literal result of any supplied unchecked evaluation is well typed. -/
theorem TypedContext.preservation (h : TypedContext Δ Γ Γv Ψ)
    (he : ValExpr.OpStep Ψ e b v) : RuntimeValue.ExprTyped Γv v :=
  RuntimeValue.preservation_mutual.2.2.2 he Γv h.evalContext

/-- Preservation followed by partial soundness at exactly the inferred type. -/
theorem TypedContext.result_sound (h : TypedContext Δ Γ Γv Ψ)
    (he : ValExpr.OpStep Ψ e b v) (ρ : ValEnvSem)
    (hρ : PartialEnvironmentsRelated PartialDirectOracle.oracle Γv ρ ρ) :
    PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle (ValExpr.inferType v)
      ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle ρ [] [] v)
      (denotValB_partial PartialDirectOracle.oracle ρ [] [] v) :=
  (RuntimeValue.partialValueDomainSoundness ρ (h.valueEnvWF ρ hρ) (h.preservation he).some).2

end GLang.Operational
