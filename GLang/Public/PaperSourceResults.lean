import GLang.Metatheory
import GLang.Elaboration.Uniqueness

/-! Source soundness and inner-product correctness under inductive context formation and reserved-name freshness. -/
namespace GLang.PaperSourceResults

def TypeDenotationForm (σ : DEnv) (τ : Ty) : Prop :=
  match τ with
  | .space s => denotTy σ τ = HType.hil (denotSpace σ s)
  | .piTy _ _ => ∃ (A : Type) (fibers : A → HType),
      denotTy σ τ = HType.sec A fibers

theorem typeDenotationForm (σ : DEnv) (τ : Ty) : TypeDenotationForm σ τ := by
  cases τ with
  | space s => rfl
  | piTy domain codomain => exact ⟨_, _, rfl⟩

theorem sourceSoundness {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty} {σ : DEnv}
    (hctx : InductiveCtxWF Δ ε) (htyped : HasType Δ ε e τ)
    (henv : EnvWF σ Δ ε) :
    StrongSourceSoundProp σ Δ ε e τ ∧ TypeDenotationForm σ τ ∧
    ∀ {e' τ'}, HasType Δ ε e' τ' → e.erase = e'.erase →
      denotTerm σ e = denotTerm σ e' ∧ denotTy σ τ = denotTy σ τ' := by
  refine ⟨Metatheory.sourceTermSoundness htyped hctx henv,
    typeDenotationForm σ τ, ?_⟩
  intro e' τ' htyped' herase
  obtain ⟨he, hτ⟩ := HasType.annotation_unique hctx htyped htyped' herase
  exact ⟨congrArg (denotTerm σ) he, congrArg (denotTy σ) hτ⟩

theorem innerProduct {σ : DEnv} {ε : NLCtx} {s : Space}
    (hctx : InductiveCtxWF ∅ ε) (henv : EnvWF σ ∅ ε)
    (hvalid : SValid ε s) (hfresh : IofFresh ε) :
    Nonempty (HasType ∅ ε (Space.iof s)
      (.space (.tprod (.dual s) (.dual s)))) ∧
    IsInnerProduct ((denotTerm σ (Space.iof s)).asLinMap
      (denotSpace σ s) (HSpace.dual (denotSpace σ s))) :=
  ⟨⟨Space.iof_hasType hfresh s hvalid⟩,
    Space.iof_denot_isInnerProduct hfresh henv hctx.toSourceContextWF.scoping hvalid⟩

end GLang.PaperSourceResults
