import GLang.Proofs.Preservation.Context
import GLang.Proofs.Adequacy.Raw.Context.RawConsistent
import GLang.Proofs.Value.Runtime.RuntimeValueQueryFinite
import GLang.Proofs.Preservation.IndexedPreservation

namespace GLang

structure RawTypedConsistent (orc : FFSOracleSem)
    (Δ : LCtx) (Γ : NLCtx) (Ψ : EvalCtx) (Γv : ValCtx)
    (σ : DEnv) (ρ : ValEnvSem) : Prop where
  raw : RawConsistent orc Δ Γ Ψ Γv σ ρ
  context : Operational.TypedContext Δ Γ Γv Ψ

instance : CoeOut (RawTypedConsistent orc Δ Γ Ψ Γv σ ρ) (RawConsistent orc Δ Γ Ψ Γv σ ρ) :=
  ⟨RawTypedConsistent.raw⟩

/-- Total-evaluator consistency includes the value context used to certify queries. -/
abbrev Consistent := RawTypedConsistent

namespace RawTypedConsistent
variable {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
  {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem}

/-- A compiled expression has finite dimension-query dependencies. -/
theorem exprFinite (h : RawTypedConsistent orc Δ Γ Ψ Γv σ ρ)
    (he : ValExpr.OpStep Ψ e b v) : ValueQueryDependencies.Finite (.expr [] v) :=
  (RuntimeValue.validExpr_queryFinite h.context.evalContext.valid.some
    (RuntimeValue.preservation_mutual.2.2.2 he Γv h.context.evalContext).some).1

/-- A compiled space has finite dimension-query dependencies. -/
theorem spaceFinite (h : RawTypedConsistent orc Δ Γ Ψ Γv σ ρ)
    (he : ValSpace.EvalS Ψ s sv) : ValueQueryDependencies.Finite (.space [] sv) :=
  RuntimeValue.validSpace_queryFinite h.context.evalContext.valid.some
    (RuntimeValue.preservation_mutual.1 he Γv h.context.evalContext).some

/-- A compiled type has finite dimension-query dependencies. -/
theorem typeFinite (h : RawTypedConsistent orc Δ Γ Ψ Γv σ ρ)
    (he : ValTy.EvalT Ψ t tv) : ValueQueryDependencies.Finite (.type [] tv) :=
  RuntimeValue.validType_queryFinite h.context.evalContext.valid.some
    (RuntimeValue.preservation_mutual.2.1 he Γv h.context.evalContext).some

/-- A compiled conversion has finite dimension-query dependencies. -/
theorem cobFinite (h : RawTypedConsistent orc Δ Γ Ψ Γv σ ρ)
    (he : Basis.EvalBB Ψ b v b') : ValueQueryDependencies.Finite (.expr [] v) :=
  (RuntimeValue.validExpr_queryFinite h.context.evalContext.valid.some
    (RuntimeValue.preservation_mutual.2.2.1 he Γv h.context.evalContext).some).1

/-- Reuse the existing semantic extension and extend its value typing in step. -/
theorem worldExtendNLAt (hirr : OracleFvIrrel orc) :
    RawWorldExtendNLAt orc (RawTypedConsistent orc) := by
  intro Δ Γ0 Γ Ψ Γv σ ρ hc hle y hy b d hb hisTy hd a w ha hdim
  have hv := hc.context.evalContext
  have hdt := (RuntimeValue.preservation_mutual.2.1 hd.toEvalT Γv hv).some
  have hx : y ∉ Γv := fun hm => (hc.context.mem_iff y).mp hm |>.elim hy.1 hy.2.1
  refine ⟨rawConsistent_worldExtendNLAt hirr hc.raw hle hy hb hisTy hd a w ha hdim, ?_⟩
  have hb' := raw_basisValid_mono hb hle
  exact .extend_nlin hc.context ⟨hy.1,hy.2.1⟩
    { valid := {
        typeRealized := by simpa only [ValExpr.inferType] using hd.toEvalT
        valueScoped := by
          rw [EvalCtx.keyNames_extend_core]
          intro z hz
          simp only [ValExpr.fv,Finset.mem_insert] at hz ⊢
          exact hz.imp_right (fun hm => hd.fv_subset_keyNames hc.raw.evalCtxScoped hm)
        locallyClosed := .var (evalT_lc hd.toEvalT hc.raw.evalCtxLc) }
      frameAnchored := by intros b0 b1 t0 t1 body hb hv; cases hv }
    hb' ⟨hdt⟩ ⟨.var (by simp)⟩

abbrev evalCtxLc (h : RawTypedConsistent orc Δ Γ Ψ Γv σ ρ) := h.raw.evalCtxLc
abbrev evalCtxScoped (h : RawTypedConsistent orc Δ Γ Ψ Γv σ ρ) := h.raw.evalCtxScoped
abbrev evalCtxValidPlus (h : RawTypedConsistent orc Δ Γ Ψ Γv σ ρ) := h.raw.evalCtxValidPlus
abbrev ctxWF_nl (h : RawTypedConsistent orc Δ Γ Ψ Γv σ ρ) := h.raw.ctxWF_nl
abbrev envWF_nl (h : RawTypedConsistent orc Δ Γ Ψ Γv σ ρ) := h.raw.envWF_nl
abbrev ctxTele (h : RawTypedConsistent orc Δ Γ Ψ Γv σ ρ) := h.context.erase

end RawTypedConsistent
end GLang
