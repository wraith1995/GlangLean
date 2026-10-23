import GLang.Proofs.Adequacy.Partial.Source.PartialSourceHistory
import GLang.Proofs.Preservation.IndexedPreservation

/-! The adequacy induction uses the value typing already present in public
consistency. It supplies finite dimension-query dependencies for compiled
expressions; it is not an additional public premise. -/
namespace GLang.PartialAdequacy

structure TypedHistory (orc : PartialFFSOracleSem)
    (Δ : LCtx) (Γ : NLCtx) (Ψ : EvalCtx) (Γv : ValCtx)
    (σ : DEnv) (ρ : ValEnvSem) : Prop where
  history : History orc Δ Γ Ψ Γv σ ρ
  context : Operational.TypedContext Δ Γ Γv Ψ

instance : CoeOut (TypedHistory orc Δ Γ Ψ Γv σ ρ) (History orc Δ Γ Ψ Γv σ ρ) :=
  ⟨TypedHistory.history⟩

def Consistent.typedHistory (h : Consistent orc Δ Γ Ψ Γv σ ρ) :
    TypedHistory orc Δ Γ Ψ Γv σ ρ := ⟨h.history,h.context⟩

namespace TypedHistory
variable {orc : PartialFFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
  {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem}

/-- A compiled expression has finite dimension-query dependencies. -/
theorem exprFinite (h : TypedHistory orc Δ Γ Ψ Γv σ ρ)
    (he : ValExpr.OpStep Ψ e b v) : ValueQueryDependencies.Finite (.expr [] v) :=
  (RuntimeValue.validExpr_queryFinite h.context.evalContext.valid.some
    (RuntimeValue.preservation_mutual.2.2.2 he Γv h.context.evalContext).some).1

/-- A compiled space has finite dimension-query dependencies. -/
theorem spaceFinite (h : TypedHistory orc Δ Γ Ψ Γv σ ρ)
    (he : ValSpace.EvalS Ψ s sv) : ValueQueryDependencies.Finite (.space [] sv) :=
  RuntimeValue.validSpace_queryFinite h.context.evalContext.valid.some
    (RuntimeValue.preservation_mutual.1 he Γv h.context.evalContext).some

/-- A compiled type has finite dimension-query dependencies. -/
theorem typeFinite (h : TypedHistory orc Δ Γ Ψ Γv σ ρ)
    (he : ValTy.EvalT Ψ t tv) : ValueQueryDependencies.Finite (.type [] tv) :=
  RuntimeValue.validType_queryFinite h.context.evalContext.valid.some
    (RuntimeValue.preservation_mutual.2.1 he Γv h.context.evalContext).some

/-- A compiled conversion has finite dimension-query dependencies. -/
theorem cobFinite (h : TypedHistory orc Δ Γ Ψ Γv σ ρ)
    (he : Basis.EvalBB Ψ b v b') : ValueQueryDependencies.Finite (.expr [] v) :=
  (RuntimeValue.validExpr_queryFinite h.context.evalContext.valid.some
    (RuntimeValue.preservation_mutual.2.2.1 he Γv h.context.evalContext).some).1

/-- Reuse the existing semantic extension and extend its value typing in step. -/
theorem worldExtendNLAt (hirr : PartialDirectFv.OracleFresh orc) :
    WorldExtendNLAt orc (TypedHistory orc) := by
  intro Δ Γ0 Γ Ψ Γv σ ρ hc hle y hy b d hb hisTy hd a w ha hdim
  have hv := hc.context.evalContext
  have hdt := (RuntimeValue.preservation_mutual.2.1 hd.toEvalT Γv hv).some
  have hx : y ∉ Γv := fun hm => (hc.context.mem_iff y).mp hm |>.elim hy.1 hy.2.1
  refine ⟨History.worldExtendNLAt hirr hc.history hle hy hb hisTy hd a w ha hdim, ?_⟩
  have hb' := raw_basisValid_mono hb hle
  exact .extend_nlin hc.context ⟨hy.1,hy.2.1⟩
    { valid := {
        typeRealized := by simpa only [ValExpr.inferType] using hd.toEvalT
        valueScoped := by
          rw [EvalCtx.keyNames_extend_core]
          intro z hz
          simp only [ValExpr.fv,Finset.mem_insert] at hz ⊢
          exact hz.imp_right (fun hm => hd.fv_subset_keyNames hc.history.evalCtxScoped hm)
        locallyClosed := .var (evalT_lc hd.toEvalT hc.history.evalCtxLc) }
      frameAnchored := by intros b0 b1 t0 t1 body hb hv; cases hv }
    hb' ⟨hdt⟩ ⟨.var (by simp)⟩

abbrev evalCtxLc (h : TypedHistory orc Δ Γ Ψ Γv σ ρ) := h.history.evalCtxLc
abbrev evalCtxScoped (h : TypedHistory orc Δ Γ Ψ Γv σ ρ) := h.history.evalCtxScoped
abbrev evalCtxValidPlus (h : TypedHistory orc Δ Γ Ψ Γv σ ρ) := h.history.evalCtxValidPlus
abbrev ctxWF_nl (h : TypedHistory orc Δ Γ Ψ Γv σ ρ) := h.history.ctxWF_nl
abbrev envWF_nl (h : TypedHistory orc Δ Γ Ψ Γv σ ρ) := h.history.envWF_nl
abbrev ctxTele (h : TypedHistory orc Δ Γ Ψ Γv σ ρ) := h.history.ctxTele
abbrev lookup (h : TypedHistory orc Δ Γ Ψ Γv σ ρ) {x : VName} {b : Basis}
    (hm : (x,b) ∈ Ψ) := h.history.lookup hm

end TypedHistory
end GLang.PartialAdequacy
