import GLang.Proofs.Progress.Certificates.RawCertifiedOperationalAdapter
import GLang.Proofs.Progress.Supporting.Progress

namespace GLang
namespace RawCertifiedProgressScratch

open OperationalStrengthening
open RawCertifiedOperational

/-- The explicit-index form of the concrete checked-progress target. -/
def CertifiedProgress : Prop :=
  ∀ {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx}
    {e : Term} {τ : Ty} {b : Basis},
    V2.CtxTele Δ Γ Ψ →
    V2.CtxWF' Δ Γ →
    V2.EvalCtxValid Ψ →
    EvalCtxLc Ψ →
    V2.EvalCtxLamAnchored Ψ →
    V2.TypingImplyEval Δ Γ Ψ →
    HasType Δ Γ e τ →
    Basis.BasisValid Γ b →
    Basis.IsTyBasis b →
    Basis.tof b = τ →
    ∃ v τv, C.Term Δ Γ Ψ e b v τv

/-- Hiding the realized result index gives exactly the preservation-facing
checked-progress interface. -/
theorem certifiedProgress_iff_interface :
    CertifiedProgress ↔ OperationalStrengthening.RawCertifiedProgress := by
  rfl

/-- Progress at the standard basis with the hereditary checked tree retained.
This is the natural term entry point of a parallel mutual induction. -/
def CertifiedStdProgress : Prop :=
  ∀ {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty},
    V2.CtxWF' Δ Γ →
    V2.EvalCtxValid Ψ →
    EvalCtxLc Ψ →
    V2.EvalCtxLamAnchored Ψ →
    V2.TypingImplyEval Δ Γ Ψ →
    V2.StdComplete Ψ →
    HasType Δ Γ e τ →
    ∃ v τv, C.Term Δ Γ Ψ e (Basis.std τ) v τv

/-- Certified standard progress conservatively projects to the existing
`progress_std` conclusion without changing the produced value. -/
theorem CertifiedStdProgress.toOrdinary
    (hprogress : CertifiedStdProgress)
    {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty}
    (hwfΔΓ : V2.CtxWF' Δ Γ)
    (hwfΨ : V2.EvalCtxValid Ψ)
    (hwflc : EvalCtxLc Ψ)
    (hanch : V2.EvalCtxLamAnchored Ψ)
    (hΓΨ : V2.TypingImplyEval Δ Γ Ψ)
    (hstd : V2.StdComplete Ψ)
    (htype : HasType Δ Γ e τ) :
    ∃ v, ValExpr.OpStep Ψ e (Basis.std τ) v := by
  obtain ⟨v, τv, hv⟩ :=
    hprogress hwfΔΓ hwfΨ hwflc hanch hΓΨ hstd htype
  exact ⟨v, hv.erase⟩

/-- The extra theorem one would have to add in order to reuse the *result* of
ordinary progress.  It is intentionally stated separately: this is not a
weakening or typing lemma, but reconstruction of the entire hereditary
checked derivation from an erased operational tree. -/
def OrdinaryTraceCompletion : Prop :=
  ∀ {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx}
    {e : Term} {τ : Ty} {b : Basis} {v : ValExpr},
    V2.CtxTele Δ Γ Ψ →
    V2.CtxWF' Δ Γ →
    V2.EvalCtxValid Ψ →
    EvalCtxLc Ψ →
    V2.EvalCtxLamAnchored Ψ →
    V2.TypingImplyEval Δ Γ Ψ →
    HasType Δ Γ e τ →
    Basis.BasisValid Γ b →
    Basis.IsTyBasis b →
    Basis.tof b = τ →
    ValExpr.OpStep Ψ e b v →
    ∃ τv, C.Term Δ Γ Ψ e b v τv

/-- Existing ordinary progress can be reused exactly when supplied with the
missing checked-tree completion theorem. -/
theorem certifiedProgress_of_ordinaryTraceCompletion
    (hcomplete : OrdinaryTraceCompletion) : CertifiedProgress := by
  intro Ψ Δ Γ e τ b htele hwfΔΓ hwfΨ hwflc hanch hΓΨ htype hb hsb htof
  obtain ⟨v, hv⟩ :=
    V2.progress htele hwfΔΓ hwfΨ hwflc hanch hΓΨ htype hb hsb htof
  obtain ⟨τv, hchecked⟩ :=
    hcomplete htele hwfΔΓ hwfΨ hwflc hanch hΓΨ htype hb hsb htof hv
  exact ⟨v, τv, hchecked⟩

def cMotiveS (Γ : NLCtx) (s : Space) : Prop :=
  ∀ Ψ : EvalCtx, V2.PCarrier Ψ → V2.VarsCovered ∅ Γ Ψ →
    ∃ sv, C.Space Γ Ψ s sv

def cMotiveT (Γ : NLCtx) (τ : Ty) : Prop :=
  ∀ Ψ : EvalCtx, V2.PCarrier Ψ → V2.VarsCovered ∅ Γ Ψ →
    ∃ τv, C.Ty Γ Ψ τ τv ∧ C.TyAt Γ Ψ (Basis.std τ) τv

def cMotiveSub (Γ : NLCtx) (s₀ s₁ : Space) : Prop :=
  ∀ Ψ : EvalCtx, V2.PCarrier Ψ → V2.VarsCovered ∅ Γ Ψ →
    ∃ v τv, C.Term ∅ Γ Ψ (.embed s₀)
      (Basis.std (.space (.tprod (.dual s₀) s₁))) v τv

/-- A standard-basis checked term already retains its exact realized type.
The separate `StdPiAnchored` tail used by ordinary progress is therefore not
part of this motive; `tyAt_stdAnchored` below recovers it structurally. -/
def cMotiveH (Δ : LCtx) (Γ : NLCtx) (e : Term) (τ : Ty) : Prop :=
  ∀ Ψ : EvalCtx, V2.PCarrier Ψ → V2.VarsCovered Δ Γ Ψ →
    ∃ v τv, C.Term Δ Γ Ψ e (Basis.std τ) v τv

/-- Checked space progress forgets to the existing space-progress motive. -/
theorem cMotiveS.toOrdinary
    (h : cMotiveS Γ s) : V2.pMotiveS Γ s := by
  intro Ψ hP hcov
  obtain ⟨sv, hsv⟩ := h Ψ hP hcov
  exact ⟨sv, hsv.erase⟩

/-- Checked type progress forgets to the existential half of the existing
type-progress motive. -/
theorem cMotiveT.toEvalT
    (h : cMotiveT Γ τ) (Ψ : EvalCtx)
    (hP : V2.PCarrier Ψ) (hcov : V2.VarsCovered ∅ Γ Ψ) :
    ∃ τv, ValTy.EvalT Ψ τ τv := by
  obtain ⟨τv, hτv, _⟩ := h Ψ hP hcov
  exact ⟨τv, hτv.erase⟩

/-- Checked subtype progress forgets to the existing subtype-progress
motive, with the exact same produced value. -/
theorem cMotiveSub.toOrdinary
    (h : cMotiveSub Γ s₀ s₁) : V2.pMotiveSub Γ s₀ s₁ := by
  intro Ψ hP hcov
  obtain ⟨v, τv, hv⟩ := h Ψ hP hcov
  exact ⟨v, hv.erase⟩

/-- The ordinary operational half of the existing term motive follows by
literal erasure. -/
theorem cMotiveH.toOpStep
    (h : cMotiveH Δ Γ e τ) (Ψ : EvalCtx)
    (hP : V2.PCarrier Ψ) (hcov : V2.VarsCovered Δ Γ Ψ) :
    ∃ v, ValExpr.OpStep Ψ e (Basis.std τ) v := by
  obtain ⟨v, τv, hv⟩ := h Ψ hP hcov
  exact ⟨v, hv.erase⟩

end RawCertifiedProgressScratch
end GLang
