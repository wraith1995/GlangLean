import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLift
import GLang.Proofs.Progress.Certificates.RawCertifiedOperationalAdapter

/-!
# Exact-lift adapter for the certified ordinary semantics

This is the small public-facing package around the five-way structural lift.
-/

namespace GLang
namespace OperationalStrengthening

/-- The concrete certified semantics has an exact strengthened lift. -/
theorem rawCertified_exactLift : CheckedExactLift rawCertifiedSemantics := by
  rintro Δ Γ Ψ e b v ⟨τv, h⟩
  exact ⟨τv, h.toS⟩

/-- Term adequacy for a checked ordinary derivation.  The strengthened
derivation is the exact structural lift, hence the source term, selected
basis, produced value, and realized result type are all preserved literally. -/
theorem rawCertified_adequacy_term
    (orc : FFSOracleSem) (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hC : RawCertifiedOperational.C.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho ->
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) :=
  adequacy_term orc hspec hC.toS

/-- Change-of-basis adequacy for a checked ordinary COB derivation. -/
theorem rawCertified_adequacy_cob
    (orc : FFSOracleSem) (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (hC : RawCertifiedOperational.C.Cob Gamma Psi bSrc env bTgt) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho ->
      CobAgree orc sigma rho bSrc bTgt env :=
  adequacy_cob orc hspec hC.toS

/-- Exact-basis dimension adequacy for a checked ordinary type anchor. -/
theorem rawCertified_adequacy_dims
    (orc : FFSOracleSem) (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {tauV : ValTy}
    (hC : RawCertifiedOperational.C.TyAt Gamma Psi b tauV) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho ->
      AgreeDims orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) :=
  adequacy_dims orc hspec hC.toS

/-- A checked raw adequacy call therefore supplies a strengthened derivation
for its literal ordinary result. -/
theorem exactLift_rawCertifiedCall
    (call : CheckedRawAdequacyCall rawCertifiedSemantics
      orc rho Δ Γ Ψ Γv σ e b v) :
    ∃ τv, S.Term Δ Γ Ψ e b v τv :=
  exactLift_checkedCall rawCertifiedSemantics rawCertified_exactLift call

/-- End-to-end checked bridge: the certified trace lifts the caller's exact
ordinary result, and the raw adequacy theorem applies directly to
that same value. -/
theorem rawResult_of_rawCertifiedCall
    (call : CheckedRawAdequacyCall rawCertifiedSemantics
      orc rho Δ Γ Ψ Γv σ e b v) :
    ∃ τv,
      S.Term Δ Γ Ψ e b v τv ∧
      RawResultAgree orc σ rho [] [] [] (Basis.tof b) τv
        (denotBasis σ b) (denotTerm σ e)
        (denotValB_semS orc rho [] [] v) := by
  obtain ⟨τv, hS⟩ := exactLift_rawCertifiedCall call
  exact ⟨τv, hS,
    RawPublicCandidate.term orc call.raw.oracle hS σ Γv
      call.raw.consistent⟩

/-! ## Conditional end-to-end progress wiring

The only input intentionally left abstract here is the checked-progress
producer itself.  Once that theorem is proved, the following adapters show
that no further operational or adequacy bridge is missing. -/

/-- Checked progress turns a step-free raw adequacy call into a checked call at
the *same* result selected by progress.  Its ordinary `OpStep` component is
literal erasure of the checked derivation. -/
theorem checkedRawAdequacyCall_of_progress
    (hprogress : RawCertifiedProgress)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (htele : V2.CtxTele Delta Gamma Psi) :
    ∃ v, CheckedRawAdequacyCall rawCertifiedSemantics
      orc rho Delta Gamma Psi GammaV sigma e b v := by
  obtain ⟨htyped⟩ := call.typed
  have hplus := rawConsistent_evalCtxValidPlus_for_bridge call.consistent.raw
  obtain ⟨v, ⟨tauV, hchecked⟩⟩ := hprogress htele
    (rawConsistent_ctxWF_for_bridge call.consistent.raw)
    (rawConsistent_evalCtxValid_for_bridge call.consistent.raw)
    hplus.toEvalCtxLc
    (rawConsistent_evalCtxLamAnchored_for_bridge call.consistent.raw)
    (rawConsistent_typingImplyEval_for_bridge call.consistent.raw)
    htyped call.basisValid call.isTyBasis rfl
  exact ⟨v, {
    raw := {
      oracle := call.oracle
      consistent := call.consistent
      typed := call.typed
      basisValid := call.basisValid
      step := hchecked.erase }
    checked := ⟨tauV, hchecked⟩ }⟩

/-- Therefore a completed checked-progress proof gives an ordinary step, its
exact strengthened lift, and raw adequacy for one literal shared result. -/
theorem rawResult_of_rawCertifiedProgress
    (hprogress : RawCertifiedProgress)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (htele : V2.CtxTele Delta Gamma Psi) :
    ∃ v tauV,
      ValExpr.OpStep Psi e b v ∧
      S.Term Delta Gamma Psi e b v tauV ∧
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) := by
  obtain ⟨v, hcall⟩ := checkedRawAdequacyCall_of_progress hprogress call htele
  obtain ⟨tauV, hS, hagree⟩ := rawResult_of_rawCertifiedCall hcall
  exact ⟨v, tauV, hcall.erase_checked, hS, hagree⟩

end OperationalStrengthening
end GLang
