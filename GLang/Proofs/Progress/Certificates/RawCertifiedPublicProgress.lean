import GLang.Proofs.Progress.Certificates.RawCertifiedCallProgress
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLiftAdapter
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedDepthAssemblyLocal
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairProgress
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardNatProgress
import GLang.Proofs.Progress.Certificates.RawCertifiedProgressBoundaries
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedCtxTeleProgress

namespace GLang
namespace RawCertifiedPublicProgress

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedPiBasisTransport
open RawCertifiedCallProgress
open RawCertifiedDepthAssemblyLocal
open RawCertifiedLocalizedCallCertificate
open RawCertifiedPairCertificate
open RawCertifiedPairProgress
open RawCertifiedPairFreeStandardNatProgress
open RawCertifiedProgressBoundaries
open RawCertifiedCtxTeleProgress

/-- Adequacy-scoped checked progress from the current raw environment. -/
theorem checked_progress_of_mutualInputs
    (laws : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    (hexact : CheckedExactBasisTyProgress)
    (htransport : CheckedBasisTransportWF)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (hside : CheckedLocalSideBases Psi ht) :
    exists v tauv, C.Term Delta Gamma Psi e b v tauv :=
  checked_progress_of_rawProgressCall laws happCut hexact htransport
    call ht hside

theorem checked_progress_of_cob
    (laws : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    (hcob : CheckedCobToStd)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (hside : CheckedLocalSideBases Psi ht) :
    exists v tauv, C.Term Delta Gamma Psi e b v tauv :=
  checked_progress_of_rawProgressCall_of_cob laws happCut hcob
    call ht hside

/-- The checked result selected above is already an ordinary result, an exact
strengthened result, and an adequate denotational result.  No equality between
separately evaluated values is used. -/
theorem rawResult_of_checked_progress_of_mutualInputs
    (laws : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    (hexact : CheckedExactBasisTyProgress)
    (htransport : CheckedBasisTransportWF)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (hside : CheckedLocalSideBases Psi ht) :
    exists v tauv,
      C.Term Delta Gamma Psi e b v tauv /\
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) := by
  obtain ⟨v, tauv, hchecked⟩ :=
    checked_progress_of_mutualInputs laws happCut hexact htransport
      call ht hside
  exact ⟨v, tauv, hchecked,
    rawCertified_adequacy_term orc call.oracle hchecked
      sigma GammaV call.consistent⟩

/-- End-to-end adequacy factored through the one remaining checked COB input. -/
theorem rawResult_of_checked_progress_of_cob
    (laws : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    (hcob : CheckedCobToStd)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (hside : CheckedLocalSideBases Psi ht) :
    exists v tauv,
      C.Term Delta Gamma Psi e b v tauv /\
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) := by
  obtain ⟨v, tauv, hchecked⟩ :=
    checked_progress_of_cob laws happCut hcob call ht hside
  exact ⟨v, tauv, hchecked,
    rawCertified_adequacy_term orc call.oracle hchecked
      sigma GammaV call.consistent⟩

theorem ordinary_strengthened_and_adequate_of_mutualInputs
    (laws : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    (hexact : CheckedExactBasisTyProgress)
    (htransport : CheckedBasisTransportWF)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (hside : CheckedLocalSideBases Psi ht) :
    exists v tauv,
      ValExpr.OpStep Psi e b v /\
      S.Term Delta Gamma Psi e b v tauv /\
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) := by
  obtain ⟨v, tauv, hchecked, hagree⟩ :=
    rawResult_of_checked_progress_of_mutualInputs
      laws happCut hexact htransport call ht hside
  exact ⟨v, tauv, hchecked.erase, hchecked.toS, hagree⟩

/-! ## Supply-free public entry points -/

theorem checked_progress
    (history : V2.CtxTele Delta Gamma Psi)
    (typed : HasType Delta Gamma e (Basis.tof b))
    (basisValid : Basis.BasisValid Gamma b) :
    exists v tauV, C.Term Delta Gamma Psi e b v tauV :=
  RawCertifiedCtxTeleProgress.checkedProgress history typed basisValid

/-- Raw consistency contains the same semantic-free creation history, so it
also supplies canonical checked progress.  Oracle and denotational fields are
discarded before the operational proof begins. -/
theorem checked_progress_of_rawConsistent
    (consistent : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (typed : HasType Delta Gamma e (Basis.tof b))
    (basisValid : Basis.BasisValid Gamma b) :
    exists v tauV, C.Term Delta Gamma Psi e b v tauV :=
  checked_progress
    (RawCertifiedCtxTele.RawConsistent.ctxTele consistent)
    typed basisValid

/-- Pure ordinary progress under exactly its operational assumptions.  This
theorem has no oracle, denotational environment, consistency relation, or
hereditary exact-type certificate. -/
theorem ordinary_progress
    (call : OrdinaryProgressCall Delta Gamma Psi e b) :
    exists v, ValExpr.OpStep Psi e b v :=
  RawCertifiedCallProgress.ordinary_progress call

/-- A semantic raw call supplies the smaller operational progress boundary.
This adapter is useful inside soundness, but is not the public progress
contract. -/
theorem ordinary_progress_of_rawCall
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b) :
    exists v, ValExpr.OpStep Psi e b v :=
  RawCertifiedCallProgress.ordinary_progress_of_rawProgressCall call

/-! ## Root-only checked-progress boundary -/

/-- Public spelling of the root-only result-basis boundary.  Recursive
construction details remain below this composition layer. -/
abbrev CheckedRootBasisBoundary :=
  RawCertifiedPairFreeStandardNatProgress.CheckedRootBasisBoundary

/-- Checked progress at the literal standard result basis.  Raw consistency
constructs the initial-entry evidence and all internal standard-basis work. -/
theorem checked_progress_standard_of_rawConsistent
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv}
    {e : Term} {tau : Ty}
    (hconsistent :
      RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (ht : HasType Delta Gamma e tau) :
    exists v tauV, C.Term Delta Gamma Psi e (Basis.std tau) v tauV :=
  RawCertifiedCtxTeleProgress.checkedProgressStandard
    (RawCertifiedCtxTele.RawConsistent.ctxTele hconsistent) ht

/-- Boundary-only checked progress at the requested root basis. -/
theorem checked_progress_of_rawConsistent_boundary
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv}
    {e : Term} {requested : Basis}
    (hconsistent :
      RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (ht : HasType Delta Gamma e (Basis.tof requested))
    (root : CheckedRootBasisBoundary Gamma Psi requested) :
    exists v tauV, C.Term Delta Gamma Psi e requested v tauV := by
  let history := RawCertifiedCtxTele.RawConsistent.ctxTele hconsistent
  obtain ⟨v, tauV, hstd⟩ :=
    RawCertifiedCtxTeleProgress.checkedProgressStandard history ht
  exact root.reanchor
    (RawCertifiedCtxTeleProgress.ctxWFPrime history) hstd

/-- A literal standard basis needs no transport: its root boundary is
reflexive. -/
theorem checkedRootBasisBoundary_standard
    {Gamma : NLCtx} {Psi : EvalCtx} {tau : Ty} {k : Kind}
    (htau : TValid Gamma tau k) :
    CheckedRootBasisBoundary Gamma Psi (Basis.std tau) :=
  RawCertifiedPairFreeStandardNatProgress.checkedRootBasisBoundary_standard
    htau

/-- Construct the root boundary from one unary requested-basis certificate
and the ordinary operational invariants at the root evaluator. -/
theorem checkedRootBasisBoundary_of_localSide
    {Gamma : NLCtx} {Psi : EvalCtx} {requested : Basis}
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hrequested : Basis.BasisValid Gamma requested)
    (sideFinite :
      RawCertifiedCobProgressMutualSpike.CheckedLocalSideBasisFinite
        Psi hrequested) :
    CheckedRootBasisBoundary Gamma Psi requested :=
  RawCertifiedPairFreeStandardNatProgress.checkedRootBasisBoundary_of_localSide
    hP hcov hstored hrequested sideFinite

/-- Progress from a recursive finite-pair root certificate. -/
theorem checkedRootBasisBoundary_of_pair_compat
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv}
    {requested : Basis}
    (hconsistent :
      RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (hrequested : Basis.BasisValid Gamma requested)
    (requestedPair : CheckedPairBasisFinite Psi Gamma
      (Basis.std (Basis.tof requested)) requested) :
    CheckedRootBasisBoundary Gamma Psi requested := by
  clear requestedPair
  exact RawCertifiedCtxTeleProgress.checkedRootBasisBoundary
    (RawCertifiedCtxTele.RawConsistent.ctxTele hconsistent) hrequested

theorem checked_progress_uniform
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (cert : CheckedLocalCallFinite Psi ht call.basisValid) :
    exists v tauv, C.Term Delta Gamma Psi e b v tauv :=
  checked_progress_of_rawProgressCall_localFinite
    RawCertifiedOperational.RenameProof.checkedRenameLaws
      RawCertifiedOperational.checkedTyAtAppCut call ht cert

/-- Canonical checked progress under unary judgment-local evidence.  The
certificate may select a proof-relevant typing derivation of the same source
judgment as the caller. -/
theorem checked_progress_localCertificate
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (cert : CheckedJudgmentLocalCallFinite Psi ht call.basisValid) :
    exists v tauv, C.Term Delta Gamma Psi e b v tauv := by
  obtain ⟨ht', localCert⟩ := cert
  exact checked_progress_of_rawProgressCall_localFinite
    RawCertifiedOperational.RenameProof.checkedRenameLaws
    RawCertifiedOperational.checkedTyAtAppCut call ht' localCert

/-- Checked progress from a recursive pair-local certificate. -/
theorem checked_progress_pairLocal_compat
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (cert : CheckedPairLocalCallFinite Psi ht b) :
    exists v tauv, C.Term Delta Gamma Psi e b v tauv :=
  checked_progress_pairLocalFinite
    RawCertifiedOperational.RenameProof.checkedRenameLaws
    RawCertifiedOperational.checkedTyAtAppCut ht call.basisValid cert
    (rawConsistent_pCarrier call.consistent.raw)
    (V2.varsCovered_of
      (rawConsistent_typingImplyEval_for_bridge call.consistent.raw))
    call.consistent.raw.storedWF
    (rawConsistent_ctxWF_for_bridge call.consistent.raw)

theorem ordinary_checked_strengthened_and_adequate_uniform
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (cert : CheckedLocalCallFinite Psi ht call.basisValid) :
    exists v tauv,
      C.Term Delta Gamma Psi e b v tauv /\
      ValExpr.OpStep Psi e b v /\
      S.Term Delta Gamma Psi e b v tauv /\
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) :=
  ordinary_strengthened_and_adequate_of_localFinite
    RawCertifiedOperational.RenameProof.checkedRenameLaws
      RawCertifiedOperational.checkedTyAtAppCut call ht cert

/-- End-to-end checked progress and raw adequacy through unary
judgment-local evidence.  All operational and denotational views name the
same produced value. -/
theorem ordinary_checked_strengthened_and_adequate
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (cert : CheckedJudgmentLocalCallFinite Psi ht call.basisValid) :
    exists v tauv,
      C.Term Delta Gamma Psi e b v tauv /\
      ValExpr.OpStep Psi e b v /\
      S.Term Delta Gamma Psi e b v tauv /\
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) := by
  obtain ⟨v, tauv, hchecked⟩ :=
    checked_progress_localCertificate call ht cert
  exact ⟨v, tauv, hchecked, hchecked.erase, hchecked.toS,
    rawCertified_adequacy_term orc call.oracle hchecked
      sigma GammaV call.consistent⟩

/-- Combined progress and adequacy from a recursive pair-local certificate. -/
theorem ordinary_checked_strengthened_and_adequate_pairLocal_compat
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (cert : CheckedPairLocalCallFinite Psi ht b) :
    exists v tauv,
      C.Term Delta Gamma Psi e b v tauv /\
      ValExpr.OpStep Psi e b v /\
      S.Term Delta Gamma Psi e b v tauv /\
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) := by
  obtain ⟨v, tauv, hchecked⟩ :=
    checked_progress_pairLocal_compat call ht cert
  exact ⟨v, tauv, hchecked, hchecked.erase, hchecked.toS,
    rawCertified_adequacy_term orc call.oracle hchecked
      sigma GammaV call.consistent⟩

end RawCertifiedPublicProgress
end GLang
