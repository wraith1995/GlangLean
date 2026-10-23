import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedDepthTransportLocal
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedDepthStdTySide
import GLang.Proofs.Progress.Certificates.RawCertifiedLocalizedCallCertificate
import GLang.Proofs.Progress.Certificates.RawCertifiedCallProgress
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLiftAdapter

/-! Finite-depth checked progress. At layer `n`, local change of basis gives exact
checked types for the basis selected at a variable leaf and builds its standard
endpoint. Source progress at `n` supplies the source-evaluating basis cases at `n+1`. -/

set_option maxHeartbeats 3200000
set_option maxRecDepth 6000

namespace GLang
namespace RawCertifiedDepthAssemblyLocal

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedSelectedProgressMaster
open RawCertifiedCobDepthLayerSpike
open RawCertifiedDepthExact
open RawCertifiedDepthExactLocal
open RawCertifiedDepthTransportLocal
open RawCertifiedDepthStdTySide
open RawCertifiedLocalizedCallCertificate
open RawCertifiedCallProgress

/-- Source progress at one depth, uniformly in the chosen root evaluator.
The root's checked storage invariant is the only evaluator-level input. -/
def CheckedTermProgressDepthAllLocal (n : Nat) : Prop :=
  forall (Psi0 : EvalCtx), V2.StoredWF Psi0 ->
    RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n

/-- The local two-sided transport specializes to the source-to-standard
service consumed by the variable handlers.  The target certificate is
derived from the source certificate itself. -/
theorem checkedBasisToStdDepth_of_allCob_local
    (n : Nat) (hcob : CheckedCobToStdDepthAll n)
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0),
      CheckedBasisToStdDepth Psi0 n := by
  intro Psi0 hrootStored Delta Gamma Psi e b v tauv hb hfuture side
    hP hcov hstored hwf hterm
  have hi : Basis.IsTyBasis b := hterm.tyAt.isTyBasis
  obtain ⟨hbStd, sideStd⟩ := checkedStdTySideDepth side hi
  exact checkedTermTransportDepth_local n hcob laws happCut
    Psi0 hrootStored Delta Gamma Psi e b
    (Basis.std (Basis.tof b)) v tauv hb side hbStd sideStd
    hfuture hP hcov hstored hwf hi (Basis.isTyBasis_std _)
    (Basis.tof_std _) hterm

theorem checkedTermProgressDepthAllLocal_zero
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    CheckedTermProgressDepthAllLocal 0 := by
  intro Psi0 _hrootStored
  exact checked_term_progress_depth_zero laws happCut Psi0

theorem checkedCobToStdDepthAllLocal_zero :
    CheckedCobToStdDepthAll 0 := by
  intro Psi0 _hrootStored
  exact checkedCobToStdDepth_zero Psi0

/-- One supply-free simultaneous step. -/
theorem checkedDepthPairLocal_step
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (n : Nat)
    (hterm : CheckedTermProgressDepthAllLocal n)
    (hcob : CheckedCobToStdDepthAll n) :
    CheckedTermProgressDepthAllLocal (n + 1) /\
      CheckedCobToStdDepthAll (n + 1) := by
  constructor
  · intro Psi0 hrootStored
    exact checked_term_progress_depth_succ laws happCut Psi0 n
      hrootStored
      (checkedExactBasisTyProgressDepth_of_allCob_local
        n hcob laws Psi0 hrootStored)
      (checkedBasisToStdDepth_of_allCob_local
        n hcob laws happCut Psi0 hrootStored)
  · intro Psi0 hrootStored
    exact checkedCobToStdDepth_succ_of_termProgress
      (hterm Psi0 hrootStored)

/-- All finite layers, with no global basis supply. -/
theorem checkedDepthPairLocal_all
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    forall n, CheckedTermProgressDepthAllLocal n /\
      CheckedCobToStdDepthAll n := by
  intro n
  induction n with
  | zero =>
      exact ⟨checkedTermProgressDepthAllLocal_zero laws happCut,
        checkedCobToStdDepthAllLocal_zero⟩
  | succ n ih =>
      exact checkedDepthPairLocal_step laws happCut n ih.1 ih.2

/-- Local services obtained from finite-depth progress. -/
theorem checkedLocalDepthServices_of_rules
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0) :
    CheckedLocalDepthServices Psi0 where
  exact n :=
    checkedExactBasisTyProgressDepth_of_allCob_local n
      (checkedDepthPairLocal_all laws happCut n).2 laws
      Psi0 hrootStored
  toStd n :=
    checkedBasisToStdDepth_of_allCob_local n
      (checkedDepthPairLocal_all laws happCut n).2 laws happCut
      Psi0 hrootStored

/-- A finite source-side certificate can always be executed at its chosen
depth. -/
theorem checkedStdTerm_of_finiteSide
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    {Psi0 : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {e : Term} {tau : Ty} {ht : HasType Delta Gamma e tau}
    (hside : CheckedLocalSideBasesFinite Psi0 ht)
    (hP : V2.PCarrier Psi0) (hcov : V2.VarsCovered Delta Gamma Psi0)
    (hstored : V2.StoredWF Psi0) (hwf : V2.CtxWF' Delta Gamma) :
    exists v tauv,
      C.Term Delta Gamma Psi0 e (Basis.std tau) v tauv := by
  obtain ⟨n, ⟨side⟩⟩ := hside
  exact (checkedDepthPairLocal_all laws happCut n).1 Psi0 hstored
    ht side Psi0 (CheckedStdFuture.refl Psi0) hP hcov hwf

/-- Purely operational call-local checked progress at the requested basis. -/
theorem checked_progress_localFinite
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis}
    (ht : HasType Delta Gamma e (Basis.tof b))
    (hb : Basis.BasisValid Gamma b)
    (hisTy : Basis.IsTyBasis b)
    (cert : CheckedLocalCallFinite Psi ht hb)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered Delta Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' Delta Gamma) :
    exists v tauv, C.Term Delta Gamma Psi e b v tauv := by
  obtain ⟨vStd, tauVStd, hStd⟩ :=
    checkedStdTerm_of_finiteSide laws happCut cert.termSide
      hP hcov hstored hwf
  obtain ⟨n, sideRequested⟩ := cert.requestedSide
  obtain ⟨hbStd, sideStd⟩ :=
    checkedStdTySideDepth sideRequested hisTy
  exact checkedTermTransportDepth_local n
    (checkedDepthPairLocal_all laws happCut n).2 laws happCut
    Psi hstored Delta Gamma Psi e (Basis.std (Basis.tof b)) b
    vStd tauVStd hbStd sideStd hb sideRequested
    (CheckedStdFuture.refl Psi) hP hcov.drop_lin hstored hwf
    (Basis.isTyBasis_std _) hisTy
    (Basis.tof_std _).symm hStd

/-- Semantic-call adapter for the purely operational checked-progress core.
Raw consistency is used only here to recover the four operational environment
invariants; the core theorem above is independent of the oracle. -/
theorem checked_progress_of_rawProgressCall_localFinite
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (cert : CheckedLocalCallFinite Psi ht call.basisValid) :
    exists v tauv, C.Term Delta Gamma Psi e b v tauv :=
  checked_progress_localFinite laws happCut ht call.basisValid call.isTyBasis cert
    (rawConsistent_pCarrier call.consistent.raw)
    (V2.varsCovered_of
      (rawConsistent_typingImplyEval_for_bridge call.consistent.raw))
    call.consistent.raw.storedWF
    (rawConsistent_ctxWF_for_bridge call.consistent.raw)

/-- End-to-end call-local result.  All four views refer to the literal same
value selected by the checked derivation. -/
theorem ordinary_strengthened_and_adequate_of_localFinite
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (cert : CheckedLocalCallFinite Psi ht call.basisValid) :
    exists v tauv,
      C.Term Delta Gamma Psi e b v tauv /\
      ValExpr.OpStep Psi e b v /\
      S.Term Delta Gamma Psi e b v tauv /\
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) := by
  obtain ⟨v, tauv, hchecked⟩ :=
    checked_progress_of_rawProgressCall_localFinite laws happCut call ht cert
  exact ⟨v, tauv, hchecked, hchecked.erase, hchecked.toS,
    OperationalStrengthening.rawCertified_adequacy_term
      orc call.oracle hchecked sigma GammaV call.consistent⟩

end RawCertifiedDepthAssemblyLocal
end GLang
