import GLang.Proofs.Progress.Certificates.RawCertifiedSelectedProgressMaster

/-! Depth-ranked, call-local checked-progress certificates. Dependent-frame callbacks range over admissible evaluator extensions and argument bases. Variable leaves retain their source contexts and type-aligned keys. -/

namespace GLang
namespace RawCertifiedLocalizedCallCertificate

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedSelectedProgressMaster

/-- The depth-ranked syntactic evidence attached to one progress call. Its two
roots are the chosen typing derivation and requested basis.  Frame descendants
retain their locally correlated hereditary callback; there is no global
`forall Psi b` basis-supply field. This evidence is an explicit local
admissibility premise. It is not implied by `RawConsistent`: promotion may
remove a name from a variable leaf's nonlinear context while that variable's
stored basis still mentions the name only in its representation.  The
`RawPromotionLocalFiniteCounterexampleScratch` regression gives an
`IsTyBasis` example. -/
structure CheckedLocalCallFinite
    (Psi0 : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {b : Basis}
    (ht : HasType Delta Gamma e tau)
    (hb : Basis.BasisValid Gamma b) : Prop where
  termSide : CheckedLocalSideBasesFinite Psi0 ht
  requestedSide : CheckedLocalSideBasisFinite Psi0 hb

/-- Judgment-level unary checked-progress evidence. -/
def CheckedJudgmentLocalCallFinite
    (Psi0 : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (_ht : HasType Delta Gamma e tau)
    {b : Basis}
    (hb : Basis.BasisValid Gamma b) : Prop :=
  exists ht' : HasType Delta Gamma e tau,
    CheckedLocalCallFinite Psi0 ht' hb

/-- Internal semantic seam, separated from the syntactic call certificate.
The Nat mutual assembly is responsible for constructing this family; it is
not intended to remain a premise of the public endpoint. -/
structure CheckedLocalDepthServices (Psi0 : EvalCtx) : Prop where
  exact : forall n, CheckedExactBasisTyProgressDepth Psi0 n
  toStd : forall n, CheckedBasisToStdDepth Psi0 n

/-- The chosen requested basis receives an exact checked type from its own
finite-rank certificate; no unrelated valid basis is quantified by the call. -/
theorem checkedExactRequested_of_localFinite
    {Psi0 : EvalCtx}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {b : Basis}
    {ht : HasType Delta Gamma e tau}
    {hb : Basis.BasisValid Gamma b}
    (cert : CheckedLocalCallFinite Psi0 ht hb)
    (services : CheckedLocalDepthServices Psi0)
    (hP : V2.PCarrier Psi0)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi0)
    (hstored : V2.StoredWF Psi0)
    (hwf : V2.CtxWF' Delta Gamma)
    (hisTy : Basis.IsTyBasis b) :
    exists tauv, C.TyAt Gamma Psi0 b tauv := by
  obtain ⟨n, hside⟩ := cert.requestedSide
  exact services.exact n hb (CheckedStdFuture.refl Psi0) hside
    hP hcov hstored Delta hwf hisTy

/-- Any already checked result at the requested basis can be standardized
using the same finite requested-basis certificate. -/
theorem checkedToStdRequested_of_localFinite
    {Psi0 : EvalCtx}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {b : Basis} {v : ValExpr} {tauv : ValTy}
    {ht : HasType Delta Gamma e tau}
    {hb : Basis.BasisValid Gamma b}
    (cert : CheckedLocalCallFinite Psi0 ht hb)
    (services : CheckedLocalDepthServices Psi0)
    (hP : V2.PCarrier Psi0)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi0)
    (hstored : V2.StoredWF Psi0)
    (hwf : V2.CtxWF' Delta Gamma)
    (hterm : C.Term Delta Gamma Psi0 e b v tauv) :
    exists w tauw,
      C.Term Delta Gamma Psi0 e (Basis.std (Basis.tof b)) w tauw := by
  obtain ⟨n, hside⟩ := cert.requestedSide
  exact services.toStd n hb (CheckedStdFuture.refl Psi0) hside
    hP hcov hstored hwf hterm

/-- Source progress at the literal standard basis uses the finite depth
carried by this one typing derivation.  The zero layer is direct; a successor
uses exactness and transport from precisely the preceding layer. -/
theorem checkedStdTerm_of_localFinite
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    {Psi0 : EvalCtx}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {b : Basis}
    {ht : HasType Delta Gamma e tau}
    {hb : Basis.BasisValid Gamma b}
    (cert : CheckedLocalCallFinite Psi0 ht hb)
    (services : CheckedLocalDepthServices Psi0)
    (hP : V2.PCarrier Psi0)
    (hcov : V2.VarsCovered Delta Gamma Psi0)
    (hstored : V2.StoredWF Psi0)
    (hwf : V2.CtxWF' Delta Gamma) :
    exists v tauv,
      C.Term Delta Gamma Psi0 e (Basis.std tau) v tauv := by
  obtain ⟨n, ⟨hside⟩⟩ := cert.termSide
  cases n with
  | zero =>
      exact checked_term_progress_depth_zero laws happCut Psi0 ht hside
        Psi0 (CheckedStdFuture.refl Psi0) hP hcov hwf
  | succ n =>
      exact checked_term_progress_depth_succ laws happCut Psi0 n hstored
        (services.exact n) (services.toStd n) ht hside
        Psi0 (CheckedStdFuture.refl Psi0) hP hcov hwf

end RawCertifiedLocalizedCallCertificate
end GLang
