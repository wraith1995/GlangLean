import GLang.Proofs.Progress.Certificates.Context.RawCertifiedContextSelectedProgress
import GLang.Proofs.Progress.Certificates.RawCertifiedFreeStdGenericCobState
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardServices
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairProgress
import GLang.Proofs.Progress.Certificates.RawCertifiedCallProgress
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardCreationPrefixLayer
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedDepthAssemblyLocal

set_option maxHeartbeats 3200000
set_option maxRecDepth 6000

namespace GLang
namespace RawCertifiedPairFreeStandardNatProgress

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate
open RawCertifiedPairFreeStandardCertificate
open RawCertifiedPairServices
open RawCertifiedPairFreeStandardServices
open RawCertifiedPairProgress
open RawCertifiedCallProgress
open RawCertifiedExactAnchorStore
open RawCertifiedContextSelectedProgress
open RawCertifiedPairFreeStandardCreationPrefixLayer
open RawCertifiedDepthAssemblyLocal
open RawCertifiedDepthStdTySide
open RawCertifiedDepthTransportLocal

/-! ## Boundary-only result reanchoring -/

/-- The one genuine basis-conversion boundary left after compiling a source
term at the literal standard basis of its type.

This interface deliberately says nothing about how the transport is built.
For a space result it may be implemented by a checked `C.Cob`; for a frame
result it is the higher-order, contravariant-domain/covariant-codomain term
transport.  In particular, the caller does not expose the recursive
`CheckedPairBasisDepth` proof-engineering tree to checked progress. -/
structure CheckedRootBasisBoundary
    (Gamma : NLCtx) (Psi : EvalCtx) (requested : Basis) : Prop where
  requestedValid : Basis.BasisValid Gamma requested
  reanchor : forall {Delta : LCtx} {e : Term}
      {v : ValExpr} {tauV : ValTy},
    V2.CtxWF' Delta Gamma ->
    C.Term Delta Gamma Psi e (Basis.std (Basis.tof requested)) v tauV ->
      exists w tauW, C.Term Delta Gamma Psi e requested w tauW

/-! ## One-depth source progress -/

/-- Store-threaded standard-result progress at one root and relaxed-pair
depth.  This is kept local to the Nat assembly to preserve the one-way import
from the assembly into the structural COB implementation. -/
def CheckedFreeStdStoreTermProgressDepth
    (Psi0 : EvalCtx) (depth : Nat) : Prop :=
  forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {tau : Ty}
    (ht : HasType Delta Gamma e tau),
    Graded.PromotionFree ht ->
    CheckedLocalSideBasesWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht ->
    CheckedStdFuture Psi0 Psi ->
    V2.PCarrier Psi -> V2.VarsCovered Delta Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
    CheckedExactLookupStore Gamma Psi ->
    exists v tauV, C.Term Delta Gamma Psi e (Basis.std tau) v tauV

/-- Store-threaded source progress at a fixed relaxed-pair depth, uniformly
over the root evaluator once its stored-WF proof is supplied. -/
def CheckedFreeStdTermProgressDepthAll (depth : Nat) : Prop :=
  forall (Psi0 : EvalCtx), V2.StoredWF Psi0 ->
    CheckedFreeStdStoreTermProgressDepth Psi0 depth

/-- The context-indexed recursor converts a concrete relaxed-pair transport
service into source progress at the same depth. -/
theorem checkedFreeStdTermProgressDepthAll_of_transport
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (depth : Nat)
    (htransport :
      RawCertifiedPairFreeStandardServices.CheckedFreeStdPairTermTransportDepth
        depth) :
    CheckedFreeStdTermProgressDepthAll depth := by
  intro Psi0 hrootStored Delta Gamma Psi e tau ht hfree side
    hfuture hP hcov _hstored hwf anchors
  exact checked_freeStd_anchor_term_progress laws happCut depth Psi0
    hrootStored htransport ht hfree side Psi
      ⟨hfuture, anchors⟩ hP hcov hwf

/-! ## Numeric mutual package -/

/-- All semantic services available at one relaxed-pair depth. -/
structure CheckedFreeStdDepthServices (depth : Nat) : Prop where
  spaceCob : CheckedFreeStdPairSpaceCobDepth depth
  sourceExact : CheckedFreeStdPairSourceExactDepth depth
  targetExact : CheckedFreeStdPairTargetExactDepth depth
  transport :
    RawCertifiedPairFreeStandardServices.CheckedFreeStdPairTermTransportDepth
      depth
  termProgress : CheckedFreeStdTermProgressDepthAll depth

/-- Space COB closes every other store-threaded service at the same depth. -/
theorem checkedFreeStdDepthServices_of_spaceCob
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (depth : Nat) (hcob : CheckedFreeStdPairSpaceCobDepth depth) :
    CheckedFreeStdDepthServices depth := by
  let htarget := checkedFreeStdPairTargetExactDepth_of_spaceCob
    depth hcob laws
  let hsource := checkedFreeStdPairSourceExactDepth_of_spaceCob
    depth hcob laws
  let htransport := checkedFreeStdPairTermTransportDepth_of_spaceCob
    depth hcob laws happCut
  exact ⟨hcob, hsource, htarget, htransport,
    checkedFreeStdTermProgressDepthAll_of_transport
      laws happCut depth htransport⟩

/-- The term-free depth-zero certificate has a structural COB and therefore
all five services without a successor premise. -/
theorem checkedFreeStdDepthServices_zero
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    CheckedFreeStdDepthServices 0 :=
  checkedFreeStdDepthServices_of_spaceCob laws happCut 0
    checkedFreeStdPairSpaceCobDepth_zero

/-- Auditable shape of the one structural successor theorem: source progress
at depth `n` builds space COB for positive relaxed pairs at depth `n + 1`. -/
def CheckedFreeStdPairSpaceCobStep : Prop :=
  forall n, CheckedFreeStdTermProgressDepthAll n ->
    CheckedFreeStdPairSpaceCobDepth (n + 1)

/-- Pure Nat assembly from the single successor COB edge. -/
theorem checkedFreeStdDepthServices_all_of_cobStep
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (hcobStep : CheckedFreeStdPairSpaceCobStep) :
    forall depth, CheckedFreeStdDepthServices depth := by
  intro depth
  induction depth with
  | zero => exact checkedFreeStdDepthServices_zero laws happCut
  | succ n ih =>
      exact checkedFreeStdDepthServices_of_spaceCob laws happCut (n + 1)
        (hcobStep n ih.termProgress)

/-- The structural state-threaded COB module discharges the one successor
edge.  Its raw telescope is definitionally the same as this assembly's local
progress family, so no semantic conversion or extra premise is needed. -/
theorem checkedFreeStdPairSpaceCobStep : CheckedFreeStdPairSpaceCobStep := by
  intro depth progressAll
  apply
    RawCertifiedFreeStdGenericCobState.checkedFreeStdPairSpaceCobDepth_succ_of_storeProgress
      depth
  intro Psi0 hrootStored
  exact progressAll Psi0 hrootStored

/-- Closed Nat mutual construction for every relaxed-pair depth. -/
theorem checkedFreeStdDepthServices_all
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    forall depth, CheckedFreeStdDepthServices depth :=
  checkedFreeStdDepthServices_all_of_cobStep laws happCut
    checkedFreeStdPairSpaceCobStep

/-! ## Root boundary constructors -/

/-- A literal standard root has the boundary by reflexivity. -/
theorem checkedRootBasisBoundary_standard
    {Gamma : NLCtx} {Psi : EvalCtx} {tau : Ty} {k : Kind}
    (htau : TValid Gamma tau k) :
    CheckedRootBasisBoundary Gamma Psi (Basis.std tau) := by
  refine ⟨Basis.std_valid _ htau, ?_⟩
  intro Delta e v tauV _hwf hterm
  exact ⟨v, tauV, by simpa only [Basis.tof_std] using hterm⟩

/-- Construct the root boundary from one unary syntax certificate for the
requested basis. -/
theorem checkedRootBasisBoundary_of_localSide
    {Gamma : NLCtx} {Psi : EvalCtx} {requested : Basis}
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hrequested : Basis.BasisValid Gamma requested)
    (sideFinite : CheckedLocalSideBasisFinite Psi hrequested) :
    CheckedRootBasisBoundary Gamma Psi requested := by
  obtain ⟨depth, sideRequested⟩ := sideFinite
  obtain ⟨hstdValid, sideStd⟩ :=
    checkedStdTySideDepth sideRequested hrequested.isTyBasis
  refine ⟨hrequested, ?_⟩
  intro Delta e v tauV hwf hStd
  exact checkedTermTransportDepth_local depth
    (checkedDepthPairLocal_all
      RawCertifiedOperational.RenameProof.checkedRenameLaws
      RawCertifiedOperational.checkedTyAtAppCut depth).2
    RawCertifiedOperational.RenameProof.checkedRenameLaws
    RawCertifiedOperational.checkedTyAtAppCut
    Psi hstored Delta Gamma Psi e
    (Basis.std (Basis.tof requested)) requested v tauV
    hstdValid sideStd hrequested sideRequested
    (CheckedStdFuture.refl Psi) hP hcov hstored hwf
    (Basis.isTyBasis_std _) hrequested.isTyBasis
    (Basis.tof_std _).symm hStd

end RawCertifiedPairFreeStandardNatProgress
end GLang
