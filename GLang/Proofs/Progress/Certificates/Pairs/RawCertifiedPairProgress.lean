import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairServices
import GLang.Proofs.Progress.Certificates.RawCertifiedSelectedProgressMaster
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairCobAssembly

/-!
# All-depth concrete-pair checked progress

This module wires the source half of the pair-aware mutual construction.
At a fixed depth, space COB yields endpoint exactness and concrete transport;
those two services close the only two evaluator-lookup arms of the generic
34-arm checked source induction.  A separate syntax-COB module supplies the
successor edge from source progress at `n` to space COB at `n+1`.
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 6000

namespace GLang
namespace RawCertifiedPairProgress

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedSelectedProgressMaster
open RawCertifiedPairCertificate
open RawCertifiedPairServices
open RawCertifiedPairCobAssembly

/-- Source progress with pair-selected lookup leaves, uniformly over the
chosen root evaluator once its stored certificates are known. -/
def CheckedPairTermProgressDepthAll (depth : Nat) : Prop :=
  forall (Psi0 : EvalCtx), V2.StoredWF Psi0 ->
    CheckedTermProgressWith (CheckedPairSelectedAt Psi0 depth) Psi0

/-- The variable part of source progress consumes only the literal selected
pair `b -> std(tof b)`.  Exactness is requested for its source endpoint; the
same pair is then executed to standardize the direct variable node. -/
theorem checkedPairSelectedVarArms
    (depth : Nat) (Psi0 : EvalCtx)
    (hrootStored : V2.StoredWF Psi0)
    (hsourceExact : CheckedPairSourceExactDepth depth)
    (htransport : CheckedPairTermTransportDepth depth) :
    CheckedSelectedVarArms (CheckedPairSelectedAt Psi0 depth)
      Psi0 (CheckedStdFuture Psi0) := by
  constructor
  · intro Gamma x s side Psi hfuture hP hcov hwf
    obtain ⟨b, v, hlookup, htof, hb, pair⟩ :=
      (side.deepHere Psi hfuture).1 hcov
    have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
    have hstored : V2.StoredWF Psi := hfuture.storedWF hrootStored
    have hi : Basis.IsTyBasis b := hstored x b hmem
    obtain ⟨k, ⟨htvalid⟩⟩ := hb.tof_tvalid
    have hbStd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
      Basis.std_valid _ htvalid
    have hiStd : Basis.IsTyBasis (Basis.std (Basis.tof b)) :=
      Basis.isTyBasis_std _
    obtain ⟨tauV, htyAt⟩ :=
      hsourceExact Psi0 hrootStored Gamma Psi b
        (Basis.std (Basis.tof b)) pair hb hbStd hfuture hP
        hcov.drop_lin hstored (Finmap.singleton x s) hwf hi hiStd
        (Basis.tof_std _)
    have hdirect : C.Term (Finmap.singleton x s) Gamma Psi
        (.var x) b v tauV := .var_lin hlookup htof hb htyAt
    obtain ⟨w, tauW, hstd⟩ :=
      htransport Psi0 hrootStored (Finmap.singleton x s) Gamma Psi
        (.var x) b (Basis.std (Basis.tof b)) v tauV pair hb hbStd
        hfuture hP hcov.drop_lin hstored hwf hi hiStd
        (Basis.tof_std _) hdirect
    rw [htof] at hstd
    exact ⟨w, tauW, hstd⟩
  · intro Gamma x tau hGamma side Psi hfuture hP hcov hwf
    obtain ⟨b, v, hlookup, htof, hb, pair⟩ :=
      (side.deepHere Psi hfuture).1 hcov
    have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
    have hstored : V2.StoredWF Psi := hfuture.storedWF hrootStored
    have hi : Basis.IsTyBasis b := hstored x b hmem
    obtain ⟨k, ⟨htvalid⟩⟩ := hb.tof_tvalid
    have hbStd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
      Basis.std_valid _ htvalid
    have hiStd : Basis.IsTyBasis (Basis.std (Basis.tof b)) :=
      Basis.isTyBasis_std _
    obtain ⟨tauV, htyAt⟩ :=
      hsourceExact Psi0 hrootStored Gamma Psi b
        (Basis.std (Basis.tof b)) pair hb hbStd hfuture hP hcov
        hstored (∅ : LCtx) hwf hi hiStd (Basis.tof_std _)
    have hGamma' : Gamma.lookup x = some (Basis.tof b) := by
      rw [htof]
      exact hGamma
    have hdirect : C.Term (∅ : LCtx) Gamma Psi (.var x) b v tauV :=
      .var_nlin hlookup hGamma' hb htyAt
    obtain ⟨w, tauW, hstd⟩ :=
      htransport Psi0 hrootStored (∅ : LCtx) Gamma Psi (.var x)
        b (Basis.std (Basis.tof b)) v tauV pair hb hbStd hfuture
        hP hcov hstored hwf hi hiStd (Basis.tof_std _) hdirect
    rw [htof] at hstd
    exact ⟨w, tauW, hstd⟩

/-- Once the semantic services at one depth are known, the generic source
recursor closes all 34 source rules. -/
theorem checkedPairTermProgressDepthAll_of_services
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (depth : Nat)
    (hsourceExact : CheckedPairSourceExactDepth depth)
    (htransport : CheckedPairTermTransportDepth depth) :
    CheckedPairTermProgressDepthAll depth := by
  intro Psi0 hrootStored
  exact checked_selected_term_progress laws happCut
    (CheckedPairSelectedAt Psi0 depth) Psi0 (CheckedStdFuture Psi0)
    (RawCertifiedWorldBinderProgress.checkedStdFuture_extensionClosed Psi0)
    (checkedPairSelectedVarArms depth Psi0 hrootStored
      hsourceExact htransport)

/-- Space COB at a depth closes all executable services at that depth. -/
structure CheckedPairDepthServices (depth : Nat) : Prop where
  spaceCob : CheckedPairSpaceCobDepth depth
  sourceExact : CheckedPairSourceExactDepth depth
  targetExact : CheckedPairTargetExactDepth depth
  transport : CheckedPairTermTransportDepth depth
  termProgress : CheckedPairTermProgressDepthAll depth

theorem checkedPairDepthServices_of_spaceCob
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (depth : Nat) (hcob : CheckedPairSpaceCobDepth depth) :
    CheckedPairDepthServices depth := by
  let htarget := checkedPairTargetExactDepth_of_spaceCob depth hcob laws
  let hsource := checkedPairSourceExactDepth_of_spaceCob depth hcob laws
  let htransport := checkedPairTermTransportDepth_of_spaceCob
    depth hcob laws happCut
  exact ⟨hcob, hsource, htarget, htransport,
    checkedPairTermProgressDepthAll_of_services laws happCut depth
      hsource htransport⟩

theorem checkedPairDepthServices_zero
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    CheckedPairDepthServices 0 :=
  checkedPairDepthServices_of_spaceCob laws happCut 0
    checkedPairSpaceCobDepth_zero

/-- The single cross-language successor edge left to the generic COB syntax
layer: checked source progress at `n` executes the embedded source terms of
both non-frame endpoints at pair depth `n+1`. -/
def CheckedPairSpaceCobStep : Prop :=
  forall n, CheckedPairTermProgressDepthAll n ->
    CheckedPairSpaceCobDepth (n + 1)

/-- Pure Nat assembly once the syntax-COB successor edge is supplied.  The
conclusion itself has no semantic premise or global basis oracle. -/
theorem checkedPairDepthServices_all_of_cobStep
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (hcobStep : CheckedPairSpaceCobStep) :
    forall depth, CheckedPairDepthServices depth := by
  intro depth
  induction depth with
  | zero => exact checkedPairDepthServices_zero laws happCut
  | succ n ih =>
      exact checkedPairDepthServices_of_spaceCob laws happCut (n + 1)
        (hcobStep n ih.termProgress)

/-- Closed mutual construction: no semantic service is assumed. -/
theorem checkedPairDepthServices_all
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    forall depth, CheckedPairDepthServices depth :=
  checkedPairDepthServices_all_of_cobStep laws happCut
    (fun n hprogress =>
      checkedPairSpaceCobDepth_succ_of_termProgress n hprogress)

/-! ## Pointwise-finite source trees and the final call -/

/-- Each evaluator lookup may choose its own pair depth.  The all-depth
service family executes that one choice immediately; no maximum across the
other leaves of the source derivation is required. -/
theorem checkedPairSelectedFiniteVarArms
    (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
    (services : forall depth, CheckedPairDepthServices depth) :
    CheckedSelectedVarArms (CheckedPairSelectedFinite Psi0)
      Psi0 (CheckedStdFuture Psi0) := by
  constructor
  · intro Gamma x s side Psi hfuture hP hcov hwf
    obtain ⟨b, v, hlookup, htof, hb, ⟨depth, pair⟩⟩ :=
      (side.deepHere Psi hfuture).1 hcov
    have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
    have hstored : V2.StoredWF Psi := hfuture.storedWF hrootStored
    have hi : Basis.IsTyBasis b := hstored x b hmem
    obtain ⟨k, ⟨htvalid⟩⟩ := hb.tof_tvalid
    have hbStd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
      Basis.std_valid _ htvalid
    have hiStd : Basis.IsTyBasis (Basis.std (Basis.tof b)) :=
      Basis.isTyBasis_std _
    obtain ⟨tauV, htyAt⟩ :=
      (services depth).sourceExact Psi0 hrootStored Gamma Psi b
        (Basis.std (Basis.tof b)) pair hb hbStd hfuture hP
        hcov.drop_lin hstored (Finmap.singleton x s) hwf hi hiStd
        (Basis.tof_std _)
    have hdirect : C.Term (Finmap.singleton x s) Gamma Psi
        (.var x) b v tauV := .var_lin hlookup htof hb htyAt
    obtain ⟨w, tauW, hstd⟩ :=
      (services depth).transport Psi0 hrootStored
        (Finmap.singleton x s) Gamma Psi (.var x) b
        (Basis.std (Basis.tof b)) v tauV pair hb hbStd hfuture
        hP hcov.drop_lin hstored hwf hi hiStd (Basis.tof_std _) hdirect
    rw [htof] at hstd
    exact ⟨w, tauW, hstd⟩
  · intro Gamma x tau hGamma side Psi hfuture hP hcov hwf
    obtain ⟨b, v, hlookup, htof, hb, ⟨depth, pair⟩⟩ :=
      (side.deepHere Psi hfuture).1 hcov
    have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
    have hstored : V2.StoredWF Psi := hfuture.storedWF hrootStored
    have hi : Basis.IsTyBasis b := hstored x b hmem
    obtain ⟨k, ⟨htvalid⟩⟩ := hb.tof_tvalid
    have hbStd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
      Basis.std_valid _ htvalid
    have hiStd : Basis.IsTyBasis (Basis.std (Basis.tof b)) :=
      Basis.isTyBasis_std _
    obtain ⟨tauV, htyAt⟩ :=
      (services depth).sourceExact Psi0 hrootStored Gamma Psi b
        (Basis.std (Basis.tof b)) pair hb hbStd hfuture hP hcov
        hstored (∅ : LCtx) hwf hi hiStd (Basis.tof_std _)
    have hGamma' : Gamma.lookup x = some (Basis.tof b) := by
      rw [htof]
      exact hGamma
    have hdirect : C.Term (∅ : LCtx) Gamma Psi (.var x) b v tauV :=
      .var_nlin hlookup hGamma' hb htyAt
    obtain ⟨w, tauW, hstd⟩ :=
      (services depth).transport Psi0 hrootStored (∅ : LCtx)
        Gamma Psi (.var x) b (Basis.std (Basis.tof b)) v tauV
        pair hb hbStd hfuture hP hcov hstored hwf hi hiStd
        (Basis.tof_std _) hdirect
    rw [htof] at hstd
    exact ⟨w, tauW, hstd⟩

theorem checkedPairFiniteTermProgress
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0) :
    CheckedTermProgressWith (CheckedPairSelectedFinite Psi0) Psi0 := by
  let services := checkedPairDepthServices_all laws happCut
  intro Delta Gamma e tau ht
  exact checked_selected_term_progress laws happCut
    (CheckedPairSelectedFinite Psi0) Psi0 (CheckedStdFuture Psi0)
    (RawCertifiedWorldBinderProgress.checkedStdFuture_extensionClosed Psi0)
    (checkedPairSelectedFiniteVarArms Psi0 hrootStored services) ht

/-- Pair-local checked progress at the requested basis.  The source tree is
pointwise finite at each lookup, and the final standard-to-requested pair
chooses one independent finite depth. -/
theorem checked_progress_pairLocalFinite
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {requested : Basis}
    (ht : HasType Delta Gamma e (Basis.tof requested))
    (hrequested : Basis.BasisValid Gamma requested)
    (cert : CheckedPairLocalCallFinite Psi ht requested)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered Delta Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' Delta Gamma) :
    exists v tauV, C.Term Delta Gamma Psi e requested v tauV := by
  obtain ⟨termSide⟩ := cert.termSide
  obtain ⟨vStd, tauVStd, hStd⟩ :=
    checkedPairFiniteTermProgress laws happCut Psi hstored ht termSide
      Psi (CheckedStdFuture.refl Psi) hP hcov hwf
  obtain ⟨depth, requestPair⟩ := cert.requestedPair
  obtain ⟨k, ⟨htvalid⟩⟩ := hrequested.tof_tvalid
  have hstdValid : Basis.BasisValid Gamma
      (Basis.std (Basis.tof requested)) :=
    Basis.std_valid _ htvalid
  exact (checkedPairDepthServices_all laws happCut depth).transport
    Psi hstored Delta Gamma Psi e (Basis.std (Basis.tof requested))
    requested vStd tauVStd requestPair hstdValid hrequested
    (CheckedStdFuture.refl Psi) hP hcov.drop_lin hstored hwf
    (Basis.isTyBasis_std _) hrequested.isTyBasis
    (Basis.tof_std _).symm hStd

end RawCertifiedPairProgress
end GLang
