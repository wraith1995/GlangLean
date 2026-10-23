import GLang.Proofs.Progress.Certificates.RawCertifiedSelectedProgressMaster
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardCertificate
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedExactAnchorStore
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairServices
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardServices

/-! Context-indexed selected-basis progress. Evaluator worlds consist of a standard-future relation and an exact lookup store. -/

namespace GLang
namespace RawCertifiedContextSelectedProgress

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate
open RawCertifiedPairFreeStandardCertificate
open RawCertifiedPairServices
open RawCertifiedPairFreeStandardServices
open RawCertifiedWorldBinderProgress
open RawCertifiedWorldProgressArms
open RawCertifiedWorldBoundaryProgress
open RawCertifiedExactAnchorStore

/-! ## Context-indexed worlds -/

/-- The concrete state needed by a free-standard source traversal.  The
future field feeds the existing proof-indexed source certificate, while the
exact store closes a literal-standard variable leaf without recursing on a
standard-self pair. -/
structure CheckedAnchorWorld (Psi0 : EvalCtx)
    (Gamma : NLCtx) (Psi : EvalCtx) : Prop where
  future : CheckedStdFuture Psi0 Psi
  anchors : CheckedExactLookupStore Gamma Psi

/-- Nonlinear source binders advance the source context, evaluator, and exact
lookup store in lockstep. -/
theorem CheckedAnchorWorld.extendNonlinearStandard
    {Psi0 Psi : EvalCtx} {Gamma : NLCtx}
    (world : CheckedAnchorWorld Psi0 Gamma Psi)
    {x : VName} (hxPsi : x ∉ Psi.names) (hxGamma : x ∉ Gamma)
    {tau : Ty} {tauV : ValTy}
    (hnew : C.TyAt Gamma Psi (Basis.std tau) tauV) :
    CheckedAnchorWorld Psi0 (Finmap.insert x tau Gamma)
      (Psi.extend x (Basis.std tau) (.var x tauV)) :=
  ⟨world.future.extend_std hxPsi tau (.var x tauV),
    RawCertifiedExactAnchorStore.CheckedExactLookupStore.extendNonlinearStandard
      world.anchors hxPsi hxGamma hnew⟩

/-- Linear source binders change only the evaluator component of the anchor
world. -/
theorem CheckedAnchorWorld.extendLinearStandard
    {Psi0 Psi : EvalCtx} {Gamma : NLCtx}
    (world : CheckedAnchorWorld Psi0 Gamma Psi)
    {x : VName} (hxPsi : x ∉ Psi.names)
    {s : Space} {tauV : ValTy}
    (hnew : C.TyAt Gamma Psi (Basis.stdSpace s) tauV) :
    CheckedAnchorWorld Psi0 Gamma
      (Psi.extend x (Basis.stdSpace s) (.var x tauV)) :=
  ⟨world.future.extend_std hxPsi (.space s) (.var x tauV),
    RawCertifiedExactAnchorStore.CheckedExactLookupStore.extendLinearStandard
      world.anchors hxPsi hnew⟩

/-- Abstract laws used by the context-indexed motives.  Keeping the law
record separate from `CheckedAnchorWorld` makes the source traversal reusable
with a stronger state, while preventing any accidental weakening back to an
evaluator-only predicate. -/
structure CheckedContextWorldLaws (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop) : Prop where
  future : forall {Gamma Psi}, World Gamma Psi -> CheckedStdFuture Psi0 Psi
  anchors : forall {Gamma Psi}, World Gamma Psi ->
    CheckedExactLookupStore Gamma Psi
  extendNonlinearStandard : forall {Gamma Psi} {x : VName},
    World Gamma Psi -> x ∉ Psi.names -> x ∉ Gamma ->
    forall {tau : Ty} {tauV : ValTy},
      C.TyAt Gamma Psi (Basis.std tau) tauV ->
      World (Finmap.insert x tau Gamma)
        (Psi.extend x (Basis.std tau) (.var x tauV))
  extendLinearStandard : forall {Gamma Psi} {x : VName},
    World Gamma Psi -> x ∉ Psi.names ->
    forall {s : Space} {tauV : ValTy},
      C.TyAt Gamma Psi (Basis.stdSpace s) tauV ->
      World Gamma (Psi.extend x (Basis.stdSpace s) (.var x tauV))

/-- The concrete anchor world satisfies the abstract laws definitionally
through the checked exact-store extension operations. -/
theorem checkedAnchorWorld_laws (Psi0 : EvalCtx) :
    CheckedContextWorldLaws Psi0 (CheckedAnchorWorld Psi0) where
  future world := world.future
  anchors world := world.anchors
  extendNonlinearStandard := by
    intro Gamma Psi x world hxPsi hxGamma tau tauV hnew
    exact CheckedAnchorWorld.extendNonlinearStandard world hxPsi hxGamma hnew
  extendLinearStandard := by
    intro Gamma Psi x world hxPsi s tauV hnew
    exact CheckedAnchorWorld.extendLinearStandard world hxPsi hnew

/-! ## Context-indexed motives -/

def cMotiveSContextSelected
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (Gamma : NLCtx) (s : Space) (h : SValid Gamma s) : Prop :=
  CheckedLocalSideSWith selected Psi0 h ->
  forall Psi, World Gamma Psi -> V2.PCarrier Psi ->
    V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
    exists sv, C.Space Gamma Psi s sv

def cMotiveTContextSelected
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (Gamma : NLCtx) (tau : Ty) (k : Kind) (h : TValid Gamma tau k) : Prop :=
  CheckedLocalSideTWith selected Psi0 h ->
  forall Psi, World Gamma Psi -> V2.PCarrier Psi ->
    V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
    exists tauV, C.Ty Gamma Psi tau tauV /\
      C.TyAt Gamma Psi (Basis.std tau) tauV

def cMotiveSubContextSelected
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (Gamma : NLCtx) (s0 s1 : Space) (h : SubType Gamma s0 s1) : Prop :=
  CheckedLocalSideSubWith selected Psi0 h ->
  forall Psi, World Gamma Psi -> V2.PCarrier Psi ->
    V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
    exists v tauV, C.Term (∅ : LCtx) Gamma Psi (.embed s0)
      (Basis.std (.space (.tprod (.dual s0) s1))) v tauV

def cMotiveHContextSelected
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (Delta : LCtx) (Gamma : NLCtx) (e : Term) (tau : Ty)
    (h : HasType Delta Gamma e tau) : Prop :=
  CheckedLocalSideBasesWith selected Psi0 h ->
  forall Psi, World Gamma Psi -> V2.PCarrier Psi ->
    V2.VarsCovered Delta Gamma Psi -> V2.CtxWF' Delta Gamma ->
    exists v tauV, C.Term Delta Gamma Psi e (Basis.std tau) v tauV

/-! ## The remaining relaxed-pair service at a variable leaf -/

/-- Variable handlers for a context-indexed source traversal. -/
structure CheckedContextSelectedVarArms
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop) : Prop where
  lin : forall {Gamma : NLCtx} {x : VName} {s : Space},
    cMotiveHContextSelected selected Psi0 World
      (Finmap.singleton x s) Gamma (.var x) (.space s) .var_lin
  nlin : forall {Gamma : NLCtx} {x : VName} {tau : Ty}
      (hGamma : Gamma.lookup x = some tau),
    cMotiveHContextSelected selected Psi0 World
      (∅ : LCtx) Gamma (.var x) tau (.var_nlin hGamma)

/-- The free-standard variable cases.  Literal-standard selections use the
world's exact lookup anchor directly.  Only the recursive right branch calls
the relaxed pair transport service. -/
theorem checkedFreeStdContextSelectedVarArms
    (depth : Nat) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (worldLaws : CheckedContextWorldLaws Psi0 World)
    (hrootStored : V2.StoredWF Psi0)
    (htransport :
      RawCertifiedPairFreeStandardServices.CheckedFreeStdPairTermTransportDepth
        depth) :
    CheckedContextSelectedVarArms (CheckedFreeStdSelectedAt Psi0 depth)
      Psi0 World := by
  constructor
  · intro Gamma x s side Psi hWorld hP hcov hwf
    have hfuture := worldLaws.future hWorld
    obtain ⟨b, v, hlookup, htof, hb, selected⟩ :=
      (side.deepHere Psi hfuture).1 hcov
    have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
    rcases selected with hstandard | pair
    · have hlookupStd : EvalCtx.lookup Psi
          (x, Basis.std (Basis.tof b)) = some v := by
        simpa only [← hstandard] using hlookup
      obtain ⟨tauV, hAt⟩ := worldLaws.anchors hWorld hlookupStd
      have htofStd : Basis.tof (Basis.std (Basis.tof b)) = .space s := by
        simpa only [Basis.tof_std] using htof
      have hbStd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) := by
        obtain ⟨_k, ⟨htvalid⟩⟩ := hb.tof_tvalid
        exact Basis.std_valid _ htvalid
      exact ⟨v, tauV, by
        simpa only [Basis.tof_std, htof] using
          (C.Term.var_lin hlookupStd htofStd hbStd hAt)⟩
    · have hstored : V2.StoredWF Psi := hfuture.storedWF hrootStored
      have hisTy : Basis.IsTyBasis b := hstored x b hmem
      obtain ⟨_k, ⟨htvalid⟩⟩ := hb.tof_tvalid
      have hbStd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
        Basis.std_valid _ htvalid
      obtain ⟨tauV, hAt⟩ := worldLaws.anchors hWorld hlookup
      have hdirect : C.Term (Finmap.singleton x s) Gamma Psi
          (.var x) b v tauV :=
        .var_lin hlookup htof hb hAt
      obtain ⟨w, tauW, hstd⟩ := htransport Psi0 hrootStored
        (Finmap.singleton x s) Gamma Psi (.var x) b
        (Basis.std (Basis.tof b)) v tauV pair hb hbStd hfuture
        (worldLaws.anchors hWorld) hP
        hcov.drop_lin hstored hwf hisTy (Basis.isTyBasis_std _)
        (Basis.tof_std _) hdirect
      rw [htof] at hstd
      exact ⟨w, tauW, hstd⟩
  · intro Gamma x tau hGamma side Psi hWorld hP hcov hwf
    have hfuture := worldLaws.future hWorld
    obtain ⟨b, v, hlookup, htof, hb, selected⟩ :=
      (side.deepHere Psi hfuture).1 hcov
    have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
    rcases selected with hstandard | pair
    · have hlookupStd : EvalCtx.lookup Psi
          (x, Basis.std (Basis.tof b)) = some v := by
        simpa only [← hstandard] using hlookup
      obtain ⟨tauV, hAt⟩ := worldLaws.anchors hWorld hlookupStd
      have hbStd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) := by
        obtain ⟨_k, ⟨htvalid⟩⟩ := hb.tof_tvalid
        exact Basis.std_valid _ htvalid
      have hGammaStd : Gamma.lookup x =
          some (Basis.tof (Basis.std (Basis.tof b))) := by
        simpa only [Basis.tof_std, htof] using hGamma
      exact ⟨v, tauV, by
        simpa only [Basis.tof_std, htof] using
          (C.Term.var_nlin hlookupStd hGammaStd hbStd hAt)⟩
    · have hstored : V2.StoredWF Psi := hfuture.storedWF hrootStored
      have hisTy : Basis.IsTyBasis b := hstored x b hmem
      obtain ⟨_k, ⟨htvalid⟩⟩ := hb.tof_tvalid
      have hbStd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
        Basis.std_valid _ htvalid
      obtain ⟨tauV, hAt⟩ := worldLaws.anchors hWorld hlookup
      have hGamma' : Gamma.lookup x = some (Basis.tof b) := by
        rw [htof]
        exact hGamma
      have hdirect : C.Term (∅ : LCtx) Gamma Psi (.var x) b v tauV :=
        .var_nlin hlookup hGamma' hb hAt
      obtain ⟨w, tauW, hstd⟩ := htransport Psi0 hrootStored
        (∅ : LCtx) Gamma Psi (.var x) b
        (Basis.std (Basis.tof b)) v tauV pair hb hbStd hfuture
        (worldLaws.anchors hWorld) hP hcov hstored hwf
        hisTy (Basis.isTyBasis_std _)
        (Basis.tof_std _) hdirect
      rw [htof] at hstd
      exact ⟨w, tauW, hstd⟩

/-! ## One context-changing binder -/

/-! The generated recursor exposes descendant trees as `PProd`s.  These
small proof-preserving adapters reconstruct the exact local-side wrapper for
an immediate child. -/

private def sideSOfPairs
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {Gamma : NLCtx} {s : Space} {h : SValid Gamma s}
    (shallow : PProd True
      (SValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi0 he) h))
    (deep : PProd True
      (SValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWith selected Psi0 he) h)) :
    CheckedLocalSideSWith selected Psi0 h :=
  CheckedLocalSideSWith.ofBelowPair shallow deep

private def sideTOfPairs
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {Gamma : NLCtx} {tau : Ty} {k : Kind} {h : TValid Gamma tau k}
    (shallow : PProd True
      (TValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi0 he) h))
    (deep : PProd True
      (TValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWith selected Psi0 he) h)) :
    CheckedLocalSideTWith selected Psi0 h :=
  CheckedLocalSideTWith.ofBelowPair shallow deep

private def sideSubOfPairs
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {Gamma : NLCtx} {s0 s1 : Space} {h : SubType Gamma s0 s1}
    (shallow : PProd True
      (SubType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi0 he) h))
    (deep : PProd True
      (SubType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWith selected Psi0 he) h)) :
    CheckedLocalSideSubWith selected Psi0 h :=
  CheckedLocalSideSubWith.ofBelowPair shallow deep

private def sideHOfPairs
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau}
    (shallow : PProd (CheckedLocalTermSideBasis Psi0 h)
      (HasType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi0 he) h))
    (deep : PProd (CheckedLocalTermSideBasisWith selected Psi0 h)
      (HasType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWith selected Psi0 he) h)) :
    CheckedLocalSideBasesWith selected Psi0 h :=
  CheckedLocalSideBasesWith.ofBelowPair shallow deep

private def sideTDomain
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind}
    {L : Finset Name} {ht0 : TValid Gamma tau0 k0}
    {hbody : forall y, y ∉ L ->
      TValid (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1}
    (side : CheckedLocalSideTWith selected Psi0
      (.piTy L ht0 hbody)) :
    CheckedLocalSideTWith selected Psi0 ht0 :=
  CheckedLocalSideTWith.ofBelowPair
    side.shallow.descendants.1 side.deep.1

private def sideTBody
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind}
    {L : Finset Name} {ht0 : TValid Gamma tau0 k0}
    {hbody : forall y, y ∉ L ->
      TValid (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1}
    (side : CheckedLocalSideTWith selected Psi0
      (.piTy L ht0 hbody)) (y : Name) (hy : y ∉ L) :
    CheckedLocalSideTWith selected Psi0 (hbody y hy) :=
  CheckedLocalSideTWith.ofBelowPair
    (side.shallow.descendants.2 y hy) (side.deep.2 y hy)

/-- Context-indexed counterpart of `checked_arm_ty_pi_world`.  The proof is
the same checked Pi construction, except that its recursive codomain call
receives the source context and exact-anchor store extended by the domain's
already-computed `C.TyAt` certificate. -/
theorem checked_arm_ty_pi_context
    (laws : CheckedRenameLaws)
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (worldLaws : CheckedContextWorldLaws Psi0 World) :
    forall {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind}
      (L : Finset Name)
      (ht0 : TValid Gamma tau0 k0)
      (hbody : forall y, y ∉ L ->
        TValid (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1),
      cMotiveTContextSelected selected Psi0 World Gamma tau0 k0 ht0 ->
      (forall y (hy : y ∉ L),
        cMotiveTContextSelected selected Psi0 World
          (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1
          (hbody y hy)) ->
      cMotiveTContextSelected selected Psi0 World Gamma
        (.piTy tau0 tau1) (.arrow k0 k1) (.piTy L ht0 hbody) := by
  intro Gamma tau0 tau1 k0 k1 L ht0 hbody ih0 ihbody
    side Psi hWorld hP hcov hwf
  obtain ⟨tauV0, _hTy0, hAt0⟩ :=
    ih0 (sideTDomain side) Psi hWorld hP hcov hwf
  have h0eval : ValTy.EvalT Psi tau0 tauV0 := by
    simpa only [Basis.tof_std] using hAt0.erase
  have hanc0 : V2.StdAnchored Psi tau0 tauV0 := tyAt_stdAnchored hAt0
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Psi ∪ L ∪ Gamma.keys ∪ Ty.fv tau1 ∪
      Basis.fv (Basis.std tau0) ∪ ValTy.fv tauV0)
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨hxPsi, hxL⟩, hxGammaKeys⟩, hxTau1⟩, hxBasis⟩,
    hxTauV0⟩ := hx
  have hxGamma : x ∉ Gamma := by
    intro hm
    exact hxGammaKeys (Finmap.mem_keys.mpr hm)
  have hxNames : x ∉ Psi.names := by
    intro hm
    obtain ⟨⟨z, b⟩, hkey, hz⟩ := Finset.mem_image.mp hm
    simp only at hz
    subst z
    exact (EvalCtx.avoidB_spec hxPsi).1 b (Finmap.mem_keys.mp hkey)
  have hWorld' : World (Finmap.insert x tau0 Gamma)
      (Psi.extend x (Basis.std tau0) (.var x tauV0)) :=
    worldLaws.extendNonlinearStandard hWorld hxNames hxGamma hAt0
  have hfresh : (x, Basis.std tau0) ∉ Psi :=
    (EvalCtx.avoidB_spec hxPsi).1 _
  have hP' : V2.PCarrier
      (Psi.extend x (Basis.std tau0) (.var x tauV0)) :=
    hP.extend_var hfresh (V2.evalT_fv h0eval hP.1) h0eval
      (fun a b heq => ⟨tauV0, heq ▸ hanc0⟩)
  have hcov' : V2.VarsCovered (∅ : LCtx)
      (Finmap.insert x tau0 Gamma)
      (Psi.extend x (Basis.std tau0) (.var x tauV0)) :=
    hcov.extend_var
  have hwf' : V2.CtxWF' (∅ : LCtx)
      (Finmap.insert x tau0 Gamma) := by
    have h := RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
      (b := Basis.std tau0) hwf Finmap.notMem_empty hxGamma
      (Basis.std_valid tau0 ht0)
    simpa only [Basis.tof_std] using h
  obtain ⟨tauV1, _hTy1, hAt1⟩ :=
    ihbody x hxL (sideTBody side x hxL) _ hWorld' hP' hcov' hwf'
  have hlcTauV0 : ValTy.lc tauV0 :=
    evalT_lc h0eval hP.1.toEvalCtxLc
  have hlcTauV1 : ValTy.lc tauV1 :=
    evalT_lc hAt1.erase hP'.1.toEvalCtxLc
  obtain ⟨L1, hcod⟩ := checkedTyAt_cofinite_of_fresh laws hwf
    ⟨k0, ⟨ht0⟩⟩ hxGamma hAt1 hxPsi hxBasis hxTauV0 hxTau1
    hlcTauV0 hlcTauV1
  let tauVOut := ValTy.closeRec 0 x tauV1
  have hAtOut : C.TyAt Gamma Psi (Basis.std (.piTy tau0 tau1))
      (.piTy tauV0 tauVOut) := by
    apply C.TyAt.frame
      (Basis.std_valid (.piTy tau0 tau1) (.piTy L ht0 hbody))
      hAt0 L1
    · intro y hy
      have hc := hcod y hy
      rw [Basis.std_openVar] at hc
      simpa only [tauVOut, Basis.tof_std] using hc
  exact ⟨.piTy tauV0 tauVOut, checkedTy_of_tyAtStd hAtOut, hAtOut⟩

/-! ## Context-changing term binders -/

/-- Context-indexed real-codomain linear abstraction.  The only difference
from the unary-world arm is that the already-computed domain interpretation
is installed in the exact-anchor world before the body induction call. -/
theorem checked_arm_llam_real_context
    (laws : CheckedRenameLaws)
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (worldLaws : CheckedContextWorldLaws Psi0 World) :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {s : Space} {e : Term}
      (L : Finset Name),
      (hs : SValid Gamma s) →
      (hbody : ∀ y, y ∉ L →
        HasType (Finmap.insert y s Delta) Gamma
          (Term.openVar y e) (.space .real)) →
      cMotiveSContextSelected selected Psi0 World Gamma s hs →
      (∀ y (hy : y ∉ L), cMotiveHContextSelected selected Psi0 World
        (Finmap.insert y s Delta) Gamma
        (Term.openVar y e) (.space .real) (hbody y hy)) →
      cMotiveHContextSelected selected Psi0 World Delta Gamma
        (.llam s .real e) (.space (.dual s)) (.llam_real L hs hbody) := by
  intro Delta Gamma s e L hs hbody ihs ihbody
    side Psi hWorld hP hcov hwf
  obtain ⟨sv, hsv⟩ :=
    ihs (CheckedLocalSideSWith.ofBelowPair
      side.shallow.descendants.1 side.deepDescendants.1)
      Psi hWorld hP hcov.drop_lin (ctxWF_dropLin hwf)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Psi ∪ L ∪ Delta.keys ∪ Gamma.keys ∪ Term.fv e ∪
      Basis.fv (Basis.stdSpace s) ∪ ValSpace.fv sv)
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨⟨hxPsi, hxL⟩, hxDeltaKeys⟩, hxGammaKeys⟩,
    hxe⟩, hxb⟩, hxsv⟩ := hx
  have hxDelta : x ∉ Delta := by
    intro hm
    exact hxDeltaKeys (Finmap.mem_keys.mpr hm)
  have hxGamma : x ∉ Gamma := by
    intro hm
    exact hxGammaKeys (Finmap.mem_keys.mpr hm)
  have hxNames : x ∉ Psi.names := by
    intro hm
    obtain ⟨⟨z, b⟩, hkey, hz⟩ := Finset.mem_image.mp hm
    simp only at hz
    subst z
    exact (EvalCtx.avoidB_spec hxPsi).1 b (Finmap.mem_keys.mp hkey)
  have hDomainAt : C.TyAt Gamma Psi (Basis.stdSpace s) (.space sv) := by
    simpa only [Basis.std, Basis.sof_stdSpace] using checked_tyAt_space hs hsv
  have hWorld' : World Gamma
      (Psi.extend x (Basis.stdSpace s) (.var x (.space sv))) :=
    worldLaws.extendLinearStandard hWorld hxNames hDomainAt
  have heval : ValTy.EvalT Psi (.space s) (.space sv) := .space hsv.erase
  have hfresh : (x, Basis.stdSpace s) ∉ Psi :=
    (EvalCtx.avoidB_spec hxPsi).1 _
  have hP' : V2.PCarrier
      (Psi.extend x (Basis.stdSpace s) (.var x (.space sv))) :=
    hP.extend_var hfresh (V2.evalT_fv heval hP.1) heval
      (fun _ _ h => nomatch h)
  have hcov' : V2.VarsCovered (Finmap.insert x s Delta) Gamma
      (Psi.extend x (Basis.stdSpace s) (.var x (.space sv))) :=
    hcov.extend_var_lin
  have hwf' : V2.CtxWF' (Finmap.insert x s Delta) Gamma := by
    have h := RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
      (b := Basis.stdSpace s) hwf hxDelta hxGamma
      (Basis.stdSpace_valid s hs)
    simpa only [Basis.sof_stdSpace] using h
  obtain ⟨v, tauV, hv⟩ :=
    ihbody x hxL
      (CheckedLocalSideBasesWith.ofBelowPair
        (side.shallow.descendants.2 x hxL)
        (side.deepDescendants.2 x hxL))
      _ hWorld' hP' hcov' hwf'
  have hv' : C.Term (Finmap.insert x s Delta) Gamma
      (Psi.extend x (Basis.stdSpace s) (.var x (.space sv)))
      (Term.openVar x e) .one
      (.reshap v (.space .real) tauV) (.space .real) :=
    retag hv tyAt_one_any
  have hlcsv : ValSpace.lc sv :=
    realize_lc_joint.1 hsv.erase hP.1.toEvalCtxLc
  obtain ⟨L1, hfam⟩ := checkedTerm_llam_cofinite_of_placeholder laws
    hwf ⟨hs⟩ hxDelta hxGamma hv' hxPsi hxb hxsv hxe
    (by simp [Basis.fv]) (by simp [ValTy.fv, ValSpace.fv]) hlcsv
  let env : Fin (ValSpace.dofUB sv) → ValExpr := fun i =>
    ValExpr.subst x (.delta i.val sv) (.reshap v (.space .real) tauV)
  have hspaceDual : C.Space Gamma Psi (.dual s) sv :=
    .dual ⟨.dual hs⟩ hsv
  have hAtOut : C.TyAt Gamma Psi (.dual (Basis.stdSpace s)) (.space sv) := by
    simpa only [Basis.std, Basis.stdSpace] using
      (checked_tyAt_space (.dual hs) hspaceDual)
  have ht : Nonempty (HasType Delta Gamma
      (.llam (Basis.sof (Basis.stdSpace s)) .real e)
      (Basis.tof (.dual (Basis.stdSpace s)))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType Delta Gamma (.llam s .real e)
        (.space (.dual s))) from ⟨.llam_real L hs hbody⟩)
  have hstep := C.Term.llam_assemble_real
    (b' := Basis.stdSpace s) (e := e) (env := env)
    (Basis.htof_stdSpace s) ht
    (.dual (Basis.stdSpace_valid s hs) (Basis.htof_stdSpace s)) hAtOut
    (by simpa only [Basis.sof_stdSpace] using hsv) L1
    (fun y hy i => by
      simpa only [env, Basis.sof_stdSpace] using hfam y hy i.val)
  exact ⟨_, _, by
    simpa only [Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

/-- Context-indexed tensor-codomain linear abstraction. -/
theorem checked_arm_llam_tensor_context
    (laws : CheckedRenameLaws)
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (worldLaws : CheckedContextWorldLaws Psi0 World) :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {s0 s : Space} {e : Term}
      (L : Finset Name)
      (hne : s ≠ .real) (hs0 : SValid Gamma s0) (hs : SValid Gamma s)
      (hbody : ∀ y, y ∉ L →
        HasType (Finmap.insert y s0 Delta) Gamma
          (Term.openVar y e) (.space s)),
      cMotiveSContextSelected selected Psi0 World Gamma s0 hs0 →
      cMotiveSContextSelected selected Psi0 World Gamma s hs →
      (∀ y (hy : y ∉ L), cMotiveHContextSelected selected Psi0 World
        (Finmap.insert y s0 Delta) Gamma (Term.openVar y e) (.space s)
          (hbody y hy)) →
      cMotiveHContextSelected selected Psi0 World Delta Gamma
        (.llam s0 s e) (.space (.tprod (.dual s0) s))
          (.llam_tensor L hne hs0 hs hbody) := by
  intro Delta Gamma s0 s e L hne hs0 hs hbody ihs0 ihs ihbody
    side Psi hWorld hP hcov hwf
  obtain ⟨sv0, hsv0⟩ :=
    ihs0 (CheckedLocalSideSWith.ofBelowPair
      side.shallow.descendants.1 side.deepDescendants.1)
      Psi hWorld hP hcov.drop_lin (ctxWF_dropLin hwf)
  obtain ⟨sv, hsv⟩ :=
    ihs (CheckedLocalSideSWith.ofBelowPair
      side.shallow.descendants.2.1 side.deepDescendants.2.1)
      Psi hWorld hP hcov.drop_lin (ctxWF_dropLin hwf)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Psi ∪ L ∪ Delta.keys ∪ Gamma.keys ∪ Term.fv e ∪
      Basis.fv (Basis.stdSpace s0) ∪ Basis.fv (Basis.stdSpace s) ∪
      ValSpace.fv sv0 ∪ ValSpace.fv sv)
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hxPsi, hxL⟩, hxDeltaKeys⟩, hxGammaKeys⟩,
    hxe⟩, hxb0⟩, hxbs⟩, hxsv0⟩, hxsv⟩ := hx
  have hxDelta : x ∉ Delta := by
    intro hm
    exact hxDeltaKeys (Finmap.mem_keys.mpr hm)
  have hxGamma : x ∉ Gamma := by
    intro hm
    exact hxGammaKeys (Finmap.mem_keys.mpr hm)
  have hxNames : x ∉ Psi.names := by
    intro hm
    obtain ⟨⟨z, b⟩, hkey, hz⟩ := Finset.mem_image.mp hm
    simp only at hz
    subst z
    exact (EvalCtx.avoidB_spec hxPsi).1 b (Finmap.mem_keys.mp hkey)
  have hDomainAt : C.TyAt Gamma Psi
      (Basis.stdSpace s0) (.space sv0) := by
    simpa only [Basis.std, Basis.sof_stdSpace] using
      checked_tyAt_space hs0 hsv0
  have hWorld' : World Gamma
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0))) :=
    worldLaws.extendLinearStandard hWorld hxNames hDomainAt
  have heval0 : ValTy.EvalT Psi (.space s0) (.space sv0) :=
    .space hsv0.erase
  have hfresh : (x, Basis.stdSpace s0) ∉ Psi :=
    (EvalCtx.avoidB_spec hxPsi).1 _
  have hP' : V2.PCarrier
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0))) :=
    hP.extend_var hfresh (V2.evalT_fv heval0 hP.1) heval0
      (fun _ _ h => nomatch h)
  have hcov' : V2.VarsCovered (Finmap.insert x s0 Delta) Gamma
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0))) :=
    hcov.extend_var_lin
  have hwf' : V2.CtxWF' (Finmap.insert x s0 Delta) Gamma := by
    have h := RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
      (b := Basis.stdSpace s0) hwf hxDelta hxGamma
      (Basis.stdSpace_valid s0 hs0)
    simpa only [Basis.sof_stdSpace] using h
  obtain ⟨v, tauV, hv⟩ :=
    ihbody x hxL
      (CheckedLocalSideBasesWith.ofBelowPair
        (side.shallow.descendants.2.2 x hxL)
        (side.deepDescendants.2.2 x hxL))
      _ hWorld' hP' hcov' hwf'
  have hsvExt : C.Space Gamma
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0))) s sv :=
    checkedSpace_extend hsv hxPsi
  have hAtCod : C.TyAt Gamma
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0)))
      (Basis.stdSpace s) (.space sv) := by
    simpa only [Basis.std, Basis.sof_stdSpace] using
      checked_tyAt_space hs hsvExt
  have hv' : C.Term (Finmap.insert x s0 Delta) Gamma
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0)))
      (Term.openVar x e) (Basis.stdSpace s)
      (.reshap v (.space sv) tauV) (.space sv) := retag hv hAtCod
  have hlcsv0 : ValSpace.lc sv0 :=
    realize_lc_joint.1 hsv0.erase hP.1.toEvalCtxLc
  obtain ⟨L1, hfam⟩ := checkedTerm_llam_cofinite_of_placeholder laws
    hwf ⟨hs0⟩ hxDelta hxGamma hv' hxPsi hxb0 hxsv0 hxe hxbs
    (by simpa only [ValTy.fv] using hxsv) hlcsv0
  let env : Fin (ValSpace.dofUB sv0) → ValExpr := fun i =>
    ValExpr.subst x (.delta i.val sv0) (.reshap v (.space sv) tauV)
  have hspaceOut : C.Space Gamma Psi (.tprod (.dual s0) s)
      (.tprod sv0 sv) :=
    .tprod ⟨.tprod (.dual hs0) hs⟩ (.dual ⟨.dual hs0⟩ hsv0) hsv
  have hAtOut : C.TyAt Gamma Psi
      (.tprod (.dual (Basis.stdSpace s0)) (Basis.stdSpace s))
      (.space (.tprod sv0 sv)) := by
    simpa only [Basis.std, Basis.stdSpace] using
      (checked_tyAt_space (.tprod (.dual hs0) hs) hspaceOut)
  have ht : Nonempty (HasType Delta Gamma
      (.llam (Basis.sof (Basis.stdSpace s0))
        (Basis.sof (Basis.stdSpace s)) e)
      (Basis.tof (.tprod (.dual (Basis.stdSpace s0))
        (Basis.stdSpace s)))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType Delta Gamma (.llam s0 s e)
        (.space (.tprod (.dual s0) s))) from
        ⟨.llam_tensor L hne hs0 hs hbody⟩)
  have hbv : Basis.BasisValid Gamma
      (.tprod (.dual (Basis.stdSpace s0)) (Basis.stdSpace s)) :=
    .tprod
      (.dual (Basis.stdSpace_valid s0 hs0) (Basis.htof_stdSpace s0))
      (Basis.stdSpace_valid s hs) rfl (Basis.htof_stdSpace s)
  have hstep := C.Term.llam_assemble
    (b' := Basis.stdSpace s0) (b := Basis.stdSpace s)
    (e := e) (env := env)
    (Basis.htof_stdSpace s0) ht hbv hAtOut
    (by simpa only [Basis.sof_stdSpace] using hsv0)
    (by simpa only [Basis.sof_stdSpace] using hsv) L1
    (fun y hy i => by
      simpa only [env, Basis.sof_stdSpace] using hfam y hy i.val)
  exact ⟨_, _, by
    simpa only [Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

/-- Context-indexed nonlinear abstraction.  Here both the nonlinear source
context and evaluator acquire the standard domain placeholder before the
body call. -/
theorem checked_arm_nllam_context
    (laws : CheckedRenameLaws)
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (worldLaws : CheckedContextWorldLaws Psi0 World) :
    ∀ {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind} {e : Term}
      (L : Finset Name)
      (ht : TValid Gamma (.piTy tau0 tau1) (.arrow k0 k1))
      (hbody : ∀ y, y ∉ L → HasType ∅ (Finmap.insert y tau0 Gamma)
        (Term.openVar y e) (Ty.openVar y tau1)),
      cMotiveTContextSelected selected Psi0 World Gamma
        (.piTy tau0 tau1) (.arrow k0 k1) ht →
      (∀ y (hy : y ∉ L), cMotiveHContextSelected selected Psi0 World
        ∅ (Finmap.insert y tau0 Gamma) (Term.openVar y e)
          (Ty.openVar y tau1) (hbody y hy)) →
      cMotiveHContextSelected selected Psi0 World ∅ Gamma
        (.nllam tau0 e) (.piTy tau0 tau1) (.nllam L ht hbody) := by
  intro Gamma tau0 tau1 k0 k1 e L ht hbody ihT ihbody
    side Psi hWorld hP hcov hwf
  cases ht with
  | piTy Lv ht0 htvalid1 =>
      obtain ⟨tauVpi, _hTyPi, hAtPi⟩ :=
        ihT (CheckedLocalSideTWith.ofBelowPair
          side.shallow.descendants.1 side.deepDescendants.1)
          Psi hWorld hP hcov hwf
      obtain ⟨tauV0, tauV1, rfl, hbv, hdom, LAt, hcod⟩ :=
        tyAtStdPi_inv hAtPi
      have h0eval : ValTy.EvalT Psi tau0 tauV0 := by
        simpa only [Basis.tof_std] using hdom.erase
      have hanc0 : V2.StdAnchored Psi tau0 tauV0 :=
        tyAt_stdAnchored hdom
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
        (EvalCtx.avoidB Psi ∪ L ∪ LAt ∪ Gamma.keys ∪ Term.fv e ∪
          Ty.fv tau1 ∪ Basis.fv (Basis.std tau0) ∪ ValTy.fv tauV0)
      simp only [Finset.mem_union, not_or] at hx
      obtain ⟨⟨⟨⟨⟨⟨⟨hxPsi, hxL⟩, hxLAt⟩, hxGammaKeys⟩,
        hxe⟩, hxTau1⟩, hxBasis⟩, hxTauV0⟩ := hx
      have hxGamma : x ∉ Gamma := by
        intro hm
        exact hxGammaKeys (Finmap.mem_keys.mpr hm)
      have hxNames : x ∉ Psi.names := by
        intro hm
        obtain ⟨⟨z, b⟩, hkey, hz⟩ := Finset.mem_image.mp hm
        simp only at hz
        subst z
        exact (EvalCtx.avoidB_spec hxPsi).1 b (Finmap.mem_keys.mp hkey)
      have hWorld' : World (Finmap.insert x tau0 Gamma)
          (Psi.extend x (Basis.std tau0) (.var x tauV0)) :=
        worldLaws.extendNonlinearStandard hWorld hxNames hxGamma hdom
      have hfresh : (x, Basis.std tau0) ∉ Psi :=
        (EvalCtx.avoidB_spec hxPsi).1 _
      have hP' : V2.PCarrier
          (Psi.extend x (Basis.std tau0) (.var x tauV0)) :=
        hP.extend_var hfresh (V2.evalT_fv h0eval hP.1) h0eval
          (fun a b heq => ⟨tauV0, heq ▸ hanc0⟩)
      have hcov' : V2.VarsCovered ∅ (Finmap.insert x tau0 Gamma)
          (Psi.extend x (Basis.std tau0) (.var x tauV0)) :=
        hcov.extend_var
      have hwf' : V2.CtxWF' ∅ (Finmap.insert x tau0 Gamma) := by
        have h := RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
          (b := Basis.std tau0) hwf Finmap.notMem_empty hxGamma
          (Basis.std_valid tau0 ht0)
        simpa only [Basis.tof_std] using h
      obtain ⟨v, tauV, hv⟩ :=
        ihbody x hxL
          (CheckedLocalSideBasesWith.ofBelowPair
            (side.shallow.descendants.2 x hxL)
            (side.deepDescendants.2 x hxL))
          _ hWorld' hP' hcov' hwf'
      have hcodx := hcod x hxLAt
      have hv' := retag hv hcodx
      have hlcTauV0 : ValTy.lc tauV0 :=
        evalT_lc h0eval hP.1.toEvalCtxLc
      have hlcv : ValExpr.lc
          (.reshap v (ValTy.openVar x tauV0 tauV1) tauV) :=
        opStep_lc hv'.erase hP'.1.toEvalCtxLc
      have hlcTauV1 : ValTy.lc (ValTy.openVar x tauV0 tauV1) :=
        evalT_lc hcodx.erase hP'.1.toEvalCtxLc
      obtain ⟨LTerm, hterm⟩ := checkedTerm_nllam_cofinite_of_fresh
        laws hwf ⟨k0, ⟨ht0⟩⟩ hxGamma hv' hxPsi hxBasis hxTauV0
        hxe hxTau1 hlcTauV0 hlcv hlcTauV1
      obtain ⟨LTy, hty⟩ := checkedTyAt_cofinite_of_fresh laws hwf
        ⟨k0, ⟨ht0⟩⟩ hxGamma hcodx hxPsi hxBasis hxTauV0
        hxTau1 hlcTauV0 hlcTauV1
      let tauVOut := ValTy.closeRec 0 x (ValTy.openVar x tauV0 tauV1)
      let env := ValExpr.closeRec 0 x
        (.reshap v (ValTy.openVar x tauV0 tauV1) tauV)
      have hAtOut : C.TyAt Gamma Psi
          (.frame (Basis.std tau0) (Basis.std tau1))
          (.piTy tauV0 tauVOut) := by
        apply C.TyAt.frame hbv hdom LTy
        · intro y hy
          have hc := hty y hy
          rw [Basis.std_openVar] at hc
          simpa only [tauVOut, Basis.tof_std] using hc
      have htTerm : Nonempty (HasType ∅ Gamma (.nllam tau0 e)
          (Basis.tof (.frame (Basis.std tau0) (Basis.std tau1)))) := by
        simpa only [Basis.tof, Basis.tof_std] using
          (show Nonempty (HasType ∅ Gamma (.nllam tau0 e)
            (.piTy tau0 tau1)) from
            ⟨.nllam L (.piTy Lv ht0 htvalid1) hbody⟩)
      have hstep := C.Term.nllam
        (b₀ := Basis.std tau0) (b₁ := Basis.std tau1)
        (env := env)
        (Basis.tof_std tau0) (Basis.tof_std tau1) htTerm
        (Basis.std_valid (.piTy tau0 tau1) (.piTy Lv ht0 htvalid1))
        hAtOut hdom (LTerm ∪ LTy)
        (fun y hy => by
          have hyt : y ∉ LTerm :=
            fun hm => hy (Finset.mem_union_left _ hm)
          have hc := hterm y hyt
          rw [Basis.std_openVar] at hc
          simpa only [env, tauVOut, Basis.tof_std] using hc)
        (fun y hy => by
          have hyy : y ∉ LTy :=
            fun hm => hy (Finset.mem_union_right _ hm)
          have hc := hty y hyy
          rw [Basis.std_openVar] at hc
          simpa only [tauVOut, Basis.tof_std] using hc)
      exact ⟨_, _, by simpa only [Basis.std] using hstep⟩

/-! ## Promotion-free four-way source recursion -/

/-- The complete source traversal over a context-indexed world.  Promotion
freedom is threaded as part of every mutual motive, so the proof-relevant
typing derivation is consumed structurally and the `promote` constructor is
eliminated by its impossible `False` branch.  All context-preserving cases
reuse the existing checked world arms; exactly the four binders above update
the context-indexed world. -/
theorem checked_context_selected_term_progress
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (worldLaws : CheckedContextWorldLaws Psi0 World)
    (vars : CheckedContextSelectedVarArms selected Psi0 World) :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
      (h : HasType Delta Gamma e tau),
      Graded.PromotionFree h →
      cMotiveHContextSelected selected Psi0 World Delta Gamma e tau h := by
  intro Delta Gamma e tau h
  apply HasType.rec
      (motive_1 := fun Gamma' s' h' =>
        Graded.SPromotionFree h' →
          cMotiveSContextSelected selected Psi0 World Gamma' s' h')
      (motive_2 := fun Gamma' tau' k' h' =>
        Graded.TPromotionFree h' →
          cMotiveTContextSelected selected Psi0 World Gamma' tau' k' h')
      (motive_3 := fun Gamma' s0' s1' h' =>
        Graded.SubPromotionFree h' →
          cMotiveSubContextSelected selected Psi0 World Gamma' s0' s1' h')
      (motive_4 := fun Delta' Gamma' e' tau' h' =>
        Graded.PromotionFree h' →
          cMotiveHContextSelected selected Psi0 World
            Delta' Gamma' e' tau' h')
  case empty =>
    intro Gamma _hfree _side
    exact checked_arm_empty_world (World Gamma)
  case real =>
    intro Gamma _hfree _side
    exact checked_arm_real_world (World Gamma)
  case dual =>
    intro Gamma _s hs ih hfree side
    exact checked_arm_dual_world (World Gamma) hs
      (ih hfree (sideSOfPairs side.shallow.descendants side.deep))
  case dsum =>
    intro Gamma _s0 _s1 hs0 hs1 ih0 ih1 hfree side
    exact checked_arm_dsum_world (World Gamma) hs0 hs1
      (ih0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deep.1))
      (ih1 hfree.2
        (sideSOfPairs side.shallow.descendants.2 side.deep.2))
  case tprod =>
    intro Gamma _s0 _s1 hs0 hs1 ih0 ih1 hfree side
    exact checked_arm_tprod_world (World Gamma) hs0 hs1
      (ih0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deep.1))
      (ih1 hfree.2
        (sideSOfPairs side.shallow.descendants.2 side.deep.2))
  case ker =>
    intro Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe hfree side
    exact checked_arm_ker_world (World Gamma) hs0 hs1 he
      (ih0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deep.1))
      (ih1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
      (ihe hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case coker =>
    intro Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe hfree side
    exact checked_arm_coker_world (World Gamma) hs0 hs1 he
      (ih0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deep.1))
      (ih1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
      (ihe hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case img =>
    intro Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe hfree side
    exact checked_arm_img_world (World Gamma) hs0 hs1 he
      (ih0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deep.1))
      (ih1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
      (ihe hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case coimg =>
    intro Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe hfree side
    exact checked_arm_coimg_world (World Gamma) hs0 hs1 he
      (ih0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deep.1))
      (ih1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
      (ihe hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case space =>
    intro Gamma _s hs ih hfree side
    exact checked_arm_ty_space_world (World Gamma) hs
      (ih hfree (sideSOfPairs side.shallow.descendants side.deep))
  case piTy =>
    intro _Gamma _tau0 _tau1 _k0 _k1 L ht0 ht1 ih0 ih1 hfree
    exact checked_arm_ty_pi_context laws selected Psi0 World worldLaws
      L ht0 ht1 (ih0 hfree.1)
      (fun y hy => ih1 y hy (hfree.2 y hy))
  case sub_ker =>
    intro Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe hfree side
    exact checked_arm_sub_ker_world (World Gamma) hs0 hs1 he
      (ih0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deep.1))
      (ih1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
      (ihe hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case sub_coker =>
    intro Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe hfree side
    exact checked_arm_sub_coker_world (World Gamma) hs0 hs1 he
      (ih0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deep.1))
      (ih1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
      (ihe hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case sub_img =>
    intro Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe hfree side
    exact checked_arm_sub_img_world (World Gamma) hs0 hs1 he
      (ih0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deep.1))
      (ih1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
      (ihe hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case sub_coimg =>
    intro Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe hfree side
    exact checked_arm_sub_coimg_world (World Gamma) hs0 hs1 he
      (ih0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deep.1))
      (ih1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
      (ihe hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case zero =>
    intro _Delta Gamma _s hs ihs hfree side
    exact checked_arm_zero_world (World Gamma) hs
      (ihs hfree
        (sideSOfPairs side.shallow.descendants side.deepDescendants))
  case smul =>
    intro _Delta0 _Delta1 Gamma _e0 _e1 _s
      hs hd ht0 ht1 ihs ih0 ih1 hfree side
    exact checked_arm_smul_world (World Gamma) hs hd ht0 ht1
      (ihs hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deepDescendants.1))
      (ih0 hfree.2.1
        (sideHOfPairs side.shallow.descendants.2.1
          side.deepDescendants.2.1))
      (ih1 hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2
          side.deepDescendants.2.2))
  case add =>
    intro _Delta Gamma _e0 _e1 _s hs ht0 ht1 ihs ih0 ih1 hfree side
    exact checked_arm_add_world (World Gamma) hs ht0 ht1
      (ihs hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deepDescendants.1))
      (ih0 hfree.2.1
        (sideHOfPairs side.shallow.descendants.2.1
          side.deepDescendants.2.1))
      (ih1 hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2
          side.deepDescendants.2.2))
  case inner =>
    intro _Gamma _s hs ihs hfree side
    exact checked_arm_inner_world (World _Gamma) hs
      (ihs hfree
        (sideSOfPairs side.shallow.descendants side.deepDescendants))
  case real_lit =>
    intro Gamma r _hfree _side
    exact checked_arm_real_lit_world (World Gamma) r
  case app_linear =>
    intro _Delta0 _Delta1 Gamma _e0 _e1 _s0 _s1
      hs0 hs1 hd ht0 ht1 ihs0 ihs1 ih0 ih1 hfree side
    exact checked_arm_app_linear_world (World Gamma) hs0 hs1 hd ht0 ht1
      (ihs0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deepDescendants.1))
      (ihs1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1
          side.deepDescendants.2.1))
      (ih0 hfree.2.2.1
        (sideHOfPairs side.shallow.descendants.2.2.1
          side.deepDescendants.2.2.1))
      (ih1 hfree.2.2.2
        (sideHOfPairs side.shallow.descendants.2.2.2
          side.deepDescendants.2.2.2))
  case app_inner =>
    intro _Delta0 _Delta1 Gamma _e0 _e1 _s
      hs hd ht0 ht1 ihs ih0 ih1 hfree side
    exact checked_arm_app_inner_world (World Gamma) hs hd ht0 ht1
      (ihs hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deepDescendants.1))
      (ih0 hfree.2.1
        (sideHOfPairs side.shallow.descendants.2.1
          side.deepDescendants.2.1))
      (ih1 hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2
          side.deepDescendants.2.2))
  case app_nonlinear =>
    intro Gamma _e0 _e1 _tau0 _tau1 ht0 ht1 ih0 ih1 hfree side
    exact checked_arm_app_nonlinear_world_of_tyAt_appCut happCut
      (World Gamma) ht0 ht1
      (ih0 hfree.1
        (sideHOfPairs side.shallow.descendants.1 side.deepDescendants.1))
      (ih1 hfree.2
        (sideHOfPairs side.shallow.descendants.2 side.deepDescendants.2))
  case var_lin =>
    intro _Gamma _x _s _hfree
    exact vars.lin
  case var_nlin =>
    intro _Gamma _x _tau hGamma _hfree
    exact vars.nlin hGamma
  case pinv_tensor =>
    intro Gamma _e _s0 _s1 hs0 hs1 ht ihs0 ihs1 ih hfree side
    exact checked_arm_pinv_tensor_world (World Gamma) hs0 hs1 ht
      (ihs0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deepDescendants.1))
      (ihs1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1
          side.deepDescendants.2.1))
      (ih hfree.2.2
        (sideHOfPairs side.shallow.descendants.2.2
          side.deepDescendants.2.2))
  case pinv_dual =>
    intro Gamma _e _s hs ht ihs ih hfree side
    exact checked_arm_pinv_dual_world (World Gamma) hs ht
      (ihs hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deepDescendants.1))
      (ih hfree.2
        (sideHOfPairs side.shallow.descendants.2 side.deepDescendants.2))
  case promote =>
    intro _Delta _Gamma _e _tau _lin _hdDelta _hdGamma _hfresh _ht _ih
      hfree
    exact False.elim hfree
  case dsumE =>
    intro _Delta Gamma _e0 _e1 _s0 _s1
      hs0 hs1 ht0 ht1 ihs0 ihs1 ih0 ih1 hfree side
    exact checked_arm_dsumE_world (World Gamma) hs0 hs1 ht0 ht1
      (ihs0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deepDescendants.1))
      (ihs1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1
          side.deepDescendants.2.1))
      (ih0 hfree.2.2.1
        (sideHOfPairs side.shallow.descendants.2.2.1
          side.deepDescendants.2.2.1))
      (ih1 hfree.2.2.2
        (sideHOfPairs side.shallow.descendants.2.2.2
          side.deepDescendants.2.2.2))
  case tprodE =>
    intro _Delta0 _Delta1 Gamma _e0 _e1 _s0 _s1
      hs0 hs1 hd ht0 ht1 ihs0 ihs1 ih0 ih1 hfree side
    exact checked_arm_tprodE_world (World Gamma) hs0 hs1 hd ht0 ht1
      (ihs0 hfree.1
        (sideSOfPairs side.shallow.descendants.1 side.deepDescendants.1))
      (ihs1 hfree.2.1
        (sideSOfPairs side.shallow.descendants.2.1
          side.deepDescendants.2.1))
      (ih0 hfree.2.2.1
        (sideHOfPairs side.shallow.descendants.2.2.1
          side.deepDescendants.2.2.1))
      (ih1 hfree.2.2.2
        (sideHOfPairs side.shallow.descendants.2.2.2
          side.deepDescendants.2.2.2))
  case llam_real =>
    intro _Delta _Gamma _s _e L hs hbody ihs ihbody hfree
    exact checked_arm_llam_real_context laws selected Psi0 World worldLaws
      L hs hbody (ihs hfree.1)
      (fun y hy => ihbody y hy (hfree.2 y hy))
  case llam_tensor =>
    intro _Delta _Gamma _s0 _s _e L hne hs0 hs hbody
      ihs0 ihs ihbody hfree
    exact checked_arm_llam_tensor_context laws selected Psi0 World worldLaws
      L hne hs0 hs hbody (ihs0 hfree.1) (ihs hfree.2.1)
      (fun y hy => ihbody y hy (hfree.2.2 y hy))
  case embed =>
    intro Gamma _s0 _s1 hsub ih hfree side
    exact checked_arm_embed_world (World Gamma) hsub
      (ih hfree
        (sideSubOfPairs side.shallow.descendants side.deepDescendants))
  case nllam =>
    intro _Gamma _tau0 _tau1 _k0 _k1 _e L ht hbody ihT ihbody hfree
    exact checked_arm_nllam_context laws selected Psi0 World worldLaws
      L ht hbody (ihT hfree.1)
      (fun y hy => ihbody y hy (hfree.2 y hy))

/-- Instantiate the generic context traversal with the free-standard
selected-basis policy and its store-threaded recursive pair transport. -/
theorem checked_freeStd_context_term_progress
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (depth : Nat) (Psi0 : EvalCtx)
    (World : NLCtx → EvalCtx → Prop)
    (worldLaws : CheckedContextWorldLaws Psi0 World)
    (hrootStored : V2.StoredWF Psi0)
    (htransport :
      RawCertifiedPairFreeStandardServices.CheckedFreeStdPairTermTransportDepth
        depth) :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
      (h : HasType Delta Gamma e tau),
      Graded.PromotionFree h →
      cMotiveHContextSelected (CheckedFreeStdSelectedAt Psi0 depth)
        Psi0 World Delta Gamma e tau h :=
  checked_context_selected_term_progress laws happCut
    (CheckedFreeStdSelectedAt Psi0 depth) Psi0 World worldLaws
    (checkedFreeStdContextSelectedVarArms depth Psi0 World worldLaws
      hrootStored htransport)

/-- Concrete exact-anchor specialization rooted at the evaluator supplied by
raw consistency. -/
theorem checked_freeStd_anchor_term_progress
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (depth : Nat) (Psi0 : EvalCtx)
    (hrootStored : V2.StoredWF Psi0)
    (htransport :
      RawCertifiedPairFreeStandardServices.CheckedFreeStdPairTermTransportDepth
        depth) :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
      (h : HasType Delta Gamma e tau),
      Graded.PromotionFree h →
      cMotiveHContextSelected (CheckedFreeStdSelectedAt Psi0 depth)
        Psi0 (CheckedAnchorWorld Psi0) Delta Gamma e tau h :=
  checked_freeStd_context_term_progress laws happCut depth Psi0
    (CheckedAnchorWorld Psi0) (checkedAnchorWorld_laws Psi0)
    hrootStored htransport

end RawCertifiedContextSelectedProgress
end GLang
