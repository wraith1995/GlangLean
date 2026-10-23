import GLang.Proofs.Progress.Certificates.RawCertifiedGenericCobSyntax
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardCertificate
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardExecutableSyntax
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedExactAnchorStore
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardServices

namespace GLang
namespace RawCertifiedFreeStdGenericCobState

open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedGenericCobSyntax
open RawCertifiedPairFreeStandardCertificate
open RawCertifiedPairFreeStandardExecutableSyntax
open RawCertifiedExactAnchorStore
open RawCertifiedPairFreeStandardServices

/-- The positive proof-relevant syntax layer stored by a free-standard pair
at leaf depth `depth`. -/
abbrev CheckedFreeStdExecutableBasisDepth
    (Psi0 : EvalCtx) (depth : Nat)
    {Gamma : NLCtx} {b : Basis} (_hb : Basis.BasisValid Gamma b) : Prop :=
  CheckedFreeStdExecutableBasisSyntaxLayer Psi0
    (fun Psi' => CheckedFreeStdSelectedAt Psi' depth) Gamma b

/-- Source-progress callback at one free-standard selected depth.  The exact
lookup store is indexed by the same current source/evaluator contexts as the
judgment being evaluated. -/
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
    exists v tauV,
      C.Term Delta Gamma Psi e (Basis.std tau) v tauV

/-! ## State-local source re-entry helpers -/

private def sideZero
    {Psi0 : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    {s : Space} {hs : SValid Gamma s}
    (side : CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth)
      Psi0 hs) :
    CheckedLocalSideBasesWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (HasType.zero (Δ := Delta) hs) :=
  CheckedLocalSideBasesWith.ofBelowPair
    ⟨True.intro, ⟨True.intro, side.shallow.descendants⟩⟩
    ⟨True.intro, ⟨True.intro, side.deep⟩⟩

/-- Realize a source space by applying state-threaded source progress to its
canonical zero term at the current exact-anchor world. -/
theorem checkedSpace_of_storeTermProgressDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {s : Space} {hs : SValid Gamma s}
    (hfree : Graded.SPromotionFree hs)
    (side : CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth)
      Psi0 hs)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi) :
    exists sv, C.Space Gamma Psi s sv := by
  let hzero : HasType (∅ : LCtx) Gamma (.zero s) (.space s) := .zero hs
  have hfreeZero : Graded.PromotionFree hzero := by
    dsimp only [hzero]
    exact hfree
  obtain ⟨v, tauV, hv⟩ := progress hzero hfreeZero (sideZero side)
    hfuture hP hcov hstored hwf anchors
  obtain ⟨sv, rfl, hspace⟩ :=
    checkedTyAt_space_inv_full (Basis.tof_std (.space s)) hv.tyAt
  exact ⟨sv, by simpa only [Basis.std, Basis.sof_stdSpace] using hspace⟩

/-- Evaluate one proof-relevant source witness at an arbitrary component
basis after state-threaded progress constructs its exact standard result. -/
theorem checkedTerm_at_spaceBasis_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {s : Space}
    {b : Basis} {envc : ValExpr} {sv : ValSpace}
    (ht : HasType (∅ : LCtx) Gamma e (.space s))
    (hfree : Graded.PromotionFree ht)
    (side : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hb : Basis.BasisValid Gamma b) (hsb : Basis.IsSpaceBasis b)
    (hsof : Basis.sof b = s)
    (hconv : C.Cob Gamma Psi b envc (Basis.stdSpace s))
    (hsv : C.Space Gamma Psi s sv) :
    exists v, C.Term (∅ : LCtx) Gamma Psi e b v (.space sv) := by
  obtain ⟨v, tauV, hv⟩ := progress ht hfree side hfuture hP hcov
    hstored hwf anchors
  have hstdValid : Basis.BasisValid Gamma (Basis.stdSpace s) := by
    have hs : SValid Gamma s := hsof ▸ Classical.choice hb.sof_valid
    exact Basis.stdSpace_valid s hs
  have hspaceB : C.Space Gamma Psi (Basis.sof b) sv := hsof.symm ▸ hsv
  have htyB : C.TyAt Gamma Psi b (.space sv) :=
    .space hsb.tof_eq hb hspaceB
  have htb : Nonempty (HasType (∅ : LCtx) Gamma e (Basis.tof b)) := by
    rw [hsb.tof_eq, hsof]
    exact ⟨ht⟩
  have hinv : C.Cob Gamma Psi (Basis.stdSpace s) (.inv envc) b :=
    .inverse hstdValid hb hconv
  exact ⟨_, .cob hsb.tof_eq (Basis.htof_stdSpace s) htb hb htyB
    (by simpa only [Basis.std] using hv) hinv hspaceB⟩

private def sideInner
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx}
    {s : Space} {hs : SValid Gamma s}
    (side : CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth)
      Psi0 hs) :
    CheckedLocalSideBasesWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (HasType.inner hs) :=
  CheckedLocalSideBasesWith.ofBelowPair
    ⟨True.intro, ⟨True.intro, side.shallow.descendants⟩⟩
    ⟨True.intro, ⟨True.intro, side.deep⟩⟩

/-- Evaluate the canonical inner product at an arbitrary component basis. -/
theorem checkedInner_at_spaceBasis_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {s : Space}
    {envc : ValExpr} {sv : ValSpace} {hs : SValid Gamma s}
    (hfree : Graded.SPromotionFree hs)
    (sideS : CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth)
      Psi0 hs)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hb : Basis.BasisValid Gamma b) (hsb : Basis.IsSpaceBasis b)
    (hsof : Basis.sof b = s)
    (hconv : C.Cob Gamma Psi b envc (Basis.stdSpace s))
    (hsv : C.Space Gamma Psi s sv) :
    exists v, C.Term (∅ : LCtx) Gamma Psi (.inner s)
      (.tprod (.dual b) (.dual b)) v (.space (.tprod sv sv)) := by
  have hconvTof : C.Cob Gamma Psi b envc (Basis.std (Basis.tof b)) := by
    apply checkedCob_stdTof_of_stdSpace hsb
    simpa only [hsof] using hconv
  have hdual := checkedCob_dual_toStdSpace hb hsb hconvTof
  have hstd : Basis.BasisValid Gamma (Basis.stdSpace s) :=
    Basis.stdSpace_valid s hs
  have hsource : Basis.BasisValid Gamma (.tprod (.dual b) (.dual b)) :=
    .tprod (.dual hb hsb.tof_eq) (.dual hb hsb.tof_eq) rfl rfl
  have htarget : Basis.BasisValid Gamma
      (.tprod (.dual (Basis.stdSpace s)) (.dual (Basis.stdSpace s))) :=
    .tprod (.dual hstd (Basis.htof_stdSpace s))
      (.dual hstd (Basis.htof_stdSpace s)) rfl rfl
  have hdual' : C.Cob Gamma Psi (.dual b) (.vtrans (.inv envc))
      (.dual (Basis.stdSpace s)) := by
    simpa only [hsof] using hdual
  have htp0 := C.Cob.tprod hsource htarget hdual' hdual'
  have htp : C.Cob Gamma Psi (.tprod (.dual b) (.dual b))
      (.vkrn (.vtrans (.inv envc)) (.vtrans (.inv envc)))
      (Basis.stdSpace (.tprod (.dual s) (.dual s))) := by
    simpa only [Basis.stdSpace, Basis.sof, hsof] using htp0
  have hsvOut : C.Space Gamma Psi (.tprod (.dual s) (.dual s))
      (.tprod sv sv) :=
    .tprod ⟨.tprod (.dual hs) (.dual hs)⟩
      (.dual ⟨.dual hs⟩ hsv) (.dual ⟨.dual hs⟩ hsv)
  have hsofOut : Basis.sof (.tprod (.dual b) (.dual b)) =
      .tprod (.dual s) (.dual s) := by simp only [Basis.sof, hsof]
  exact checkedTerm_at_spaceBasis_storeDepth progress (.inner hs) hfree
    (sideInner sideS) hfuture hP hcov hstored hwf anchors hsource
    ⟨hsb, hsb⟩ hsofOut htp hsvOut

/-- Evaluate a proof-relevant map witness at arbitrary component bases. -/
theorem checkedMapTerm_at_bases_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {s0 s1 : Space}
    {c0 c1 : Basis} {env0 env1 : ValExpr} {sv0 sv1 : ValSpace}
    (ht : HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1)))
    (hfree : Graded.PromotionFree ht)
    (side : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hc0 : Basis.BasisValid Gamma c0)
    (hc1 : Basis.BasisValid Gamma c1)
    (hsb0 : Basis.IsSpaceBasis c0) (hsb1 : Basis.IsSpaceBasis c1)
    (hsof0 : Basis.sof c0 = s0) (hsof1 : Basis.sof c1 = s1)
    (hconv0 : C.Cob Gamma Psi c0 env0 (Basis.stdSpace s0))
    (hconv1 : C.Cob Gamma Psi c1 env1 (Basis.stdSpace s1))
    (hsv0 : C.Space Gamma Psi s0 sv0)
    (hsv1 : C.Space Gamma Psi s1 sv1) :
    exists v, C.Term (∅ : LCtx) Gamma Psi e (.tprod (.dual c0) c1) v
      (.space (.tprod sv0 sv1)) := by
  obtain ⟨env, hmapConv0⟩ := checkedCob_tprod_dual hc0 hc1 hsb0 hsb1
    hsof0 hsof1 hconv0 hconv1
  have hmapConv : C.Cob Gamma Psi (.tprod (.dual c0) c1) env
      (Basis.stdSpace (.tprod (.dual s0) s1)) := by
    simpa only [Basis.stdSpace] using hmapConv0
  have hsource : Basis.BasisValid Gamma (.tprod (.dual c0) c1) :=
    .tprod (.dual hc0 hsb0.tof_eq) hc1 rfl hsb1.tof_eq
  have hs0 : SValid Gamma s0 := hsof0 ▸ Classical.choice hc0.sof_valid
  have hs1 : SValid Gamma s1 := hsof1 ▸ Classical.choice hc1.sof_valid
  have hsvMap : C.Space Gamma Psi (.tprod (.dual s0) s1)
      (.tprod sv0 sv1) :=
    .tprod ⟨.tprod (.dual hs0) hs1⟩
      (.dual ⟨.dual hs0⟩ hsv0) hsv1
  have hsofMap : Basis.sof (.tprod (.dual c0) c1) =
      .tprod (.dual s0) s1 := by simp only [Basis.sof, hsof0, hsof1]
  exact checkedTerm_at_spaceBasis_storeDepth progress ht hfree side
    hfuture hP hcov hstored hwf anchors hsource ⟨hsb0, hsb1⟩
    hsofMap hmapConv hsvMap

/-! ## Executable syntax inversions -/

private theorem executableDualChild
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma (.dual b)}
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth hb) :
    exists hb0 : Basis.BasisValid Gamma b,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb0 := by
  simpa [CheckedFreeStdExecutableBasisDepth,
    CheckedFreeStdExecutableBasisSyntaxLayer] using side

private theorem executableDsumChildren
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.dsum b0 b1)}
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb0) /\
    exists hb1 : Basis.BasisValid Gamma b1,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb1 := by
  simpa [CheckedFreeStdExecutableBasisDepth,
    CheckedFreeStdExecutableBasisSyntaxLayer] using side

private theorem executableTprodChildren
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.tprod b0 b1)}
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb0) /\
    exists hb1 : Basis.BasisValid Gamma b1,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb1 := by
  simpa [CheckedFreeStdExecutableBasisDepth,
    CheckedFreeStdExecutableBasisSyntaxLayer] using side

private theorem executableProjKerParts
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx}
    {s0 s1 : Space} {e : Term} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.proj (.ker s0 s1 e) b0 b1)}
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb0) /\
    (exists hb1 : Basis.BasisValid Gamma b1,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb1) /\
    Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
    CheckedFreeStdExecutableTermWitness
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)) := by
  simpa [CheckedFreeStdExecutableBasisDepth,
    CheckedFreeStdExecutableBasisSyntaxLayer] using side

private theorem executableProjCokerParts
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx}
    {s0 s1 : Space} {e : Term} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.proj (.coker s0 s1 e) b0 b1)}
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb0) /\
    (exists hb1 : Basis.BasisValid Gamma b1,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb1) /\
    Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
    CheckedFreeStdExecutableTermWitness
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)) := by
  simpa [CheckedFreeStdExecutableBasisDepth,
    CheckedFreeStdExecutableBasisSyntaxLayer] using side

private theorem executableProjImgParts
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx}
    {s0 s1 : Space} {e : Term} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.proj (.img s0 s1 e) b0 b1)}
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb0) /\
    (exists hb1 : Basis.BasisValid Gamma b1,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb1) /\
    Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
    CheckedFreeStdExecutableTermWitness
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)) := by
  simpa [CheckedFreeStdExecutableBasisDepth,
    CheckedFreeStdExecutableBasisSyntaxLayer] using side

private theorem executableProjCoimgParts
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx}
    {s0 s1 : Space} {e : Term} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.proj (.coimg s0 s1 e) b0 b1)}
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb0) /\
    (exists hb1 : Basis.BasisValid Gamma b1,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb1) /\
    Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
    CheckedFreeStdExecutableTermWitness
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)) := by
  simpa [CheckedFreeStdExecutableBasisDepth,
    CheckedFreeStdExecutableBasisSyntaxLayer] using side

private theorem executableImageParts
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma (.image b)}
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth hb) :
    exists s0 s1 e, exists hb0 : Basis.BasisValid Gamma b,
      Basis.sof b = .coker s0 s1 e /\
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb0 /\
      CheckedFreeStdExecutableTermWitness
        (CheckedFreeStdSelectedAt Psi0 depth) Psi0 (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)) := by
  simpa [CheckedFreeStdExecutableBasisDepth,
    CheckedFreeStdExecutableBasisSyntaxLayer] using side

private theorem executableTermsParts
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx}
    {s : Space} {es : List Term} {b : Basis}
    {hb : Basis.BasisValid Gamma (.terms s es b)}
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth hb) :
    (exists hb0 : Basis.BasisValid Gamma b,
      CheckedFreeStdExecutableBasisDepth Psi0 depth hb0) /\
    Basis.sof b = s /\
    CheckedFreeStdExecutableSpaceWitness
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 Gamma s /\
    forall e, e ∈ es ->
      CheckedFreeStdExecutableTermWitness
        (CheckedFreeStdSelectedAt Psi0 depth) Psi0 (∅ : LCtx) Gamma e
          (.space s) := by
  simpa [CheckedFreeStdExecutableBasisDepth,
    CheckedFreeStdExecutableBasisSyntaxLayer] using side

private def executableSideEmpty
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} :
    CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (SValid.empty : SValid Gamma .empty) := by
  apply CheckedLocalSideSWith.ofBelowPair
  · exact ⟨trivial, PUnit.unit⟩
  · exact ⟨trivial, PUnit.unit⟩

private def executableSideReal
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} :
    CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (SValid.real : SValid Gamma .real) := by
  apply CheckedLocalSideSWith.ofBelowPair
  · exact ⟨trivial, PUnit.unit⟩
  · exact ⟨trivial, PUnit.unit⟩

private def executableSideDual
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s : Space}
    {hs : SValid Gamma s}
    (side : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs) :
    CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.dual hs) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨trivial, side.shallow.descendants⟩⟩
    ⟨trivial, ⟨trivial, side.deep⟩⟩

private def executableSideDsum
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    (side0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (side1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1) :
    CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.dsum hs0 hs1) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨trivial, side1.shallow.descendants⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩, ⟨trivial, side1.deep⟩⟩⟩

private def executableSideTprod
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    (side0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (side1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1) :
    CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.tprod hs0 hs1) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨trivial, side1.shallow.descendants⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩, ⟨trivial, side1.deep⟩⟩⟩

private def executableSideKer
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (side1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (sideT : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht) :
    CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.ker hs0 hs1 ht) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def executableSideCoker
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (side1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (sideT : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht) :
    CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.coker hs0 hs1 ht) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def executableSideImg
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (side1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (sideT : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht) :
    CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.img hs0 hs1 ht) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def executableSideCoimg
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (side1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (sideT : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht) :
    CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.coimg hs0 hs1 ht) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

/-- Executable syntax for a space basis reconstructs the exact source-space
derivation together with both its promotion-freedom proof and matching local
side tree.  This is the proof-relevant strengthening of
`genericCheckedSofSide` needed by every source-crossing COB arm. -/
private theorem executableCheckedSofWitness
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma b}
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth hb)
    (hsb : Basis.IsSpaceBasis b) :
    exists hs : SValid Gamma (Basis.sof b),
      Graded.SPromotionFree hs /\
      Nonempty (CheckedLocalSideSWith
        (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs) := by
  revert side hsb
  induction hb with
  | empty =>
      intro _side _hsb
      exact ⟨.empty, trivial, ⟨executableSideEmpty⟩⟩
  | one =>
      intro _side _hsb
      exact ⟨.real, trivial, ⟨executableSideReal⟩⟩
  | @dual Gamma b hb _htof ih =>
      intro side hsb
      obtain ⟨hb', side0⟩ := executableDualChild side
      obtain ⟨hs, hfree, ⟨sideS⟩⟩ := ih side0 hsb
      exact ⟨.dual hs, hfree, ⟨executableSideDual sideS⟩⟩
  | @dsum Gamma b0 b1 hb0 hb1 _htof0 _htof1 ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩⟩ :=
        executableDsumChildren side
      obtain ⟨hs0, hfree0, ⟨sideS0⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1, hfree1, ⟨sideS1⟩⟩ := ih1 side1 hsb.2
      exact ⟨.dsum hs0 hs1, ⟨hfree0, hfree1⟩,
        ⟨executableSideDsum sideS0 sideS1⟩⟩
  | @tprod Gamma b0 b1 hb0 hb1 _htof0 _htof1 ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩⟩ :=
        executableTprodChildren side
      obtain ⟨hs0, hfree0, ⟨sideS0⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1, hfree1, ⟨sideS1⟩⟩ := ih1 side1 hsb.2
      exact ⟨.tprod hs0 hs1, ⟨hfree0, hfree1⟩,
        ⟨executableSideTprod sideS0 sideS1⟩⟩
  | @proj_ker Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _,
        ⟨ht, hfreeT, ⟨sideT⟩⟩⟩ := executableProjKerParts side
      obtain ⟨hs0', hfree0', ⟨sideS0'⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1', hfree1', ⟨sideS1'⟩⟩ := ih1 side1 hsb.2
      have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
      have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
      have p0 : exists hs0 : SValid Gamma s0,
          Graded.SPromotionFree hs0 /\
          Nonempty (CheckedLocalSideSWith
            (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0) := by
        rw [← hsof0]
        exact ⟨hs0', hfree0', ⟨sideS0'⟩⟩
      have p1 : exists hs1 : SValid Gamma s1,
          Graded.SPromotionFree hs1 /\
          Nonempty (CheckedLocalSideSWith
            (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1) := by
        rw [← hsof1]
        exact ⟨hs1', hfree1', ⟨sideS1'⟩⟩
      obtain ⟨hs0, hfree0, ⟨sideS0⟩⟩ := p0
      obtain ⟨hs1, hfree1, ⟨sideS1⟩⟩ := p1
      simpa only [Basis.sof] using
        ⟨SValid.ker hs0 hs1 ht, ⟨hfree0, hfree1, hfreeT⟩,
          ⟨executableSideKer sideS0 sideS1 sideT⟩⟩
  | @proj_coker Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _,
        ⟨ht, hfreeT, ⟨sideT⟩⟩⟩ := executableProjCokerParts side
      obtain ⟨hs0', hfree0', ⟨sideS0'⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1', hfree1', ⟨sideS1'⟩⟩ := ih1 side1 hsb.2
      have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
      have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
      have p0 : exists hs0 : SValid Gamma s0,
          Graded.SPromotionFree hs0 /\
          Nonempty (CheckedLocalSideSWith
            (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0) := by
        rw [← hsof0]
        exact ⟨hs0', hfree0', ⟨sideS0'⟩⟩
      have p1 : exists hs1 : SValid Gamma s1,
          Graded.SPromotionFree hs1 /\
          Nonempty (CheckedLocalSideSWith
            (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1) := by
        rw [← hsof1]
        exact ⟨hs1', hfree1', ⟨sideS1'⟩⟩
      obtain ⟨hs0, hfree0, ⟨sideS0⟩⟩ := p0
      obtain ⟨hs1, hfree1, ⟨sideS1⟩⟩ := p1
      simpa only [Basis.sof] using
        ⟨SValid.coker hs0 hs1 ht, ⟨hfree0, hfree1, hfreeT⟩,
          ⟨executableSideCoker sideS0 sideS1 sideT⟩⟩
  | @proj_img Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _,
        ⟨ht, hfreeT, ⟨sideT⟩⟩⟩ := executableProjImgParts side
      obtain ⟨hs0', hfree0', ⟨sideS0'⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1', hfree1', ⟨sideS1'⟩⟩ := ih1 side1 hsb.2
      have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
      have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
      have p0 : exists hs0 : SValid Gamma s0,
          Graded.SPromotionFree hs0 /\
          Nonempty (CheckedLocalSideSWith
            (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0) := by
        rw [← hsof0]
        exact ⟨hs0', hfree0', ⟨sideS0'⟩⟩
      have p1 : exists hs1 : SValid Gamma s1,
          Graded.SPromotionFree hs1 /\
          Nonempty (CheckedLocalSideSWith
            (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1) := by
        rw [← hsof1]
        exact ⟨hs1', hfree1', ⟨sideS1'⟩⟩
      obtain ⟨hs0, hfree0, ⟨sideS0⟩⟩ := p0
      obtain ⟨hs1, hfree1, ⟨sideS1⟩⟩ := p1
      simpa only [Basis.sof] using
        ⟨SValid.img hs0 hs1 ht, ⟨hfree0, hfree1, hfreeT⟩,
          ⟨executableSideImg sideS0 sideS1 sideT⟩⟩
  | @proj_coimg Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _,
        ⟨ht, hfreeT, ⟨sideT⟩⟩⟩ := executableProjCoimgParts side
      obtain ⟨hs0', hfree0', ⟨sideS0'⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1', hfree1', ⟨sideS1'⟩⟩ := ih1 side1 hsb.2
      have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
      have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
      have p0 : exists hs0 : SValid Gamma s0,
          Graded.SPromotionFree hs0 /\
          Nonempty (CheckedLocalSideSWith
            (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0) := by
        rw [← hsof0]
        exact ⟨hs0', hfree0', ⟨sideS0'⟩⟩
      have p1 : exists hs1 : SValid Gamma s1,
          Graded.SPromotionFree hs1 /\
          Nonempty (CheckedLocalSideSWith
            (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1) := by
        rw [← hsof1]
        exact ⟨hs1', hfree1', ⟨sideS1'⟩⟩
      obtain ⟨hs0, hfree0, ⟨sideS0⟩⟩ := p0
      obtain ⟨hs1, hfree1, ⟨sideS1⟩⟩ := p1
      simpa only [Basis.sof] using
        ⟨SValid.coimg hs0 hs1 ht, ⟨hfree0, hfree1, hfreeT⟩,
          ⟨executableSideCoimg sideS0 sideS1 sideT⟩⟩
  | @image Gamma b s0 s1 e hb hsof hw ih =>
      intro side hsb
      obtain ⟨_, _, _, hb', hsof', side0,
        ⟨_ht, _hfreeT, ⟨_sideT⟩⟩⟩ := executableImageParts side
      obtain ⟨hs, hfreeS, ⟨sideS⟩⟩ := ih side0 hsb
      have p : exists hc : SValid Gamma (.coker s0 s1 e),
          Graded.SPromotionFree hc /\
          Nonempty (CheckedLocalSideSWith
            (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hc) := by
        rw [← hsof]
        exact ⟨hs, hfreeS, ⟨sideS⟩⟩
      obtain ⟨hc, hfreeC, ⟨sideC⟩⟩ := p
      cases hc with
      | coker hs0 hs1 ht0 =>
          have sideS0 : CheckedLocalSideSWith
              (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0 :=
            CheckedLocalSideSWith.ofBelowPair
              sideC.shallow.descendants.1 sideC.deep.1
          have sideS1 : CheckedLocalSideSWith
              (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1 :=
            CheckedLocalSideSWith.ofBelowPair
              sideC.shallow.descendants.2.1 sideC.deep.2.1
          have sideT0 : CheckedLocalSideBasesWith
              (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht0 :=
            CheckedLocalSideBasesWith.ofBelowPair
              sideC.shallow.descendants.2.2 sideC.deep.2.2
          rw [Basis.sof, hsof]
          exact ⟨SValid.img hs0 hs1 ht0, hfreeC,
            ⟨executableSideImg sideS0 sideS1 sideT0⟩⟩
  | @terms Gamma s es b hb htof hsv hall _hne ih =>
      intro side _hsb
      obtain ⟨_, _, ⟨hs, hfree, ⟨sideS⟩⟩, _⟩ :=
        executableTermsParts side
      have hsof := Basis.sof_eq_of_tof_eq_space htof
      rw [Basis.sof, hsof]
      exact ⟨hs, hfree, ⟨sideS⟩⟩
  | frame L hb0 hbody ih0 ihbody =>
      intro _side hsb
      exact False.elim hsb

/-- COB-to-standard service with exact lookup state at the current context.
The syntax layer retains the exact promotion-free source witnesses used by
the free-standard pair certificate. -/
def CheckedFreeStdCobToStdDepthWithStore
    (Psi0 : EvalCtx) (depth : Nat) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    (hb : Basis.BasisValid Gamma b),
    CheckedFreeStdExecutableBasisDepth Psi0 depth hb ->
    CheckedStdFuture Psi0 Psi ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
    CheckedExactLookupStore Gamma Psi ->
    Basis.IsSpaceBasis b ->
    exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))

structure CheckedFreeStdCobTermArmsDepthWithStore
    (Psi0 : EvalCtx) (depth : Nat) : Prop where
  proj_ker :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
      {b0 b1 : Basis}
      (hb0 : Basis.BasisValid Gamma b0)
      (hb1 : Basis.BasisValid Gamma b1)
      (htof0 : Basis.tof b0 = .space s0)
      (htof1 : Basis.tof b1 = .space s1)
      (hw : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))),
      CheckedFreeStdExecutableBasisDepth Psi0 depth
        (.proj_ker hb0 hb1 htof0 htof1 hw) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
      CheckedExactLookupStore Gamma Psi ->
      Basis.IsSpaceBasis b0 -> Basis.IsSpaceBasis b1 ->
      (exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0))) ->
      (exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) ->
      exists env, C.Cob Gamma Psi (.proj (.ker s0 s1 e) b0 b1) env
        (Basis.std (Basis.tof (.proj (.ker s0 s1 e) b0 b1)))
  proj_coker :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
      {b0 b1 : Basis}
      (hb0 : Basis.BasisValid Gamma b0)
      (hb1 : Basis.BasisValid Gamma b1)
      (htof0 : Basis.tof b0 = .space s0)
      (htof1 : Basis.tof b1 = .space s1)
      (hw : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))),
      CheckedFreeStdExecutableBasisDepth Psi0 depth
        (.proj_coker hb0 hb1 htof0 htof1 hw) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
      CheckedExactLookupStore Gamma Psi ->
      Basis.IsSpaceBasis b0 -> Basis.IsSpaceBasis b1 ->
      (exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0))) ->
      (exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) ->
      exists env, C.Cob Gamma Psi (.proj (.coker s0 s1 e) b0 b1) env
        (Basis.std (Basis.tof (.proj (.coker s0 s1 e) b0 b1)))
  proj_img :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
      {b0 b1 : Basis}
      (hb0 : Basis.BasisValid Gamma b0)
      (hb1 : Basis.BasisValid Gamma b1)
      (htof0 : Basis.tof b0 = .space s0)
      (htof1 : Basis.tof b1 = .space s1)
      (hw : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))),
      CheckedFreeStdExecutableBasisDepth Psi0 depth
        (.proj_img hb0 hb1 htof0 htof1 hw) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
      CheckedExactLookupStore Gamma Psi ->
      Basis.IsSpaceBasis b0 -> Basis.IsSpaceBasis b1 ->
      (exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0))) ->
      (exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) ->
      exists env, C.Cob Gamma Psi (.proj (.img s0 s1 e) b0 b1) env
        (Basis.std (Basis.tof (.proj (.img s0 s1 e) b0 b1)))
  proj_coimg :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
      {b0 b1 : Basis}
      (hb0 : Basis.BasisValid Gamma b0)
      (hb1 : Basis.BasisValid Gamma b1)
      (htof0 : Basis.tof b0 = .space s0)
      (htof1 : Basis.tof b1 = .space s1)
      (hw : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))),
      CheckedFreeStdExecutableBasisDepth Psi0 depth
        (.proj_coimg hb0 hb1 htof0 htof1 hw) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
      CheckedExactLookupStore Gamma Psi ->
      Basis.IsSpaceBasis b0 -> Basis.IsSpaceBasis b1 ->
      (exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0))) ->
      (exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) ->
      exists env, C.Cob Gamma Psi (.proj (.coimg s0 s1 e) b0 b1) env
        (Basis.std (Basis.tof (.proj (.coimg s0 s1 e) b0 b1)))
  image :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
      {s0 s1 : Space} {e : Term}
      (hb : Basis.BasisValid Gamma b)
      (hsof : Basis.sof b = .coker s0 s1 e)
      (hw : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))),
      CheckedFreeStdExecutableBasisDepth Psi0 depth (.image hb hsof hw) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
      CheckedExactLookupStore Gamma Psi ->
      Basis.IsSpaceBasis b ->
      (exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) ->
      exists env, C.Cob Gamma Psi (.image b) env
        (Basis.std (Basis.tof (.image b)))
  terms :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s : Space}
      {es : List Term} {b : Basis}
      (hb : Basis.BasisValid Gamma b)
      (htof : Basis.tof b = .space s)
      (hsv : Nonempty (SValid Gamma s))
      (hall : forall e, e ∈ es ->
        Nonempty (HasType (∅ : LCtx) Gamma e (.space s)))
      (hne : es ≠ []),
      CheckedFreeStdExecutableBasisDepth Psi0 depth
        (.terms hb htof hsv hall hne) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
      CheckedExactLookupStore Gamma Psi ->
      Basis.IsSpaceBasis b ->
      (exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) ->
      exists env, C.Cob Gamma Psi (.terms s es b) env
        (Basis.std (Basis.tof (.terms s es b)))

/-! ## Concrete source-crossing arms -/

private theorem checkedFreeStdCob_image_arm_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    {s0 s1 : Space} {e : Term}
    (hb : Basis.BasisValid Gamma b)
    (hsof : Basis.sof b = .coker s0 s1 e)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth
      (.image hb hsof hw))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hsb : Basis.IsSpaceBasis b)
    (ih : exists env, C.Cob Gamma Psi b env
      (Basis.std (Basis.tof b))) :
    exists env, C.Cob Gamma Psi (.image b) env
      (Basis.std (Basis.tof (.image b))) := by
  obtain ⟨s0', s1', e', hb', hsof', sideB,
    ⟨ht, hfreeT, ⟨sideT⟩⟩⟩ := executableImageParts side
  have heq : Space.coker s0' s1' e' = .coker s0 s1 e :=
    hsof'.symm.trans hsof
  cases heq
  obtain ⟨hc, hfreeC, ⟨sideC⟩⟩ :=
    executableCheckedSofWitness sideB hsb
  have pc : exists hc0 : SValid Gamma (.coker s0 s1 e),
      Graded.SPromotionFree hc0 /\
      Nonempty (CheckedLocalSideSWith
        (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hc0) := by
    rw [← hsof]
    exact ⟨hc, hfreeC, ⟨sideC⟩⟩
  obtain ⟨hc0, hfreeC0, ⟨sideC0⟩⟩ := pc
  cases hc0 with
  | coker hs0 hs1 hwt0 =>
      obtain ⟨hfree0, hfree1, _hfreeWt0⟩ := hfreeC0
      have sideS0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          sideC0.shallow.descendants.1 sideC0.deep.1
      have sideS1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          sideC0.shallow.descendants.2.1 sideC0.deep.2.1
      obtain ⟨sv0, hsv0⟩ := checkedSpace_of_storeTermProgressDepth progress
        hfree0 sideS0 hfuture hP hcov hstored hwf anchors
      obtain ⟨sv1, hsv1⟩ := checkedSpace_of_storeTermProgressDepth progress
        hfree1 sideS1 hfuture hP hcov hstored hwf anchors
      obtain ⟨v, tauv, hev0⟩ := progress ht hfreeT sideT
        hfuture hP hcov hstored hwf anchors
      obtain ⟨v', hsvb, hev⟩ := checked_ffs_witness
        hs0 hs1 hsv0 hsv1 hev0
      let svc : ValSpace :=
        .ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v' (.tprod sv0 sv1))
      let svi : ValSpace :=
        .ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v' (.tprod sv0 sv1))
      have hcokerSpace : C.Space Gamma Psi (.coker s0 s1 e) svc :=
        .coker ⟨.coker hs0 hs1 ht⟩ (Basis.sof_stdSpace _)
          ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
          hsvb hev
      have himgSpace : C.Space Gamma Psi (.img s0 s1 e) svi :=
        .img ⟨.img hs0 hs1 ht⟩ (Basis.sof_stdSpace _)
          ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
          hsvb hev
      obtain ⟨envc, hc0⟩ := ih
      have hc : C.Cob Gamma Psi b envc
          (Basis.stdSpace (.coker s0 s1 e)) := by
        have hc' := checkedCob_stdSpace_of_stdTof hsb hc0
        simpa only [hsof] using hc'
      have hstd0 : Basis.BasisValid Gamma (Basis.stdSpace s0) :=
        Basis.stdSpace_valid s0 hs0
      have hstd1 : Basis.BasisValid Gamma (Basis.stdSpace s1) :=
        Basis.stdSpace_valid s1 hs1
      have hstdCoker : Basis.BasisValid Gamma
          (Basis.stdSpace (.coker s0 s1 e)) :=
        Basis.stdSpace_valid _ (.coker hs0 hs1 ht)
      have hsource : Basis.BasisValid Gamma (.image b) :=
        .image hb hsof ⟨ht⟩
      have hmid : Basis.BasisValid Gamma
          (.image (Basis.stdSpace (.coker s0 s1 e))) :=
        .image hstdCoker (Basis.sof_stdSpace _) ⟨ht⟩
      have htarget : Basis.BasisValid Gamma
          (.proj (.img s0 s1 e) (Basis.stdSpace s0) (Basis.stdSpace s1)) :=
        .proj_img hstd0 hstd1 (Basis.tof_stdSpace s0)
          (Basis.tof_stdSpace s1) ⟨ht⟩
      have hstep1 : C.Cob Gamma Psi (.image b) envc
          (.image (Basis.stdSpace (.coker s0 s1 e))) :=
        .image hsource hmid ⟨s0, s1, e, hsof⟩ hc
      have hstep2 : C.Cob Gamma Psi
          (.image (Basis.stdSpace (.coker s0 s1 e)))
          (ValExpr.reshap (.imageCoords (.tprod sv0 sv1) v')
            (.space (.tprod svc svi))
            (.space (ValExpr.inferSpaceCtx [] (.imageCoords (.tprod sv0 sv1) v'))))
          (.proj (.img s0 s1 e) (Basis.stdSpace s0)
            (Basis.stdSpace s1)) := by
        simpa only [Basis.stdSpace, Basis.sof_stdSpace, svc, svi] using
          C.Cob.image_svds hmid htarget
            (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
            (Basis.isStd_stdSpace s0) (Basis.isStd_stdSpace s1) hsvb hev
      have hsourceRealized : C.Space Gamma Psi (Basis.sof (.image b)) svi := by
        simpa only [Basis.sof, hsof] using himgSpace
      have htrans := C.Cob.trans hsource htarget hstep1 hstep2
        hsourceRealized
      have hex : exists env, C.Cob Gamma Psi (.image b) env
          (Basis.stdSpace (Basis.sof (.image b))) :=
        ⟨_, by simpa only [Basis.stdSpace, Basis.sof, hsof] using htrans⟩
      obtain ⟨out, hout⟩ := hex
      exact ⟨out, checkedCob_stdTof_of_stdSpace hsb hout⟩

private def executableSideDsumE
    {Psi0 : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    {s0 s1 : Space} {e0 e1 : Term}
    {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht0 : HasType Delta Gamma e0 (.space s0)}
    {ht1 : HasType Delta Gamma e1 (.space s1)}
    (sideS0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (sideS1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (side0 : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht0)
    (side1 : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht1) :
    CheckedLocalSideBasesWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.dsumE hs0 hs1 ht0 ht1) :=
  CheckedLocalSideBasesWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, sideS0.shallow.descendants⟩,
      ⟨⟨trivial, sideS1.shallow.descendants⟩,
        ⟨⟨side0.shallow.here, side0.shallow.descendants⟩,
          ⟨side1.shallow.here, side1.shallow.descendants⟩⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, sideS0.deep⟩,
      ⟨⟨trivial, sideS1.deep⟩,
        ⟨⟨side0.deepHere, side0.deepDescendants⟩,
          ⟨side1.deepHere, side1.deepDescendants⟩⟩⟩⟩⟩

private theorem checkedHasTypeDsumChainExecutableGo
    {Psi0 : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    {s : Space} (hs : SValid Gamma s)
    (hfreeS : Graded.SPromotionFree hs)
    (sideS : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs)
    (es : List Term) :
    forall (t : Space) (e0 : Term) (ht : SValid Gamma t)
      (hfreeT : Graded.SPromotionFree ht)
      (sideT : CheckedLocalSideSWith
        (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht)
      (he0 : HasType Delta Gamma e0 (.space t))
      (hfreeE0 : Graded.PromotionFree he0)
      (sideE0 : CheckedLocalSideBasesWith
        (CheckedFreeStdSelectedAt Psi0 depth) Psi0 he0),
      (forall e, e ∈ es ->
        CheckedFreeStdExecutableTermWitness
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 Delta Gamma e
            (.space s)) ->
      exists hout : HasType Delta Gamma (Term.dsumChain e0 es)
          (.space (es.foldl (fun u _ => Space.dsum u s) t)),
        Graded.PromotionFree hout /\
        Nonempty (CheckedLocalSideBasesWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hout) := by
  induction es with
  | nil =>
      intro t e0 ht hfreeT sideT he0 hfreeE0 sideE0 _hall
      exact ⟨he0, hfreeE0, ⟨sideE0⟩⟩
  | cons a as ih =>
      intro t e0 ht hfreeT sideT he0 hfreeE0 sideE0 hall
      obtain ⟨ha, hfreeA, ⟨sideA⟩⟩ := hall a List.mem_cons_self
      let hpair : HasType Delta Gamma (.dsumE e0 a)
          (.space (.dsum t s)) := .dsumE ht hs he0 ha
      have hfreePair : Graded.PromotionFree hpair := by
        dsimp only [hpair]
        exact ⟨hfreeT, hfreeS, hfreeE0, hfreeA⟩
      have sidePair : CheckedLocalSideBasesWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hpair := by
        dsimp only [hpair]
        exact executableSideDsumE sideT sideS sideE0 sideA
      exact ih (.dsum t s) (.dsumE e0 a) (.dsum ht hs)
        ⟨hfreeT, hfreeS⟩ (executableSideDsum sideT sideS)
        hpair hfreePair sidePair
        (fun e he => hall e (List.mem_cons_of_mem a he))

private theorem foldlDsumChain_store (s : Space) :
    forall (es : List Term) (m : Nat),
      es.foldl (fun t _ => Space.dsum t s) (Space.dsumChain s m) =
        Space.dsumChain s (m + es.length)
  | [], m => by simp
  | _a :: as, m => by
      simp only [List.foldl_cons, List.length_cons]
      have hshift : Space.dsum (Space.dsumChain s m) s =
          Space.dsumChain s (m + 1) := rfl
      rw [hshift, foldlDsumChain_store s as (m + 1)]
      congr 1
      omega

private theorem checkedHasTypeDsumChainExecutable
    {Psi0 : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    {s : Space} {e0 : Term} {es : List Term}
    (hs : SValid Gamma s) (hfreeS : Graded.SPromotionFree hs)
    (sideS : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs)
    (hall : forall e, e ∈ (e0 :: es) ->
      CheckedFreeStdExecutableTermWitness
        (CheckedFreeStdSelectedAt Psi0 depth) Psi0 Delta Gamma e
          (.space s)) :
    exists hout : HasType Delta Gamma (Term.dsumChain e0 es)
        (.space (es.foldl (fun u _ => Space.dsum u s) s)),
      Graded.PromotionFree hout /\
      Nonempty (CheckedLocalSideBasesWith
        (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hout) := by
  obtain ⟨he0, hfreeE0, ⟨sideE0⟩⟩ := hall e0 List.mem_cons_self
  exact checkedHasTypeDsumChainExecutableGo hs hfreeS sideS es
    s e0 hs hfreeS sideS he0 hfreeE0 sideE0
    (fun e he => hall e (List.mem_cons_of_mem e0 he))

private def executableSideSDsumChain
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s : Space}
    {hs : SValid Gamma s}
    (side : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs) :
    forall m, CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 (sValid_dsumChain hs m)
  | 0 => side
  | m + 1 => executableSideDsum (executableSideSDsumChain side m) side

private theorem sPromotionFree_dsumChain
    {Gamma : NLCtx} {s : Space} {hs : SValid Gamma s}
    (hfree : Graded.SPromotionFree hs) :
    forall m, Graded.SPromotionFree (sValid_dsumChain hs m)
  | 0 => hfree
  | m + 1 => ⟨sPromotionFree_dsumChain hfree m, hfree⟩

private theorem checkedFreeStdCob_terms_arm_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {s : Space}
    {es : List Term} {b : Basis}
    (hb : Basis.BasisValid Gamma b) (htof : Basis.tof b = .space s)
    (hsv : Nonempty (SValid Gamma s))
    (hall : forall e, e ∈ es ->
      Nonempty (HasType (∅ : LCtx) Gamma e (.space s)))
    (hne : es ≠ [])
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth
      (.terms hb htof hsv hall hne))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hsb : Basis.IsSpaceBasis b)
    (ih : exists env, C.Cob Gamma Psi b env
      (Basis.std (Basis.tof b))) :
    exists env, C.Cob Gamma Psi (.terms s es b) env
      (Basis.std (Basis.tof (.terms s es b))) := by
  obtain ⟨e0, es', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨⟨hb', sideB⟩, hsof',
    ⟨hs, hfreeS, ⟨sideS⟩⟩, termSides⟩ := executableTermsParts side
  subst s
  obtain ⟨envc, hc0⟩ := ih
  have hc : C.Cob Gamma Psi b envc (Basis.stdSpace (Basis.sof b)) :=
    checkedCob_stdSpace_of_stdTof hsb hc0
  obtain ⟨sv, hspace⟩ := checkedSpace_of_storeTermProgressDepth progress
    hfreeS sideS hfuture hP hcov hstored hwf anchors
  obtain ⟨envChain, hchainConv0⟩ :=
    checkedCob_dsumChain_toStdSpace hb hsb hc es'.length
  have hchainConv : C.Cob Gamma Psi (Basis.dsumChain b es'.length) envChain
      (Basis.stdSpace (Space.dsumChain (Basis.sof b) es'.length)) := by
    simpa only [Basis.sof_dsumChain] using hchainConv0
  have hchainValid := basisValid_dsumChain hb hsb es'.length
  have hchainSpace := Basis.IsSpaceBasis.dsumChain hsb es'.length
  let hchainSValid := sValid_dsumChain hs es'.length
  have sideChainS : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hchainSValid := by
    dsimp only [hchainSValid]
    exact executableSideSDsumChain sideS es'.length
  have hfreeChainS : Graded.SPromotionFree hchainSValid := by
    dsimp only [hchainSValid]
    exact sPromotionFree_dsumChain hfreeS es'.length
  obtain ⟨svChain, hsvChain⟩ := checkedSpace_of_storeTermProgressDepth progress
    hfreeChainS sideChainS hfuture hP hcov hstored hwf anchors
  have hchainSof : Basis.sof (Basis.dsumChain b es'.length) =
      Space.dsumChain (Basis.sof b) es'.length := Basis.sof_dsumChain _ _
  obtain ⟨htChain, hfreeChain, ⟨sideChain⟩⟩ :=
    checkedHasTypeDsumChainExecutable hs hfreeS sideS
      (fun e he => termSides e he)
  have hfold : es'.foldl (fun t _ => Space.dsum t (Basis.sof b))
      (Basis.sof b) = Space.dsumChain (Basis.sof b) es'.length := by
    simpa only [Space.dsumChain, Nat.zero_add] using
      foldlDsumChain_store (Basis.sof b) es' 0
  have hchainConvFold : C.Cob Gamma Psi (Basis.dsumChain b es'.length)
      envChain (Basis.stdSpace
        (es'.foldl (fun t _ => Space.dsum t (Basis.sof b))
          (Basis.sof b))) := by
    rw [hfold]
    exact hchainConv
  have hsvChainFold : C.Space Gamma Psi
      (es'.foldl (fun t _ => Space.dsum t (Basis.sof b)) (Basis.sof b))
      svChain := by
    rw [hfold]
    exact hsvChain
  have hchainSofFold : Basis.sof (Basis.dsumChain b es'.length) =
      es'.foldl (fun t _ => Space.dsum t (Basis.sof b)) (Basis.sof b) :=
    hchainSof.trans hfold.symm
  obtain ⟨chainValue, hchain⟩ := checkedTerm_at_spaceBasis_storeDepth
    progress htChain hfreeChain sideChain hfuture hP hcov hstored hwf
    anchors hchainValid hchainSpace hchainSofFold hchainConvFold
    hsvChainFold
  have hstdValid : Basis.BasisValid Gamma (Basis.stdSpace (Basis.sof b)) :=
    Basis.stdSpace_valid _ hs
  have hall' : forall e, e ∈ (e0 :: es') ->
      Nonempty (HasType (∅ : LCtx) Gamma e (.space (Basis.sof b))) := by
    intro e he
    obtain ⟨ht, _⟩ := termSides e he
    exact ⟨ht⟩
  have hwhole : Basis.BasisValid Gamma
      (.terms (Basis.sof b) (e0 :: es') b) :=
    .terms hb hsb.tof_eq ⟨hs⟩ hall' (by simp)
  have hinv : C.Cob Gamma Psi (Basis.stdSpace (Basis.sof b)) (.inv envc) b :=
    .inverse hstdValid hb hc
  have hspaceStd : C.Space Gamma Psi
      (Basis.sof (Basis.stdSpace (Basis.sof b))) sv := by
    simpa only [Basis.sof_stdSpace] using hspace
  have hforward : C.Cob Gamma Psi (Basis.stdSpace (Basis.sof b))
      (ValExpr.reshapBase
        (.rrefRep chainValue
          (ValExpr.reshapBase (.inv envc) (.tprod sv sv)))
        (.tprod sv sv))
      (.terms (Basis.sof b) (e0 :: es') b) :=
    C.Cob.terms_rref hstdValid hwhole hinv hchain hspaceStd
  have hresult : C.Cob Gamma Psi (.terms (Basis.sof b) (e0 :: es') b)
      (.inv (ValExpr.reshapBase
        (.rrefRep chainValue
          (ValExpr.reshapBase (.inv envc) (.tprod sv sv)))
        (.tprod sv sv)))
      (Basis.stdSpace (Basis.sof b)) :=
    .inverse hwhole hstdValid hforward
  exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨by simp, hsb⟩ (by
    simpa only [Basis.sof] using hresult)⟩

private def executableSideEmbed
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {hsub : SubType Gamma s0 s1}
    (sideSub : CheckedLocalSideSubWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsub) :
    CheckedLocalSideBasesWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (HasType.embed hsub) :=
  CheckedLocalSideBasesWith.ofBelowPair
    ⟨trivial, ⟨trivial, sideSub.shallow.descendants⟩⟩
    ⟨trivial, ⟨trivial, sideSub.deep⟩⟩

private def executableSideLproj
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {sSub sAmb : Space}
    {hsSub : SValid Gamma sSub} {hsAmb : SValid Gamma sAmb}
    {hsub : SubType Gamma sSub sAmb}
    (sideSubS : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsSub)
    (sideAmbS : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsAmb)
    (sideSub : CheckedLocalSideSubWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsub) :
    CheckedLocalSideBasesWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (HasType.lproj hsSub hsAmb hsub) := by
  let sideE := executableSideEmbed sideSub
  exact CheckedLocalSideBasesWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, sideSubS.shallow.descendants⟩,
      ⟨⟨trivial, sideAmbS.shallow.descendants⟩,
        ⟨sideE.shallow.here, sideE.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, sideSubS.deep⟩,
      ⟨⟨trivial, sideAmbS.deep⟩,
        ⟨sideE.deepHere, sideE.deepDescendants⟩⟩⟩⟩

private def executableSideSubKer
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (side1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (sideT : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht) :
    CheckedLocalSideSubWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.sub_ker hs0 hs1 ht) :=
  CheckedLocalSideSubWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def executableSideSubCoker
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (side1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (sideT : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht) :
    CheckedLocalSideSubWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.sub_coker hs0 hs1 ht) :=
  CheckedLocalSideSubWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def executableSideSubImg
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (side1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (sideT : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht) :
    CheckedLocalSideSubWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.sub_img hs0 hs1 ht) :=
  CheckedLocalSideSubWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def executableSideSubCoimg
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (side1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (sideT : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 ht) :
    CheckedLocalSideSubWith (CheckedFreeStdSelectedAt Psi0 depth) Psi0
      (.sub_coimg hs0 hs1 ht) :=
  CheckedLocalSideSubWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private theorem checkedFreeStdCob_proj_dom_arm_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 : Basis}
    (hsOr : s = .ker s0 s1 e ∨ s = .coker s0 s1 e)
    (hsS : SValid Gamma s) (hfreeS : Graded.SPromotionFree hsS)
    (sideS : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsS)
    (hsub : SubType Gamma s s0)
    (hfreeSub : Graded.SubPromotionFree hsub)
    (sideSub : CheckedLocalSideSubWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsub)
    (hs0 : SValid Gamma s0) (hfree0 : Graded.SPromotionFree hs0)
    (sideS0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (hs1 : SValid Gamma s1) (hfree1 : Graded.SPromotionFree hs1)
    (sideS1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (hwt : HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1)))
    (hfreeT : Graded.PromotionFree hwt)
    (sideT : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hwt)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj s b0 b1) env
      (Basis.std (Basis.tof (.proj s b0 b1))) := by
  have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
  have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
  have hstdS : Basis.stdSpace s =
      .proj s (Basis.stdSpace s0) (Basis.stdSpace s1) := by
    rcases hsOr with rfl | rfl <;> rfl
  obtain ⟨sv0, hsv0⟩ := checkedSpace_of_storeTermProgressDepth progress
    hfree0 sideS0 hfuture hP hcov hstored hwf anchors
  obtain ⟨sv1, hsv1⟩ := checkedSpace_of_storeTermProgressDepth progress
    hfree1 sideS1 hfuture hP hcov hstored hwf anchors
  obtain ⟨env0, hc00⟩ := ih0
  obtain ⟨env1, hc10⟩ := ih1
  have hc0 : C.Cob Gamma Psi b0 env0 (Basis.stdSpace s0) := by
    have h := checkedCob_stdSpace_of_stdTof hsb0 hc00
    simpa only [hsof0] using h
  have hc1 : C.Cob Gamma Psi b1 env1 (Basis.stdSpace s1) := by
    have h := checkedCob_stdSpace_of_stdTof hsb1 hc10
    simpa only [hsof1] using h
  let refl0 := checkedCob_refl_stdSpace hs0 hsv0
  let refl1 := checkedCob_refl_stdSpace hs1 hsv1
  obtain ⟨vi0, hi0⟩ := checkedInner_at_spaceBasis_storeDepth progress
    hfree0 sideS0 hfuture hP hcov hstored hwf anchors
    hb0 hsb0 hsof0 hc0 hsv0
  obtain ⟨vi1, hi1⟩ := checkedInner_at_spaceBasis_storeDepth progress
    hfree1 sideS1 hfuture hP hcov hstored hwf anchors
    hb1 hsb1 hsof1 hc1 hsv1
  have hi0std := checked_inner_at hs0 hsv0
  have hi1std := checked_inner_at hs1 hsv1
  have hstd0 : Basis.BasisValid Gamma (Basis.stdSpace s0) :=
    Basis.stdSpace_valid s0 hs0
  have hstd1 : Basis.BasisValid Gamma (Basis.stdSpace s1) :=
    Basis.stdSpace_valid s1 hs1
  obtain ⟨ve1, he1⟩ := checkedMapTerm_at_bases_storeDepth progress
    hwt hfreeT sideT hfuture hP hcov hstored hwf anchors
    hb0 hb1 hsb0 hsb1 hsof0 hsof1 hc0 hc1 hsv0 hsv1
  obtain ⟨ve2, he2⟩ := checkedMapTerm_at_bases_storeDepth progress
    hwt hfreeT sideT hfuture hP hcov hstored hwf anchors
    hb0 hstd1 hsb0 (Basis.isSpaceBasis_stdSpace s1)
    hsof0 (Basis.sof_stdSpace s1) hc0 refl1 hsv0 hsv1
  obtain ⟨ve3, he3⟩ := checkedMapTerm_at_bases_storeDepth progress
    hwt hfreeT sideT hfuture hP hcov hstored hwf anchors
    hstd0 hstd1 (Basis.isSpaceBasis_stdSpace s0)
    (Basis.isSpaceBasis_stdSpace s1)
    (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    refl0 refl1 hsv0 hsv1
  obtain ⟨svS3, em3, hS3, hem3⟩ := checkedEmbed_domside hsOr
    hstd0 hstd1 (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    hs0 hs1 hwt hsv0 hsv1 hi0std hi1std he3
  have hP3 : Basis.BasisValid Gamma
      (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) := by
    rcases hsOr with rfl | rfl
    · exact .proj_ker hstd0 hstd1 (Basis.tof_stdSpace s0)
        (Basis.tof_stdSpace s1) ⟨hwt⟩
    · exact .proj_coker hstd0 hstd1 (Basis.tof_stdSpace s0)
        (Basis.tof_stdSpace s1) ⟨hwt⟩
  have hprojOutValid : Basis.BasisValid Gamma
      (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))) :=
    .tprod (.dual hstd0 (Basis.isSpaceBasis_stdSpace s0).tof_eq) hP3 rfl rfl
  have hsvProjOut : C.Space Gamma Psi (.tprod (.dual s0) s)
      (.tprod sv0 svS3) :=
    .tprod ⟨.tprod (.dual hs0) hsS⟩ (.dual ⟨.dual hs0⟩ hsv0) hS3
  have htyProjOut : C.TyAt Gamma Psi
      (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.space (.tprod sv0 svS3)) :=
    .space rfl hprojOutValid (by
      simpa only [Basis.sof, Basis.sof_stdSpace] using hsvProjOut)
  have htProjOut : Nonempty (HasType (∅ : LCtx) Gamma
      (Term.lproj s s0)
      (Basis.tof (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType (∅ : LCtx) Gamma (Term.lproj s s0)
        (.space (.tprod (.dual s0) s))) from
        ⟨HasType.lproj hsS hs0 hsub⟩)
  have htProjRaw : Nonempty (HasType (∅ : LCtx) Gamma
      (.pinvT
        (Basis.sof (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
        (Basis.sof (Basis.stdSpace s0)) (Term.lembd s))
      (Basis.tof (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))))) := by
    simpa only [Term.lproj, Basis.sof, Basis.sof_stdSpace] using htProjOut
  have hp3raw := C.Term.pinvT_std
    (b₀ := Basis.stdSpace s0)
    (b₁ := .proj s (Basis.stdSpace s0) (Basis.stdSpace s1))
    (Basis.isStd_stdSpace s0)
    (show Basis.isStd (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) from
      ⟨Basis.isStd_stdSpace s0, Basis.isStd_stdSpace s1⟩)
    htProjRaw hprojOutValid htyProjOut hem3
  have hp3 : C.Term (∅ : LCtx) Gamma Psi (Term.lproj s s0)
      (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.pinv em3) (.space (.tprod sv0 svS3)) := by
    simpa only [Term.lproj, Basis.sof, Basis.sof_stdSpace] using hp3raw
  obtain ⟨svS2, em2, hS2, hem2⟩ := checkedEmbed_domside hsOr
    hb0 hstd1 hsof0 (Basis.sof_stdSpace s1)
    hs0 hs1 hwt hsv0 hsv1 hi0 hi1std he2
  have hP2 : Basis.BasisValid Gamma
      (.proj s b0 (Basis.stdSpace s1)) := by
    rcases hsOr with rfl | rfl
    · exact .proj_ker hb0 hstd1 htof0 (Basis.tof_stdSpace s1) ⟨hwt⟩
    · exact .proj_coker hb0 hstd1 htof0 (Basis.tof_stdSpace s1) ⟨hwt⟩
  have hspaceB0 : C.Space Gamma Psi (Basis.sof b0) sv0 := by
    simpa only [hsof0] using hsv0
  have hspaceStd0 : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s0)) sv0 := by
    simpa only [Basis.sof_stdSpace] using hsv0
  have hspaceStd1 : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s1)) sv1 := by
    simpa only [Basis.sof_stdSpace] using hsv1
  have hp3' : C.Term (∅ : LCtx) Gamma Psi
      (Term.lproj s (Basis.sof (Basis.stdSpace s0)))
      (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.pinv em3) (.space (.tprod sv0 svS3)) := by
    simpa only [Basis.sof_stdSpace] using hp3
  have hC2raw := C.Cob.proj_ker_coker hP2 hP3 hsOr hsof0
    (Basis.sof_stdSpace s1) hspaceB0 hspaceStd1 hS2 hS3 hspaceStd0
    hc0 hem2 hp3'
  have hC2 : C.Cob Gamma Psi (.proj s b0 (Basis.stdSpace s1)) _
      (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) := hC2raw
  obtain ⟨svS1, em1, hS1, hem1⟩ := checkedEmbed_domside hsOr
    hb0 hb1 hsof0 hsof1 hs0 hs1 hwt hsv0 hsv1 hi0 hi1 he1
  have hP1 : Basis.BasisValid Gamma (.proj s b0 b1) := by
    rcases hsOr with rfl | rfl
    · exact .proj_ker hb0 hb1 htof0 htof1 ⟨hwt⟩
    · exact .proj_coker hb0 hb1 htof0 htof1 ⟨hwt⟩
  have hC2stdExists : exists env,
      C.Cob Gamma Psi (.proj s b0 (Basis.stdSpace s1)) env
        (Basis.stdSpace s) :=
    ⟨_, by simpa only [hstdS] using hC2⟩
  obtain ⟨envP2, hC2std⟩ := hC2stdExists
  obtain ⟨envMix, hMixConv0⟩ := checkedCob_tprod_dual
    hb0 hP2 hsb0 ⟨hsb0, Basis.isSpaceBasis_stdSpace s1⟩
    hsof0 rfl hc0 hC2std
  have hMixConv : C.Cob Gamma Psi
      (.tprod (.dual b0) (.proj s b0 (Basis.stdSpace s1))) envMix
      (Basis.stdSpace (.tprod (.dual s0) s)) := by
    simpa only [Basis.stdSpace] using hMixConv0
  have hMixValid : Basis.BasisValid Gamma
      (.tprod (.dual b0) (.proj s b0 (Basis.stdSpace s1))) :=
    .tprod (.dual hb0 hsb0.tof_eq) hP2 rfl rfl
  have hMixSof : Basis.sof
      (.tprod (.dual b0) (.proj s b0 (Basis.stdSpace s1))) =
      .tprod (.dual s0) s := by simp only [Basis.sof, hsof0]
  have hMixSpace : C.Space Gamma Psi (.tprod (.dual s0) s)
      (.tprod sv0 svS2) :=
    .tprod ⟨.tprod (.dual hs0) hsS⟩ (.dual ⟨.dual hs0⟩ hsv0) hS2
  have hfreeLproj : Graded.PromotionFree (HasType.lproj hsS hs0 hsub) :=
    ⟨hfreeS, hfree0, hfreeSub⟩
  obtain ⟨pmix, hpmix⟩ := checkedTerm_at_spaceBasis_storeDepth progress
    (HasType.lproj hsS hs0 hsub) hfreeLproj
    (executableSideLproj sideS sideS0 sideSub)
    hfuture hP hcov hstored hwf anchors hMixValid
    ⟨hsb0, ⟨hsb0, Basis.isSpaceBasis_stdSpace s1⟩⟩
    hMixSof hMixConv hMixSpace
  have hspaceP1 : C.Space Gamma Psi (Basis.sof (.proj s b0 b1)) svS1 := by
    simpa only [Basis.sof] using hS1
  have hpmix' : C.Term (∅ : LCtx) Gamma Psi
      (Term.lproj s (Basis.sof b0))
      (.tprod (.dual b0) (.proj s b0 (Basis.stdSpace s1)))
      pmix (.space (.tprod sv0 svS2)) := by
    simpa only [hsof0] using hpmix
  have hC1 := C.Cob.proj_ker_coker_cod hP1 hP2 hsOr hsof0 hsof1
    (Basis.sof_stdSpace s1) hspaceB0 hS1 hS2 hem1 hpmix'
  have htrans := C.Cob.trans hP1 hP3 hC1 hC2 hspaceP1
  have htoStdSpace : exists env, C.Cob Gamma Psi (.proj s b0 b1) env
      (Basis.stdSpace (Basis.sof (.proj s b0 b1))) :=
    ⟨_, by simpa only [Basis.sof, hstdS] using htrans⟩
  obtain ⟨out, hout⟩ := htoStdSpace
  exact ⟨out, checkedCob_stdTof_of_stdSpace ⟨hsb0, hsb1⟩ hout⟩

private theorem checkedFreeStdCob_proj_cod_arm_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 : Basis}
    (hsOr : s = .img s0 s1 e ∨ s = .coimg s0 s1 e)
    (hsS : SValid Gamma s) (hfreeS : Graded.SPromotionFree hsS)
    (sideS : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsS)
    (hsub : SubType Gamma s s1)
    (hfreeSub : Graded.SubPromotionFree hsub)
    (sideSub : CheckedLocalSideSubWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsub)
    (hs0 : SValid Gamma s0) (hfree0 : Graded.SPromotionFree hs0)
    (sideS0 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0)
    (hs1 : SValid Gamma s1) (hfree1 : Graded.SPromotionFree hs1)
    (sideS1 : CheckedLocalSideSWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1)
    (hwt : HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1)))
    (hfreeT : Graded.PromotionFree hwt)
    (sideT : CheckedLocalSideBasesWith
      (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hwt)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj s b0 b1) env
      (Basis.std (Basis.tof (.proj s b0 b1))) := by
  have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
  have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
  have hstdS : Basis.stdSpace s =
      .proj s (Basis.stdSpace s0) (Basis.stdSpace s1) := by
    rcases hsOr with rfl | rfl <;> rfl
  obtain ⟨sv0, hsv0⟩ := checkedSpace_of_storeTermProgressDepth progress
    hfree0 sideS0 hfuture hP hcov hstored hwf anchors
  obtain ⟨sv1, hsv1⟩ := checkedSpace_of_storeTermProgressDepth progress
    hfree1 sideS1 hfuture hP hcov hstored hwf anchors
  obtain ⟨env0, hc00⟩ := ih0
  obtain ⟨env1, hc10⟩ := ih1
  have hc0 : C.Cob Gamma Psi b0 env0 (Basis.stdSpace s0) := by
    have h := checkedCob_stdSpace_of_stdTof hsb0 hc00
    simpa only [hsof0] using h
  have hc1 : C.Cob Gamma Psi b1 env1 (Basis.stdSpace s1) := by
    have h := checkedCob_stdSpace_of_stdTof hsb1 hc10
    simpa only [hsof1] using h
  let refl0 := checkedCob_refl_stdSpace hs0 hsv0
  let refl1 := checkedCob_refl_stdSpace hs1 hsv1
  obtain ⟨vi0, hi0⟩ := checkedInner_at_spaceBasis_storeDepth progress
    hfree0 sideS0 hfuture hP hcov hstored hwf anchors
    hb0 hsb0 hsof0 hc0 hsv0
  obtain ⟨vi1, hi1⟩ := checkedInner_at_spaceBasis_storeDepth progress
    hfree1 sideS1 hfuture hP hcov hstored hwf anchors
    hb1 hsb1 hsof1 hc1 hsv1
  have hi0std := checked_inner_at hs0 hsv0
  have hi1std := checked_inner_at hs1 hsv1
  have hstd0 : Basis.BasisValid Gamma (Basis.stdSpace s0) :=
    Basis.stdSpace_valid s0 hs0
  have hstd1 : Basis.BasisValid Gamma (Basis.stdSpace s1) :=
    Basis.stdSpace_valid s1 hs1
  obtain ⟨ve1, he1⟩ := checkedMapTerm_at_bases_storeDepth progress
    hwt hfreeT sideT hfuture hP hcov hstored hwf anchors
    hb0 hb1 hsb0 hsb1 hsof0 hsof1 hc0 hc1 hsv0 hsv1
  obtain ⟨ve2, he2⟩ := checkedMapTerm_at_bases_storeDepth progress
    hwt hfreeT sideT hfuture hP hcov hstored hwf anchors
    hstd0 hb1 (Basis.isSpaceBasis_stdSpace s0) hsb1
    (Basis.sof_stdSpace s0) hsof1 refl0 hc1 hsv0 hsv1
  obtain ⟨ve3, he3⟩ := checkedMapTerm_at_bases_storeDepth progress
    hwt hfreeT sideT hfuture hP hcov hstored hwf anchors
    hstd0 hstd1 (Basis.isSpaceBasis_stdSpace s0)
    (Basis.isSpaceBasis_stdSpace s1)
    (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    refl0 refl1 hsv0 hsv1
  obtain ⟨svS3, em3, hS3, hem3⟩ := checkedEmbed_codside hsOr
    hstd0 hstd1 (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    hs0 hs1 hwt hsv0 hsv1 hi0std hi1std he3
  have hP3 : Basis.BasisValid Gamma
      (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) := by
    rcases hsOr with rfl | rfl
    · exact .proj_img hstd0 hstd1 (Basis.tof_stdSpace s0)
        (Basis.tof_stdSpace s1) ⟨hwt⟩
    · exact .proj_coimg hstd0 hstd1 (Basis.tof_stdSpace s0)
        (Basis.tof_stdSpace s1) ⟨hwt⟩
  have hprojOutValid : Basis.BasisValid Gamma
      (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))) :=
    .tprod (.dual hstd1 (Basis.isSpaceBasis_stdSpace s1).tof_eq) hP3 rfl rfl
  have hsvProjOut : C.Space Gamma Psi (.tprod (.dual s1) s)
      (.tprod sv1 svS3) :=
    .tprod ⟨.tprod (.dual hs1) hsS⟩ (.dual ⟨.dual hs1⟩ hsv1) hS3
  have htyProjOut : C.TyAt Gamma Psi
      (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.space (.tprod sv1 svS3)) :=
    .space rfl hprojOutValid (by
      simpa only [Basis.sof, Basis.sof_stdSpace] using hsvProjOut)
  have htProjOut : Nonempty (HasType (∅ : LCtx) Gamma
      (Term.lproj s s1)
      (Basis.tof (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType (∅ : LCtx) Gamma (Term.lproj s s1)
        (.space (.tprod (.dual s1) s))) from
        ⟨HasType.lproj hsS hs1 hsub⟩)
  have htProjRaw : Nonempty (HasType (∅ : LCtx) Gamma
      (.pinvT
        (Basis.sof (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
        (Basis.sof (Basis.stdSpace s1)) (Term.lembd s))
      (Basis.tof (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))))) := by
    simpa only [Term.lproj, Basis.sof, Basis.sof_stdSpace] using htProjOut
  have hp3raw := C.Term.pinvT_std
    (b₀ := Basis.stdSpace s1)
    (b₁ := .proj s (Basis.stdSpace s0) (Basis.stdSpace s1))
    (Basis.isStd_stdSpace s1)
    (show Basis.isStd (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) from
      ⟨Basis.isStd_stdSpace s0, Basis.isStd_stdSpace s1⟩)
    htProjRaw hprojOutValid htyProjOut hem3
  have hp3 : C.Term (∅ : LCtx) Gamma Psi (Term.lproj s s1)
      (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.pinv em3) (.space (.tprod sv1 svS3)) := by
    simpa only [Term.lproj, Basis.sof, Basis.sof_stdSpace] using hp3raw
  obtain ⟨svS2, em2, hS2, hem2⟩ := checkedEmbed_codside hsOr
    hstd0 hb1 (Basis.sof_stdSpace s0) hsof1
    hs0 hs1 hwt hsv0 hsv1 hi0std hi1 he2
  have hP2 : Basis.BasisValid Gamma
      (.proj s (Basis.stdSpace s0) b1) := by
    rcases hsOr with rfl | rfl
    · exact .proj_img hstd0 hb1 (Basis.tof_stdSpace s0) htof1 ⟨hwt⟩
    · exact .proj_coimg hstd0 hb1 (Basis.tof_stdSpace s0) htof1 ⟨hwt⟩
  have hspaceB1 : C.Space Gamma Psi (Basis.sof b1) sv1 := by
    simpa only [hsof1] using hsv1
  have hspaceStd0 : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s0)) sv0 := by
    simpa only [Basis.sof_stdSpace] using hsv0
  have hspaceStd1 : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s1)) sv1 := by
    simpa only [Basis.sof_stdSpace] using hsv1
  have hp3' : C.Term (∅ : LCtx) Gamma Psi
      (Term.lproj s (Basis.sof (Basis.stdSpace s1)))
      (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.pinv em3) (.space (.tprod sv1 svS3)) := by
    simpa only [Basis.sof_stdSpace] using hp3
  have hC2raw := C.Cob.proj_img_coimg hP2 hP3 hsOr
    (Basis.sof_stdSpace s0) hsof1 hspaceStd0 hspaceB1 hS2 hS3
    hspaceStd1 hc1 hem2 hp3'
  have hC2 : C.Cob Gamma Psi (.proj s (Basis.stdSpace s0) b1) _
      (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) := hC2raw
  obtain ⟨svS1, em1, hS1, hem1⟩ := checkedEmbed_codside hsOr
    hb0 hb1 hsof0 hsof1 hs0 hs1 hwt hsv0 hsv1 hi0 hi1 he1
  have hP1 : Basis.BasisValid Gamma (.proj s b0 b1) := by
    rcases hsOr with rfl | rfl
    · exact .proj_img hb0 hb1 htof0 htof1 ⟨hwt⟩
    · exact .proj_coimg hb0 hb1 htof0 htof1 ⟨hwt⟩
  have hC2stdExists : exists env,
      C.Cob Gamma Psi (.proj s (Basis.stdSpace s0) b1) env
        (Basis.stdSpace s) :=
    ⟨_, by simpa only [hstdS] using hC2⟩
  obtain ⟨envP2, hC2std⟩ := hC2stdExists
  obtain ⟨envMix, hMixConv0⟩ := checkedCob_tprod_dual
    hb1 hP2 hsb1 ⟨Basis.isSpaceBasis_stdSpace s0, hsb1⟩
    hsof1 rfl hc1 hC2std
  have hMixConv : C.Cob Gamma Psi
      (.tprod (.dual b1) (.proj s (Basis.stdSpace s0) b1)) envMix
      (Basis.stdSpace (.tprod (.dual s1) s)) := by
    simpa only [Basis.stdSpace] using hMixConv0
  have hMixValid : Basis.BasisValid Gamma
      (.tprod (.dual b1) (.proj s (Basis.stdSpace s0) b1)) :=
    .tprod (.dual hb1 hsb1.tof_eq) hP2 rfl rfl
  have hMixSof : Basis.sof
      (.tprod (.dual b1) (.proj s (Basis.stdSpace s0) b1)) =
      .tprod (.dual s1) s := by simp only [Basis.sof, hsof1]
  have hMixSpace : C.Space Gamma Psi (.tprod (.dual s1) s)
      (.tprod sv1 svS2) :=
    .tprod ⟨.tprod (.dual hs1) hsS⟩ (.dual ⟨.dual hs1⟩ hsv1) hS2
  have hfreeLproj : Graded.PromotionFree (HasType.lproj hsS hs1 hsub) :=
    ⟨hfreeS, hfree1, hfreeSub⟩
  obtain ⟨pmix, hpmix⟩ := checkedTerm_at_spaceBasis_storeDepth progress
    (HasType.lproj hsS hs1 hsub) hfreeLproj
    (executableSideLproj sideS sideS1 sideSub)
    hfuture hP hcov hstored hwf anchors hMixValid
    ⟨hsb1, ⟨Basis.isSpaceBasis_stdSpace s0, hsb1⟩⟩
    hMixSof hMixConv hMixSpace
  have hspaceP1 : C.Space Gamma Psi (Basis.sof (.proj s b0 b1)) svS1 := by
    simpa only [Basis.sof] using hS1
  have hpmix' : C.Term (∅ : LCtx) Gamma Psi
      (Term.lproj s (Basis.sof b1))
      (.tprod (.dual b1) (.proj s (Basis.stdSpace s0) b1))
      pmix (.space (.tprod sv1 svS2)) := by
    simpa only [hsof1] using hpmix
  have hC1 := C.Cob.proj_img_coimg_dom hP1 hP2 hsOr hsof0 hsof1
    (Basis.sof_stdSpace s0) hspaceB1 hS1 hS2 hem1 hpmix'
  have htrans := C.Cob.trans hP1 hP3 hC1 hC2 hspaceP1
  have htoStdSpace : exists env, C.Cob Gamma Psi (.proj s b0 b1) env
      (Basis.stdSpace (Basis.sof (.proj s b0 b1))) :=
    ⟨_, by simpa only [Basis.sof, hstdS] using htrans⟩
  obtain ⟨out, hout⟩ := htoStdSpace
  exact ⟨out, checkedCob_stdTof_of_stdSpace ⟨hsb0, hsb1⟩ hout⟩

private theorem checkedFreeStdCob_proj_ker_arm_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
    {b0 b1 : Basis}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth
      (.proj_ker hb0 hb1 htof0 htof1 hw))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj (.ker s0 s1 e) b0 b1) env
      (Basis.std (Basis.tof (.proj (.ker s0 s1 e) b0 b1))) := by
  obtain ⟨hsS, hfreeS, ⟨sideS⟩⟩ :=
    executableCheckedSofWitness side ⟨hsb0, hsb1⟩
  cases hsS with
  | ker hs0 hs1 hwt =>
      obtain ⟨hfree0, hfree1, hfreeT⟩ := hfreeS
      have sideS0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.1 sideS.deep.1
      have sideS1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.2.1 sideS.deep.2.1
      have sideT : CheckedLocalSideBasesWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hwt :=
        CheckedLocalSideBasesWith.ofBelowPair
          sideS.shallow.descendants.2.2 sideS.deep.2.2
      let hsub : SubType Gamma (.ker s0 s1 e) s0 :=
        .sub_ker hs0 hs1 hwt
      have hfreeSub : Graded.SubPromotionFree hsub := by
        dsimp only [hsub]
        exact ⟨hfree0, hfree1, hfreeT⟩
      have sideSub : CheckedLocalSideSubWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsub := by
        dsimp only [hsub]
        exact executableSideSubKer sideS0 sideS1 sideT
      exact checkedFreeStdCob_proj_dom_arm_storeDepth progress (Or.inl rfl)
        (.ker hs0 hs1 hwt) ⟨hfree0, hfree1, hfreeT⟩ sideS
        hsub hfreeSub sideSub hs0 hfree0 sideS0 hs1 hfree1 sideS1
        hwt hfreeT sideT hfuture hP hcov hstored hwf anchors
        hb0 hb1 htof0 htof1 hsb0 hsb1 ih0 ih1

private theorem checkedFreeStdCob_proj_coker_arm_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
    {b0 b1 : Basis}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth
      (.proj_coker hb0 hb1 htof0 htof1 hw))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj (.coker s0 s1 e) b0 b1) env
      (Basis.std (Basis.tof (.proj (.coker s0 s1 e) b0 b1))) := by
  obtain ⟨hsS, hfreeS, ⟨sideS⟩⟩ :=
    executableCheckedSofWitness side ⟨hsb0, hsb1⟩
  cases hsS with
  | coker hs0 hs1 hwt =>
      obtain ⟨hfree0, hfree1, hfreeT⟩ := hfreeS
      have sideS0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.1 sideS.deep.1
      have sideS1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.2.1 sideS.deep.2.1
      have sideT : CheckedLocalSideBasesWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hwt :=
        CheckedLocalSideBasesWith.ofBelowPair
          sideS.shallow.descendants.2.2 sideS.deep.2.2
      let hsub : SubType Gamma (.coker s0 s1 e) s0 :=
        .sub_coker hs0 hs1 hwt
      have hfreeSub : Graded.SubPromotionFree hsub := by
        dsimp only [hsub]
        exact ⟨hfree0, hfree1, hfreeT⟩
      have sideSub : CheckedLocalSideSubWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsub := by
        dsimp only [hsub]
        exact executableSideSubCoker sideS0 sideS1 sideT
      exact checkedFreeStdCob_proj_dom_arm_storeDepth progress (Or.inr rfl)
        (.coker hs0 hs1 hwt) ⟨hfree0, hfree1, hfreeT⟩ sideS
        hsub hfreeSub sideSub hs0 hfree0 sideS0 hs1 hfree1 sideS1
        hwt hfreeT sideT hfuture hP hcov hstored hwf anchors
        hb0 hb1 htof0 htof1 hsb0 hsb1 ih0 ih1

private theorem checkedFreeStdCob_proj_img_arm_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
    {b0 b1 : Basis}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth
      (.proj_img hb0 hb1 htof0 htof1 hw))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj (.img s0 s1 e) b0 b1) env
      (Basis.std (Basis.tof (.proj (.img s0 s1 e) b0 b1))) := by
  obtain ⟨hsS, hfreeS, ⟨sideS⟩⟩ :=
    executableCheckedSofWitness side ⟨hsb0, hsb1⟩
  cases hsS with
  | img hs0 hs1 hwt =>
      obtain ⟨hfree0, hfree1, hfreeT⟩ := hfreeS
      have sideS0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.1 sideS.deep.1
      have sideS1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.2.1 sideS.deep.2.1
      have sideT : CheckedLocalSideBasesWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hwt :=
        CheckedLocalSideBasesWith.ofBelowPair
          sideS.shallow.descendants.2.2 sideS.deep.2.2
      let hsub : SubType Gamma (.img s0 s1 e) s1 :=
        .sub_img hs0 hs1 hwt
      have hfreeSub : Graded.SubPromotionFree hsub := by
        dsimp only [hsub]
        exact ⟨hfree0, hfree1, hfreeT⟩
      have sideSub : CheckedLocalSideSubWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsub := by
        dsimp only [hsub]
        exact executableSideSubImg sideS0 sideS1 sideT
      exact checkedFreeStdCob_proj_cod_arm_storeDepth progress (Or.inl rfl)
        (.img hs0 hs1 hwt) ⟨hfree0, hfree1, hfreeT⟩ sideS
        hsub hfreeSub sideSub hs0 hfree0 sideS0 hs1 hfree1 sideS1
        hwt hfreeT sideT hfuture hP hcov hstored hwf anchors
        hb0 hb1 htof0 htof1 hsb0 hsb1 ih0 ih1

private theorem checkedFreeStdCob_proj_coimg_arm_storeDepth
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
    {b0 b1 : Basis}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (side : CheckedFreeStdExecutableBasisDepth Psi0 depth
      (.proj_coimg hb0 hb1 htof0 htof1 hw))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (anchors : CheckedExactLookupStore Gamma Psi)
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj (.coimg s0 s1 e) b0 b1) env
      (Basis.std (Basis.tof (.proj (.coimg s0 s1 e) b0 b1))) := by
  obtain ⟨hsS, hfreeS, ⟨sideS⟩⟩ :=
    executableCheckedSofWitness side ⟨hsb0, hsb1⟩
  cases hsS with
  | coimg hs0 hs1 hwt =>
      obtain ⟨hfree0, hfree1, hfreeT⟩ := hfreeS
      have sideS0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.1 sideS.deep.1
      have sideS1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.2.1 sideS.deep.2.1
      have sideT : CheckedLocalSideBasesWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hwt :=
        CheckedLocalSideBasesWith.ofBelowPair
          sideS.shallow.descendants.2.2 sideS.deep.2.2
      let hsub : SubType Gamma (.coimg s0 s1 e) s1 :=
        .sub_coimg hs0 hs1 hwt
      have hfreeSub : Graded.SubPromotionFree hsub := by
        dsimp only [hsub]
        exact ⟨hfree0, hfree1, hfreeT⟩
      have sideSub : CheckedLocalSideSubWith
          (CheckedFreeStdSelectedAt Psi0 depth) Psi0 hsub := by
        dsimp only [hsub]
        exact executableSideSubCoimg sideS0 sideS1 sideT
      exact checkedFreeStdCob_proj_cod_arm_storeDepth progress (Or.inr rfl)
        (.coimg hs0 hs1 hwt) ⟨hfree0, hfree1, hfreeT⟩ sideS
        hsub hfreeSub sideSub hs0 hfree0 sideS0 hs1 hfree1 sideS1
        hwt hfreeT sideT hfuture hP hcov hstored hwf anchors
        hb0 hb1 htof0 htof1 hsb0 hsb1 ih0 ih1

/-- All six state-threaded source-crossing obligations are constructively
discharged by the exact proof-indexed source progress callback. -/
theorem checkedFreeStdCobTermArmsDepthWithStore_of_progress
    (progress : CheckedFreeStdStoreTermProgressDepth Psi0 depth) :
    CheckedFreeStdCobTermArmsDepthWithStore Psi0 depth where
  proj_ker := checkedFreeStdCob_proj_ker_arm_storeDepth progress
  proj_coker := checkedFreeStdCob_proj_coker_arm_storeDepth progress
  proj_img := checkedFreeStdCob_proj_img_arm_storeDepth progress
  proj_coimg := checkedFreeStdCob_proj_coimg_arm_storeDepth progress
  image := checkedFreeStdCob_image_arm_storeDepth progress
  terms := checkedFreeStdCob_terms_arm_storeDepth progress

/-- Complete structural basis recursion once the six state-threaded source
arms are supplied.  No constructor changes `Gamma` or `Psi`, so the exact
lookup store is passed unchanged to structural children. -/
theorem checkedFreeStdCobToStdDepth_of_termArmsWithStore
    (Psi0 : EvalCtx) (depth : Nat)
    (arms : CheckedFreeStdCobTermArmsDepthWithStore Psi0 depth) :
    CheckedFreeStdCobToStdDepthWithStore Psi0 depth := by
  intro Gamma Psi b hb
  revert Psi
  induction hb with
  | empty =>
      intro Psi _side _hfuture _hP _hcov _hstored _hwf _anchors _hsb
      exact ⟨_, .refl .empty rfl .empty⟩
  | one =>
      intro Psi _side _hfuture _hP _hcov _hstored _hwf _anchors _hsb
      exact ⟨_, .refl .one rfl .real⟩
  | @dual Gamma b hb htof ih =>
      intro Psi side hfuture hP hcov hstored hwf anchors hsb
      obtain ⟨hb', side'⟩ := executableDualChild side
      obtain ⟨env, henv⟩ :=
        ih side' hfuture hP hcov hstored hwf anchors hsb
      exact ⟨_, by
        simpa only [Basis.std, Basis.tof, Basis.sof] using
          checkedCob_dual_toStdSpace hb hsb henv⟩
  | @dsum Gamma b0 b1 hb0 hb1 htof0 htof1 ih0 ih1 =>
      intro Psi side hfuture hP hcov hstored hwf anchors hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩⟩ := executableDsumChildren side
      obtain ⟨hs0, hs1⟩ := hsb
      obtain ⟨env0, h0⟩ :=
        ih0 side0 hfuture hP hcov hstored hwf anchors hs0
      obtain ⟨env1, h1⟩ :=
        ih1 side1 hfuture hP hcov hstored hwf anchors hs1
      have h0' := checkedCob_stdSpace_of_stdTof hs0 h0
      have h1' := checkedCob_stdSpace_of_stdTof hs1 h1
      exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hs0, hs1⟩
        (checkedCob_dsum_toStdSpace hb0 hb1 hs0 hs1 h0' h1')⟩
  | @tprod Gamma b0 b1 hb0 hb1 htof0 htof1 ih0 ih1 =>
      intro Psi side hfuture hP hcov hstored hwf anchors hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩⟩ := executableTprodChildren side
      obtain ⟨hs0, hs1⟩ := hsb
      obtain ⟨env0, h0⟩ :=
        ih0 side0 hfuture hP hcov hstored hwf anchors hs0
      obtain ⟨env1, h1⟩ :=
        ih1 side1 hfuture hP hcov hstored hwf anchors hs1
      have h0' := checkedCob_stdSpace_of_stdTof hs0 h0
      have h1' := checkedCob_stdSpace_of_stdTof hs1 h1
      exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hs0, hs1⟩
        (checkedCob_tprod_toStdSpace hb0 hb1 hs0 hs1 h0' h1')⟩
  | @proj_ker Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro Psi side hfuture hP hcov hstored hwf anchors hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, _⟩ :=
        executableProjKerParts side
      exact arms.proj_ker hb0 hb1 htof0 htof1 hw side hfuture hP hcov
        hstored hwf anchors hsb.1 hsb.2
        (ih0 side0 hfuture hP hcov hstored hwf anchors hsb.1)
        (ih1 side1 hfuture hP hcov hstored hwf anchors hsb.2)
  | @proj_coker Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro Psi side hfuture hP hcov hstored hwf anchors hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, _⟩ :=
        executableProjCokerParts side
      exact arms.proj_coker hb0 hb1 htof0 htof1 hw side hfuture hP hcov
        hstored hwf anchors hsb.1 hsb.2
        (ih0 side0 hfuture hP hcov hstored hwf anchors hsb.1)
        (ih1 side1 hfuture hP hcov hstored hwf anchors hsb.2)
  | @proj_img Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro Psi side hfuture hP hcov hstored hwf anchors hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, _⟩ :=
        executableProjImgParts side
      exact arms.proj_img hb0 hb1 htof0 htof1 hw side hfuture hP hcov
        hstored hwf anchors hsb.1 hsb.2
        (ih0 side0 hfuture hP hcov hstored hwf anchors hsb.1)
        (ih1 side1 hfuture hP hcov hstored hwf anchors hsb.2)
  | @proj_coimg Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro Psi side hfuture hP hcov hstored hwf anchors hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, _⟩ :=
        executableProjCoimgParts side
      exact arms.proj_coimg hb0 hb1 htof0 htof1 hw side hfuture hP hcov
        hstored hwf anchors hsb.1 hsb.2
        (ih0 side0 hfuture hP hcov hstored hwf anchors hsb.1)
        (ih1 side1 hfuture hP hcov hstored hwf anchors hsb.2)
  | @image Gamma b s0 s1 e hb hsof hw ih =>
      intro Psi side hfuture hP hcov hstored hwf anchors hsb
      obtain ⟨_, _, _, hb', _, side', _⟩ := executableImageParts side
      exact arms.image hb hsof hw side hfuture hP hcov hstored hwf anchors
        hsb (ih side' hfuture hP hcov hstored hwf anchors hsb)
  | @terms Gamma s es b hb htof hsv hall hne ih =>
      intro Psi side hfuture hP hcov hstored hwf anchors hsb
      obtain ⟨⟨hb', side'⟩, _, _, _⟩ := executableTermsParts side
      exact arms.terms hb htof hsv hall hne side hfuture hP hcov hstored hwf
        anchors hsb.2
        (ih side' hfuture hP hcov hstored hwf anchors hsb.2)
  | frame L hb0 hbody ih0 ihbody =>
      intro Psi _side _hfuture _hP _hcov _hstored _hwf _anchors hsb
      exact False.elim hsb

/-- A positive free-standard pair between space bases is necessarily in the
non-frame clause and therefore exposes the two executable endpoint syntax
layers at the predecessor leaf depth. -/
private theorem executableEndpointSides_of_pairSucc
    {Psi0 : EvalCtx} {depth : Nat} {Gamma : NLCtx}
    {source target : Basis}
    (pair : CheckedFreeStdPairBasisDepth Psi0 (depth + 1) Gamma source target)
    (hsource : Basis.BasisValid Gamma source)
    (htarget : Basis.BasisValid Gamma target)
    (hsSource : Basis.IsSpaceBasis source)
    (hsTarget : Basis.IsSpaceBasis target) :
    CheckedFreeStdExecutableBasisDepth Psi0 depth hsource /\
      CheckedFreeStdExecutableBasisDepth Psi0 depth htarget := by
  cases source <;> cases target <;>
    simp only [CheckedFreeStdPairBasisDepth] at pair
  all_goals try exact ⟨pair.2.2.2.1, pair.2.2.2.2⟩
  all_goals simp only [Basis.IsSpaceBasis] at hsSource hsTarget

/-- Uniform state-threaded source progress at one predecessor depth.  This
has the same telescope as the Nat assembly's local alias, while avoiding an
import cycle from this structural module back into the assembly. -/
def CheckedFreeStdStoreTermProgressDepthAll (depth : Nat) : Prop :=
  forall (Psi0 : EvalCtx), V2.StoredWF Psi0 ->
    CheckedFreeStdStoreTermProgressDepth Psi0 depth

/-- The successor space-COB edge for free-standard pairs.  Positive
space-typed pairs cannot be frames, so their executable endpoint layers are
fed to the complete structural COB recursion.  `StoredWF` at the current
world follows from the root proof and standard-future growth. -/
theorem checkedFreeStdPairSpaceCobDepth_succ_of_storeProgress
    (depth : Nat)
    (progressAll : CheckedFreeStdStoreTermProgressDepthAll depth) :
    CheckedFreeStdPairSpaceCobDepth (depth + 1) := by
  intro Psi0 hrootStored Gamma Psi source target pair hsource htarget
    hfuture anchors hP hcov hwf hsSource hsTarget
  obtain ⟨sourceSide, targetSide⟩ :=
    executableEndpointSides_of_pairSucc pair hsource htarget
      hsSource hsTarget
  have arms : CheckedFreeStdCobTermArmsDepthWithStore Psi0 depth :=
    checkedFreeStdCobTermArmsDepthWithStore_of_progress
      (progressAll Psi0 hrootStored)
  have hcob : CheckedFreeStdCobToStdDepthWithStore Psi0 depth :=
    checkedFreeStdCobToStdDepth_of_termArmsWithStore Psi0 depth arms
  have hstored : V2.StoredWF Psi := hfuture.storedWF hrootStored
  constructor
  · exact hcob hsource sourceSide hfuture hP hcov hstored hwf anchors hsSource
  · exact hcob htarget targetSide hfuture hP hcov hstored hwf anchors hsTarget

end RawCertifiedFreeStdGenericCobState
end GLang
