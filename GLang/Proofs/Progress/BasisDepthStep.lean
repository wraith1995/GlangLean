import GLang.Proofs.Progress.Certificates.RawCertifiedSelectedProgressMaster
import GLang.Proofs.Progress.Certificates.RawCertifiedCobProgress
import GLang.Proofs.Progress.StandardBasisDepth

/-!
# One constructive checked COB depth layer

This module proves the basis half of the checked progress/COB
mutual recursion.  A basis certificate at depth `n + 1` exposes every
embedded source derivation at depth `n`; structural basis children remain at
depth `n + 1` and decrease in basis syntax.

There are exactly six source-crossing constructors.  The structural theorem
takes those six source cases as explicit hypotheses supplied by the mutual
induction. No axiom or admission is used.
-/

namespace GLang
namespace RawCertifiedCobDepthLayerSpike

open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedCobProgressMutualSpike
open RawCertifiedSelectedProgressMaster
open RawCertifiedHereditaryStore
open RawCertifiedDepthStdSideSpike

/-- The exact COB conclusion at one depth, scoped to a fixed raw root. -/
def CheckedCobToStdDepth (Psi0 : EvalCtx) (n : Nat) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    (hb : Basis.BasisValid Gamma b),
    CheckedLocalSideBasisDepth Psi0 n hb ->
    CheckedStdFuture Psi0 Psi ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.CtxWF' (∅ : LCtx) Gamma -> Basis.IsSpaceBasis b ->
    exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))

/-- The six and only six basis-validity constructors which evaluate source
syntax.  Each field receives the complete depth certificate for its root;
that certificate contains its source witness at depth `n` and its structural
children at depth `n + 1`. -/
structure CheckedCobTermArmsDepth (Psi0 : EvalCtx) (n : Nat) : Prop where
  proj_ker :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
      {b0 b1 : Basis}
      (hb0 : Basis.BasisValid Gamma b0)
      (hb1 : Basis.BasisValid Gamma b1)
      (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
      (hw : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))),
      CheckedLocalSideBasisDepth Psi0 (n + 1)
        (.proj_ker hb0 hb1 htof0 htof1 hw) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.CtxWF' (∅ : LCtx) Gamma ->
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
      (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
      (hw : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))),
      CheckedLocalSideBasisDepth Psi0 (n + 1)
        (.proj_coker hb0 hb1 htof0 htof1 hw) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.CtxWF' (∅ : LCtx) Gamma ->
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
      (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
      (hw : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))),
      CheckedLocalSideBasisDepth Psi0 (n + 1)
        (.proj_img hb0 hb1 htof0 htof1 hw) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.CtxWF' (∅ : LCtx) Gamma ->
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
      (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
      (hw : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))),
      CheckedLocalSideBasisDepth Psi0 (n + 1)
        (.proj_coimg hb0 hb1 htof0 htof1 hw) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.CtxWF' (∅ : LCtx) Gamma ->
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
      CheckedLocalSideBasisDepth Psi0 (n + 1) (.image hb hsof hw) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.CtxWF' (∅ : LCtx) Gamma -> Basis.IsSpaceBasis b ->
      (exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) ->
      exists env, C.Cob Gamma Psi (.image b) env
        (Basis.std (Basis.tof (.image b)))
  terms :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s : Space}
      {es : List Term} {b : Basis}
      (hb : Basis.BasisValid Gamma b) (htof : Basis.tof b = .space s)
      (hsv : Nonempty (SValid Gamma s))
      (hall : forall e, e ∈ es ->
        Nonempty (HasType (∅ : LCtx) Gamma e (.space s)))
      (hne : es ≠ []),
      CheckedLocalSideBasisDepth Psi0 (n + 1) (.terms hb htof hsv hall hne) ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.CtxWF' (∅ : LCtx) Gamma ->
      Basis.IsSpaceBasis b ->
      (exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) ->
      exists env, C.Cob Gamma Psi (.terms s es b) env
        (Basis.std (Basis.tof (.terms s es b)))

/-! ## Root-local source re-entry helpers -/

private def sideZero
    {Psi0 : EvalCtx} {n : Nat} {Delta : LCtx} {Gamma : NLCtx}
    {s : Space} {hs : SValid Gamma s}
    (side : CheckedLocalSideSDepth Psi0 n hs) :
    CheckedLocalSideBasesDepth Psi0 n
      (HasType.zero (Δ := Delta) hs) :=
  CheckedLocalSideBasesWith.ofBelowPair
    ⟨trivial, ⟨trivial, side.shallow.descendants⟩⟩
    ⟨trivial, ⟨trivial, side.deep⟩⟩

/-- Space realization from the depth-`n` source theorem. -/
theorem checkedSpace_of_termProgressDepth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {s : Space} {hs : SValid Gamma s}
    (side : CheckedLocalSideSDepth Psi0 n hs)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma) :
    exists sv, C.Space Gamma Psi s sv := by
  obtain ⟨v, tauv, hv⟩ := hprogress (.zero hs) (sideZero side)
    Psi hfuture hP hcov hwf
  obtain ⟨sv, rfl, hspace⟩ :=
    checkedTyAt_space_inv_full (Basis.tof_std (.space s)) hv.tyAt
  exact ⟨sv, by simpa only [Basis.std, Basis.sof_stdSpace] using hspace⟩

private def sideInner
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {s : Space} {hs : SValid Gamma s}
    (side : CheckedLocalSideSDepth Psi0 n hs) :
    CheckedLocalSideBasesDepth Psi0 n (HasType.inner hs) :=
  CheckedLocalSideBasesWith.ofBelowPair
    ⟨trivial, ⟨trivial, side.shallow.descendants⟩⟩
    ⟨trivial, ⟨trivial, side.deep⟩⟩

/-- Root-local depth version of `checkedTerm_at_spaceBasis`. -/
theorem checkedTerm_at_spaceBasisDepth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {s : Space}
    {b : Basis} {envc : ValExpr} {sv : ValSpace}
    (ht : HasType (∅ : LCtx) Gamma e (.space s))
    (side : CheckedLocalSideBasesDepth Psi0 n ht)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hb : Basis.BasisValid Gamma b) (hsb : Basis.IsSpaceBasis b)
    (hsof : Basis.sof b = s)
    (hconv : C.Cob Gamma Psi b envc (Basis.stdSpace s))
    (hsv : C.Space Gamma Psi s sv) :
    exists v, C.Term (∅ : LCtx) Gamma Psi e b v (.space sv) := by
  obtain ⟨v, tauv, hv⟩ := hprogress ht side Psi hfuture hP hcov hwf
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

/-- Evaluate the canonical inner product at an arbitrary component basis. -/
theorem checkedInner_at_spaceBasisDepth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {s : Space}
    {envc : ValExpr} {sv : ValSpace} {hs : SValid Gamma s}
    (sideS : CheckedLocalSideSDepth Psi0 n hs)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
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
  exact checkedTerm_at_spaceBasisDepth hprogress (.inner hs)
    (sideInner sideS) hfuture hP hcov hwf hsource ⟨hsb, hsb⟩
    hsofOut htp hsvOut

/-- Evaluate a map witness at arbitrary domain/codomain component bases. -/
theorem checkedMapTerm_at_basesDepth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {s0 s1 : Space}
    {c0 c1 : Basis} {env0 env1 : ValExpr} {sv0 sv1 : ValSpace}
    (ht : HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1)))
    (side : CheckedLocalSideBasesDepth Psi0 n ht)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hc0 : Basis.BasisValid Gamma c0) (hc1 : Basis.BasisValid Gamma c1)
    (hsb0 : Basis.IsSpaceBasis c0) (hsb1 : Basis.IsSpaceBasis c1)
    (hsof0 : Basis.sof c0 = s0) (hsof1 : Basis.sof c1 = s1)
    (hconv0 : C.Cob Gamma Psi c0 env0 (Basis.stdSpace s0))
    (hconv1 : C.Cob Gamma Psi c1 env1 (Basis.stdSpace s1))
    (hsv0 : C.Space Gamma Psi s0 sv0) (hsv1 : C.Space Gamma Psi s1 sv1) :
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
  exact checkedTerm_at_spaceBasisDepth hprogress ht side hfuture hP hcov hwf
    hsource ⟨hsb0, hsb1⟩ hsofMap hmapConv hsvMap

/-! ## The six concrete source-crossing arms -/

/-- Depth-local image-basis arm.  The child basis certificate supplies the
source-space side trees, while the image layer supplies the witness term at
the strictly smaller source depth. -/
theorem checkedCob_image_arm_depth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    {s0 s1 : Space} {e : Term}
    (hb : Basis.BasisValid Gamma b)
    (hsof : Basis.sof b = .coker s0 s1 e)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (side : CheckedLocalSideBasisDepth Psi0 (n + 1) (.image hb hsof hw))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hsb : Basis.IsSpaceBasis b)
    (ih : exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) :
    exists env, C.Cob Gamma Psi (.image b) env
      (Basis.std (Basis.tof (.image b))) := by
  obtain ⟨s0', s1', e', hb', hsof', sideB, ht, ⟨sideT⟩⟩ :=
    side.image_parts
  have heq : Space.coker s0' s1' e' = .coker s0 s1 e :=
    hsof'.symm.trans hsof
  cases heq
  obtain ⟨hc, ⟨sideC⟩⟩ := checkedSofSideDepth sideB hsb
  have pc : exists hc0 : SValid Gamma (.coker s0 s1 e),
      Nonempty (CheckedLocalSideSDepth Psi0 n hc0) := by
    rw [← hsof]
    exact ⟨hc, ⟨sideC⟩⟩
  obtain ⟨hc0, ⟨sideC0⟩⟩ := pc
  cases hc0 with
  | coker hs0 hs1 hwt0 =>
      have sideS0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          sideC0.shallow.descendants.1 sideC0.deep.1
      have sideS1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          sideC0.shallow.descendants.2.1 sideC0.deep.2.1
      obtain ⟨sv0, hsv0⟩ := checkedSpace_of_termProgressDepth hprogress
        sideS0 hfuture hP hcov hwf
      obtain ⟨sv1, hsv1⟩ := checkedSpace_of_termProgressDepth hprogress
        sideS1 hfuture hP hcov hwf
      obtain ⟨v, tauv, hev0⟩ := hprogress ht sideT
        Psi hfuture hP hcov hwf
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
      have htrans := C.Cob.trans hsource htarget hstep1 hstep2 hsourceRealized
      have hex : exists env, C.Cob Gamma Psi (.image b) env
          (Basis.stdSpace (Basis.sof (.image b))) :=
        ⟨_, by simpa only [Basis.stdSpace, Basis.sof, hsof] using htrans⟩
      obtain ⟨out, hout⟩ := hex
      exact ⟨out, checkedCob_stdTof_of_stdSpace hsb hout⟩

private def sideDsumS
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1) :
    CheckedLocalSideSDepth Psi0 n (.dsum hs0 hs1) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨trivial, side1.shallow.descendants⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩, ⟨trivial, side1.deep⟩⟩⟩

private def sideDsumE
    {Psi0 : EvalCtx} {n : Nat} {Delta : LCtx} {Gamma : NLCtx}
    {s0 s1 : Space} {e0 e1 : Term}
    {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht0 : HasType Delta Gamma e0 (.space s0)}
    {ht1 : HasType Delta Gamma e1 (.space s1)}
    (sideS0 : CheckedLocalSideSDepth Psi0 n hs0)
    (sideS1 : CheckedLocalSideSDepth Psi0 n hs1)
    (side0 : CheckedLocalSideBasesDepth Psi0 n ht0)
    (side1 : CheckedLocalSideBasesDepth Psi0 n ht1) :
    CheckedLocalSideBasesDepth Psi0 n (.dsumE hs0 hs1 ht0 ht1) :=
  CheckedLocalSideBasesWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, sideS0.shallow.descendants⟩,
      ⟨⟨trivial, sideS1.shallow.descendants⟩,
        ⟨⟨side0.shallow.here, side0.shallow.descendants⟩,
          ⟨side1.shallow.here, side1.shallow.descendants⟩⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, sideS0.deep⟩,
      ⟨⟨trivial, sideS1.deep⟩,
        ⟨⟨side0.deepHere, side0.deepDescendants⟩,
          ⟨side1.deepHere, side1.deepDescendants⟩⟩⟩⟩⟩

private theorem checkedHasTypeDsumChainSideGo
    {Psi0 : EvalCtx} {n : Nat} {Delta : LCtx} {Gamma : NLCtx}
    {s : Space} (hs : SValid Gamma s)
    (sideS : CheckedLocalSideSDepth Psi0 n hs) (es : List Term) :
    forall (t : Space) (e0 : Term) (ht : SValid Gamma t)
      (sideT : CheckedLocalSideSDepth Psi0 n ht)
      (he0 : HasType Delta Gamma e0 (.space t))
      (sideE0 : CheckedLocalSideBasesDepth Psi0 n he0),
      (forall e, e ∈ es -> exists he : HasType Delta Gamma e (.space s),
        Nonempty (CheckedLocalSideBasesDepth Psi0 n he)) ->
      exists hout : HasType Delta Gamma (Term.dsumChain e0 es)
          (.space (es.foldl (fun u _ => Space.dsum u s) t)),
        Nonempty (CheckedLocalSideBasesDepth Psi0 n hout) := by
  induction es with
  | nil =>
      intro t e0 ht sideT he0 sideE0 hall
      exact ⟨he0, ⟨sideE0⟩⟩
  | cons a as ih =>
      intro t e0 ht sideT he0 sideE0 hall
      obtain ⟨ha, ⟨sideA⟩⟩ := hall a List.mem_cons_self
      let hpair : HasType Delta Gamma (.dsumE e0 a)
          (.space (.dsum t s)) := .dsumE ht hs he0 ha
      have sidePair : CheckedLocalSideBasesDepth Psi0 n hpair :=
        by
          dsimp only [hpair]
          exact sideDsumE sideT sideS sideE0 sideA
      exact ih (.dsum t s) (.dsumE e0 a) (.dsum ht hs)
        (sideDsumS sideT sideS) hpair sidePair
        (fun e he => hall e (List.mem_cons_of_mem a he))

private theorem foldlDsumChain (s : Space) :
    forall (es : List Term) (m : Nat),
      es.foldl (fun t _ => Space.dsum t s) (Space.dsumChain s m) =
        Space.dsumChain s (m + es.length)
  | [], m => by simp
  | a :: as, m => by
      simp only [List.foldl_cons, List.length_cons]
      have hshift : Space.dsum (Space.dsumChain s m) s =
          Space.dsumChain s (m + 1) := rfl
      rw [hshift, foldlDsumChain s as (m + 1)]
      congr 1
      omega

private theorem checkedHasTypeDsumChainSide
    {Psi0 : EvalCtx} {n : Nat} {Delta : LCtx} {Gamma : NLCtx}
    {s : Space} {e0 : Term} {es : List Term}
    (hs : SValid Gamma s) (sideS : CheckedLocalSideSDepth Psi0 n hs)
    (hall : forall e, e ∈ (e0 :: es) ->
      exists he : HasType Delta Gamma e (.space s),
        Nonempty (CheckedLocalSideBasesDepth Psi0 n he)) :
    exists hout : HasType Delta Gamma (Term.dsumChain e0 es)
        (.space (es.foldl (fun u _ => Space.dsum u s) s)),
      Nonempty (CheckedLocalSideBasesDepth Psi0 n hout) := by
  obtain ⟨he0, ⟨sideE0⟩⟩ := hall e0 List.mem_cons_self
  obtain ⟨hout, ⟨sideOut⟩⟩ := checkedHasTypeDsumChainSideGo
    hs sideS es s e0 hs sideS he0 sideE0
    (fun e he => hall e (List.mem_cons_of_mem e0 he))
  exact ⟨hout, ⟨sideOut⟩⟩

private def sideSDsumChain
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s : Space}
    {hs : SValid Gamma s} (side : CheckedLocalSideSDepth Psi0 n hs) :
    forall m, CheckedLocalSideSDepth Psi0 n (sValid_dsumChain hs m)
  | 0 => side
  | m + 1 => sideDsumS (sideSDsumChain side m) side

/-- Depth-local explicit-list basis arm. -/
theorem checkedCob_terms_arm_depth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {s : Space}
    {es : List Term} {b : Basis}
    (hb : Basis.BasisValid Gamma b) (htof : Basis.tof b = .space s)
    (hsv : Nonempty (SValid Gamma s))
    (hall : forall e, e ∈ es ->
      Nonempty (HasType (∅ : LCtx) Gamma e (.space s)))
    (hne : es ≠ [])
    (side : CheckedLocalSideBasisDepth Psi0 (n + 1)
      (.terms hb htof hsv hall hne))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hsb : Basis.IsSpaceBasis b)
    (ih : exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) :
    exists env, C.Cob Gamma Psi (.terms s es b) env
      (Basis.std (Basis.tof (.terms s es b))) := by
  obtain ⟨e0, es', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨⟨hb', sideB⟩, hsof', ⟨hs, ⟨sideS⟩⟩, termSides⟩ :=
    side.terms_parts
  subst s
  obtain ⟨envc, hc0⟩ := ih
  have hc : C.Cob Gamma Psi b envc (Basis.stdSpace (Basis.sof b)) :=
    checkedCob_stdSpace_of_stdTof hsb hc0
  obtain ⟨sv, hspace⟩ := checkedSpace_of_termProgressDepth hprogress
    sideS hfuture hP hcov hwf
  obtain ⟨envChain, hchainConv0⟩ :=
    checkedCob_dsumChain_toStdSpace hb hsb hc es'.length
  have hchainConv : C.Cob Gamma Psi (Basis.dsumChain b es'.length) envChain
      (Basis.stdSpace (Space.dsumChain (Basis.sof b) es'.length)) := by
    simpa only [Basis.sof_dsumChain] using hchainConv0
  have hchainValid := basisValid_dsumChain hb hsb es'.length
  have hchainSpace := Basis.IsSpaceBasis.dsumChain hsb es'.length
  let hchainSValid := sValid_dsumChain hs es'.length
  have sideChainS : CheckedLocalSideSDepth Psi0 n hchainSValid :=
    by
      dsimp only [hchainSValid]
      exact sideSDsumChain sideS es'.length
  obtain ⟨svChain, hsvChain⟩ := checkedSpace_of_termProgressDepth hprogress
    sideChainS hfuture hP hcov hwf
  have hchainSof : Basis.sof (Basis.dsumChain b es'.length) =
      Space.dsumChain (Basis.sof b) es'.length := Basis.sof_dsumChain _ _
  obtain ⟨htChain, ⟨sideChain⟩⟩ := checkedHasTypeDsumChainSide hs sideS
    (fun e he => termSides e he)
  have hfold : es'.foldl (fun t _ => Space.dsum t (Basis.sof b))
      (Basis.sof b) = Space.dsumChain (Basis.sof b) es'.length := by
    simpa only [Space.dsumChain, Nat.zero_add] using
      foldlDsumChain (Basis.sof b) es' 0
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
  obtain ⟨chainValue, hchain⟩ := checkedTerm_at_spaceBasisDepth hprogress
    htChain sideChain hfuture hP hcov hwf hchainValid hchainSpace
    hchainSofFold hchainConvFold hsvChainFold
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

private def sideEmbed
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {hsub : SubType Gamma s0 s1}
    (sideSub : CheckedLocalSideSubDepth Psi0 n hsub) :
    CheckedLocalSideBasesDepth Psi0 n (HasType.embed hsub) :=
  CheckedLocalSideBasesWith.ofBelowPair
    ⟨trivial, ⟨trivial, sideSub.shallow.descendants⟩⟩
    ⟨trivial, ⟨trivial, sideSub.deep⟩⟩

private def sideLproj
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {sSub sAmb : Space}
    {hsSub : SValid Gamma sSub} {hsAmb : SValid Gamma sAmb}
    {hsub : SubType Gamma sSub sAmb}
    (sideSubS : CheckedLocalSideSDepth Psi0 n hsSub)
    (sideAmbS : CheckedLocalSideSDepth Psi0 n hsAmb)
    (sideSub : CheckedLocalSideSubDepth Psi0 n hsub) :
    CheckedLocalSideBasesDepth Psi0 n (HasType.lproj hsSub hsAmb hsub) := by
  let sideE := sideEmbed sideSub
  exact CheckedLocalSideBasesWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, sideSubS.shallow.descendants⟩,
      ⟨⟨trivial, sideAmbS.shallow.descendants⟩,
        ⟨sideE.shallow.here, sideE.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, sideSubS.deep⟩,
      ⟨⟨trivial, sideAmbS.deep⟩,
        ⟨sideE.deepHere, sideE.deepDescendants⟩⟩⟩⟩

private def sideSubKer
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1)
    (sideT : CheckedLocalSideBasesDepth Psi0 n ht) :
    CheckedLocalSideSubDepth Psi0 n (.sub_ker hs0 hs1 ht) :=
  CheckedLocalSideSubWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def sideSubCoker
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1)
    (sideT : CheckedLocalSideBasesDepth Psi0 n ht) :
    CheckedLocalSideSubDepth Psi0 n (.sub_coker hs0 hs1 ht) :=
  CheckedLocalSideSubWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def sideSubImg
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1)
    (sideT : CheckedLocalSideBasesDepth Psi0 n ht) :
    CheckedLocalSideSubDepth Psi0 n (.sub_img hs0 hs1 ht) :=
  CheckedLocalSideSubWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def sideSubCoimg
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1)
    (sideT : CheckedLocalSideBasesDepth Psi0 n ht) :
    CheckedLocalSideSubDepth Psi0 n (.sub_coimg hs0 hs1 ht) :=
  CheckedLocalSideSubWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

/-- Domain-side (kernel/cokernel) projection construction with only the
actual depth-local source evidence used by the proof. -/
theorem checkedCob_proj_dom_arm_depth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 : Basis}
    (hsOr : s = .ker s0 s1 e ∨ s = .coker s0 s1 e)
    (hsS : SValid Gamma s) (sideS : CheckedLocalSideSDepth Psi0 n hsS)
    (hsub : SubType Gamma s s0)
    (sideSub : CheckedLocalSideSubDepth Psi0 n hsub)
    (hs0 : SValid Gamma s0) (sideS0 : CheckedLocalSideSDepth Psi0 n hs0)
    (hs1 : SValid Gamma s1) (sideS1 : CheckedLocalSideSDepth Psi0 n hs1)
    (hwt : HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1)))
    (sideT : CheckedLocalSideBasesDepth Psi0 n hwt)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
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
  obtain ⟨sv0, hsv0⟩ := checkedSpace_of_termProgressDepth hprogress sideS0 hfuture hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := checkedSpace_of_termProgressDepth hprogress sideS1 hfuture hP hcov hwf
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
  obtain ⟨vi0, hi0⟩ := checkedInner_at_spaceBasisDepth hprogress sideS0 hfuture hP hcov hwf
    hb0 hsb0 hsof0 hc0 hsv0
  obtain ⟨vi1, hi1⟩ := checkedInner_at_spaceBasisDepth hprogress sideS1 hfuture hP hcov hwf
    hb1 hsb1 hsof1 hc1 hsv1
  have hi0std := checked_inner_at hs0 hsv0
  have hi1std := checked_inner_at hs1 hsv1
  have hstd0 : Basis.BasisValid Gamma (Basis.stdSpace s0) :=
    Basis.stdSpace_valid s0 hs0
  have hstd1 : Basis.BasisValid Gamma (Basis.stdSpace s1) :=
    Basis.stdSpace_valid s1 hs1
  -- Witness evaluations at arbitrary, one-sided-standard, and all-standard bases.
  obtain ⟨ve1, he1⟩ := checkedMapTerm_at_basesDepth hprogress hwt sideT
    hfuture hP hcov hwf
    hb0 hb1 hsb0 hsb1 hsof0 hsof1 hc0 hc1 hsv0 hsv1
  obtain ⟨ve2, he2⟩ := checkedMapTerm_at_basesDepth hprogress hwt sideT
    hfuture hP hcov hwf
    hb0 hstd1 hsb0 (Basis.isSpaceBasis_stdSpace s1)
    hsof0 (Basis.sof_stdSpace s1) hc0 refl1 hsv0 hsv1
  obtain ⟨ve3, he3⟩ := checkedMapTerm_at_basesDepth hprogress hwt sideT
    hfuture hP hcov hwf
    hstd0 hstd1 (Basis.isSpaceBasis_stdSpace s0)
    (Basis.isSpaceBasis_stdSpace s1)
    (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    refl0 refl1 hsv0 hsv1
  -- Step 1: all-standard embed and projection.
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
  -- Step 2: standardize the domain coordinate while codomain is already std.
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
        (Basis.stdSpace s) := by
    exact ⟨_, by simpa only [hstdS] using hC2⟩
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
  obtain ⟨pmix, hpmix⟩ := checkedTerm_at_spaceBasisDepth hprogress (HasType.lproj hsS hs0 hsub)
    (sideLproj sideS sideS0 sideSub) hfuture hP hcov hwf hMixValid
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
      (Basis.stdSpace (Basis.sof (.proj s b0 b1))) := by
    exact ⟨_, by simpa only [Basis.sof, hstdS] using htrans⟩
  obtain ⟨out, hout⟩ := htoStdSpace
  exact ⟨out, checkedCob_stdTof_of_stdSpace ⟨hsb0, hsb1⟩ hout⟩

/-- Codomain-side (image/coimage) mirror of
`checkedCob_proj_dom_arm_depth`. -/
theorem checkedCob_proj_cod_arm_depth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 : Basis}
    (hsOr : s = .img s0 s1 e ∨ s = .coimg s0 s1 e)
    (hsS : SValid Gamma s) (sideS : CheckedLocalSideSDepth Psi0 n hsS)
    (hsub : SubType Gamma s s1)
    (sideSub : CheckedLocalSideSubDepth Psi0 n hsub)
    (hs0 : SValid Gamma s0) (sideS0 : CheckedLocalSideSDepth Psi0 n hs0)
    (hs1 : SValid Gamma s1) (sideS1 : CheckedLocalSideSDepth Psi0 n hs1)
    (hwt : HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1)))
    (sideT : CheckedLocalSideBasesDepth Psi0 n hwt)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
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
  obtain ⟨sv0, hsv0⟩ := checkedSpace_of_termProgressDepth hprogress sideS0 hfuture hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := checkedSpace_of_termProgressDepth hprogress sideS1 hfuture hP hcov hwf
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
  obtain ⟨vi0, hi0⟩ := checkedInner_at_spaceBasisDepth hprogress sideS0 hfuture hP hcov hwf
    hb0 hsb0 hsof0 hc0 hsv0
  obtain ⟨vi1, hi1⟩ := checkedInner_at_spaceBasisDepth hprogress sideS1 hfuture hP hcov hwf
    hb1 hsb1 hsof1 hc1 hsv1
  have hi0std := checked_inner_at hs0 hsv0
  have hi1std := checked_inner_at hs1 hsv1
  have hstd0 : Basis.BasisValid Gamma (Basis.stdSpace s0) :=
    Basis.stdSpace_valid s0 hs0
  have hstd1 : Basis.BasisValid Gamma (Basis.stdSpace s1) :=
    Basis.stdSpace_valid s1 hs1
  obtain ⟨ve1, he1⟩ := checkedMapTerm_at_basesDepth hprogress hwt sideT
    hfuture hP hcov hwf
    hb0 hb1 hsb0 hsb1 hsof0 hsof1 hc0 hc1 hsv0 hsv1
  obtain ⟨ve2, he2⟩ := checkedMapTerm_at_basesDepth hprogress hwt sideT
    hfuture hP hcov hwf
    hstd0 hb1 (Basis.isSpaceBasis_stdSpace s0) hsb1
    (Basis.sof_stdSpace s0) hsof1 refl0 hc1 hsv0 hsv1
  obtain ⟨ve3, he3⟩ := checkedMapTerm_at_basesDepth hprogress hwt sideT
    hfuture hP hcov hwf
    hstd0 hstd1 (Basis.isSpaceBasis_stdSpace s0)
    (Basis.isSpaceBasis_stdSpace s1)
    (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    refl0 refl1 hsv0 hsv1
  -- Step 1: all-standard inclusion and projection.
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
  -- Step 2: standardize the codomain coordinate while domain is already std.
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
  -- Step 3: standardize the remaining domain coordinate.
  obtain ⟨svS1, em1, hS1, hem1⟩ := checkedEmbed_codside hsOr
    hb0 hb1 hsof0 hsof1 hs0 hs1 hwt hsv0 hsv1 hi0 hi1 he1
  have hP1 : Basis.BasisValid Gamma (.proj s b0 b1) := by
    rcases hsOr with rfl | rfl
    · exact .proj_img hb0 hb1 htof0 htof1 ⟨hwt⟩
    · exact .proj_coimg hb0 hb1 htof0 htof1 ⟨hwt⟩
  have hC2stdExists : exists env,
      C.Cob Gamma Psi (.proj s (Basis.stdSpace s0) b1) env
        (Basis.stdSpace s) := by
    exact ⟨_, by simpa only [hstdS] using hC2⟩
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
  obtain ⟨pmix, hpmix⟩ := checkedTerm_at_spaceBasisDepth hprogress (HasType.lproj hsS hs1 hsub)
    (sideLproj sideS sideS1 sideSub) hfuture hP hcov hwf hMixValid
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
      (Basis.stdSpace (Basis.sof (.proj s b0 b1))) := by
    exact ⟨_, by simpa only [Basis.sof, hstdS] using htrans⟩
  obtain ⟨out, hout⟩ := htoStdSpace
  exact ⟨out, checkedCob_stdTof_of_stdSpace ⟨hsb0, hsb1⟩ hout⟩

private theorem checkedCob_proj_ker_arm_depth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
    {b0 b1 : Basis}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (side : CheckedLocalSideBasisDepth Psi0 (n + 1)
      (.proj_ker hb0 hb1 htof0 htof1 hw))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj (.ker s0 s1 e) b0 b1) env
      (Basis.std (Basis.tof (.proj (.ker s0 s1 e) b0 b1))) := by
  have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
  have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
  obtain ⟨hsS, ⟨sideS⟩⟩ := checkedSofSideDepth side ⟨hsb0, hsb1⟩
  cases hsS with
  | ker hs0 hs1 hwt =>
      have sideS0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.1 sideS.deep.1
      have sideS1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.2.1 sideS.deep.2.1
      have sideT : CheckedLocalSideBasesDepth Psi0 n hwt :=
        CheckedLocalSideBasesWith.ofBelowPair
          sideS.shallow.descendants.2.2 sideS.deep.2.2
      let hsub : SubType Gamma (.ker s0 s1 e) s0 :=
        .sub_ker hs0 hs1 hwt
      have sideSub : CheckedLocalSideSubDepth Psi0 n hsub := by
        dsimp only [hsub]
        exact sideSubKer sideS0 sideS1 sideT
      exact checkedCob_proj_dom_arm_depth hprogress (Or.inl rfl)
        (.ker hs0 hs1 hwt) sideS hsub sideSub
        hs0 sideS0 hs1 sideS1 hwt sideT hfuture hP hcov hwf
        hb0 hb1 htof0 htof1 hsb0 hsb1 ih0 ih1

private theorem checkedCob_proj_coker_arm_depth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
    {b0 b1 : Basis}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (side : CheckedLocalSideBasisDepth Psi0 (n + 1)
      (.proj_coker hb0 hb1 htof0 htof1 hw))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj (.coker s0 s1 e) b0 b1) env
      (Basis.std (Basis.tof (.proj (.coker s0 s1 e) b0 b1))) := by
  have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
  have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
  obtain ⟨hsS, ⟨sideS⟩⟩ := checkedSofSideDepth side ⟨hsb0, hsb1⟩
  cases hsS with
  | coker hs0 hs1 hwt =>
      have sideS0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.1 sideS.deep.1
      have sideS1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.2.1 sideS.deep.2.1
      have sideT : CheckedLocalSideBasesDepth Psi0 n hwt :=
        CheckedLocalSideBasesWith.ofBelowPair
          sideS.shallow.descendants.2.2 sideS.deep.2.2
      let hsub : SubType Gamma (.coker s0 s1 e) s0 :=
        .sub_coker hs0 hs1 hwt
      have sideSub : CheckedLocalSideSubDepth Psi0 n hsub := by
        dsimp only [hsub]
        exact sideSubCoker sideS0 sideS1 sideT
      exact checkedCob_proj_dom_arm_depth hprogress (Or.inr rfl)
        (.coker hs0 hs1 hwt) sideS hsub sideSub
        hs0 sideS0 hs1 sideS1 hwt sideT hfuture hP hcov hwf
        hb0 hb1 htof0 htof1 hsb0 hsb1 ih0 ih1

private theorem checkedCob_proj_img_arm_depth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
    {b0 b1 : Basis}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (side : CheckedLocalSideBasisDepth Psi0 (n + 1)
      (.proj_img hb0 hb1 htof0 htof1 hw))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj (.img s0 s1 e) b0 b1) env
      (Basis.std (Basis.tof (.proj (.img s0 s1 e) b0 b1))) := by
  have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
  have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
  obtain ⟨hsS, ⟨sideS⟩⟩ := checkedSofSideDepth side ⟨hsb0, hsb1⟩
  cases hsS with
  | img hs0 hs1 hwt =>
      have sideS0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.1 sideS.deep.1
      have sideS1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.2.1 sideS.deep.2.1
      have sideT : CheckedLocalSideBasesDepth Psi0 n hwt :=
        CheckedLocalSideBasesWith.ofBelowPair
          sideS.shallow.descendants.2.2 sideS.deep.2.2
      let hsub : SubType Gamma (.img s0 s1 e) s1 :=
        .sub_img hs0 hs1 hwt
      have sideSub : CheckedLocalSideSubDepth Psi0 n hsub := by
        dsimp only [hsub]
        exact sideSubImg sideS0 sideS1 sideT
      exact checkedCob_proj_cod_arm_depth hprogress (Or.inl rfl)
        (.img hs0 hs1 hwt) sideS hsub sideSub
        hs0 sideS0 hs1 sideS1 hwt sideT hfuture hP hcov hwf
        hb0 hb1 htof0 htof1 hsb0 hsb1 ih0 ih1

private theorem checkedCob_proj_coimg_arm_depth
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
    {b0 b1 : Basis}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (htof0 : Basis.tof b0 = .space s0) (htof1 : Basis.tof b1 = .space s1)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (side : CheckedLocalSideBasisDepth Psi0 (n + 1)
      (.proj_coimg hb0 hb1 htof0 htof1 hw))
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj (.coimg s0 s1 e) b0 b1) env
      (Basis.std (Basis.tof (.proj (.coimg s0 s1 e) b0 b1))) := by
  have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
  have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
  obtain ⟨hsS, ⟨sideS⟩⟩ := checkedSofSideDepth side ⟨hsb0, hsb1⟩
  cases hsS with
  | coimg hs0 hs1 hwt =>
      have sideS0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.1 sideS.deep.1
      have sideS1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          sideS.shallow.descendants.2.1 sideS.deep.2.1
      have sideT : CheckedLocalSideBasesDepth Psi0 n hwt :=
        CheckedLocalSideBasesWith.ofBelowPair
          sideS.shallow.descendants.2.2 sideS.deep.2.2
      let hsub : SubType Gamma (.coimg s0 s1 e) s1 :=
        .sub_coimg hs0 hs1 hwt
      have sideSub : CheckedLocalSideSubDepth Psi0 n hsub := by
        dsimp only [hsub]
        exact sideSubCoimg sideS0 sideS1 sideT
      exact checkedCob_proj_cod_arm_depth hprogress (Or.inr rfl)
        (.coimg hs0 hs1 hwt) sideS hsub sideSub
        hs0 sideS0 hs1 sideS1 hwt sideT hfuture hP hcov hwf
        hb0 hb1 htof0 htof1 hsb0 hsb1 ih0 ih1

/-- The six source-crossing obligations are all constructively discharged by
the source theorem at the preceding depth. -/
theorem checkedCobTermArmsDepth_of_termProgress
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n) :
    CheckedCobTermArmsDepth Psi0 n := by
  exact
    { proj_ker := checkedCob_proj_ker_arm_depth hprogress
      proj_coker := checkedCob_proj_coker_arm_depth hprogress
      proj_img := checkedCob_proj_img_arm_depth hprogress
      proj_coimg := checkedCob_proj_coimg_arm_depth hprogress
      image := checkedCob_image_arm_depth hprogress
      terms := checkedCob_terms_arm_depth hprogress }

/-- Structural basis recursion at one positive depth.  All source-crossing
work is visible in `arms`; every other case is closed here. -/
theorem checkedCobToStdDepth_of_termArms
    (Psi0 : EvalCtx) (n : Nat)
    (arms : CheckedCobTermArmsDepth Psi0 n) :
    CheckedCobToStdDepth Psi0 (n + 1) := by
  intro Gamma Psi b hb
  revert Psi
  induction hb with
  | empty =>
      intro Psi _side _hfuture _hP _hcov _hwf _hsb
      exact ⟨_, .refl .empty rfl .empty⟩
  | one =>
      intro Psi _side _hfuture _hP _hcov _hwf _hsb
      exact ⟨_, .refl .one rfl .real⟩
  | @dual Gamma b hb htof ih =>
      intro Psi side hfuture hP hcov hwf hsb
      obtain ⟨hb', side'⟩ := side.dual_child
      obtain ⟨env, henv⟩ := ih side' hfuture hP hcov hwf hsb
      exact ⟨_, by
        simpa only [Basis.std, Basis.tof, Basis.sof] using
          checkedCob_dual_toStdSpace hb hsb henv⟩
  | @dsum Gamma b0 b1 hb0 hb1 htof0 htof1 ih0 ih1 =>
      intro Psi side hfuture hP hcov hwf hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩⟩ := side.dsum_children
      obtain ⟨hs0, hs1⟩ := hsb
      obtain ⟨env0, h0⟩ := ih0 side0 hfuture hP hcov hwf hs0
      obtain ⟨env1, h1⟩ := ih1 side1 hfuture hP hcov hwf hs1
      have h0' := checkedCob_stdSpace_of_stdTof hs0 h0
      have h1' := checkedCob_stdSpace_of_stdTof hs1 h1
      exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hs0, hs1⟩
        (checkedCob_dsum_toStdSpace hb0 hb1 hs0 hs1 h0' h1')⟩
  | @tprod Gamma b0 b1 hb0 hb1 htof0 htof1 ih0 ih1 =>
      intro Psi side hfuture hP hcov hwf hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩⟩ := side.tprod_children
      obtain ⟨hs0, hs1⟩ := hsb
      obtain ⟨env0, h0⟩ := ih0 side0 hfuture hP hcov hwf hs0
      obtain ⟨env1, h1⟩ := ih1 side1 hfuture hP hcov hwf hs1
      have h0' := checkedCob_stdSpace_of_stdTof hs0 h0
      have h1' := checkedCob_stdSpace_of_stdTof hs1 h1
      exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hs0, hs1⟩
        (checkedCob_tprod_toStdSpace hb0 hb1 hs0 hs1 h0' h1')⟩
  | @proj_ker Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro Psi side hfuture hP hcov hwf hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, _⟩ :=
        side.proj_ker_parts
      exact arms.proj_ker hb0 hb1 htof0 htof1 hw side hfuture hP hcov hwf
        hsb.1 hsb.2 (ih0 side0 hfuture hP hcov hwf hsb.1)
        (ih1 side1 hfuture hP hcov hwf hsb.2)
  | @proj_coker Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro Psi side hfuture hP hcov hwf hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, _⟩ :=
        side.proj_coker_parts
      exact arms.proj_coker hb0 hb1 htof0 htof1 hw side hfuture hP hcov hwf
        hsb.1 hsb.2 (ih0 side0 hfuture hP hcov hwf hsb.1)
        (ih1 side1 hfuture hP hcov hwf hsb.2)
  | @proj_img Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro Psi side hfuture hP hcov hwf hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, _⟩ :=
        side.proj_img_parts
      exact arms.proj_img hb0 hb1 htof0 htof1 hw side hfuture hP hcov hwf
        hsb.1 hsb.2 (ih0 side0 hfuture hP hcov hwf hsb.1)
        (ih1 side1 hfuture hP hcov hwf hsb.2)
  | @proj_coimg Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro Psi side hfuture hP hcov hwf hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, _⟩ :=
        side.proj_coimg_parts
      exact arms.proj_coimg hb0 hb1 htof0 htof1 hw side hfuture hP hcov hwf
        hsb.1 hsb.2 (ih0 side0 hfuture hP hcov hwf hsb.1)
        (ih1 side1 hfuture hP hcov hwf hsb.2)
  | @image Gamma b s0 s1 e hb hsof hw ih =>
      intro Psi side hfuture hP hcov hwf hsb
      obtain ⟨_, _, _, hb', _, side', _⟩ := side.image_parts
      exact arms.image hb hsof hw side hfuture hP hcov hwf hsb
        (ih side' hfuture hP hcov hwf hsb)
  | @terms Gamma s es b hb htof hsv hall hne ih =>
      intro Psi side hfuture hP hcov hwf hsb
      obtain ⟨⟨hb', side'⟩, _, _, _⟩ := side.terms_parts
      exact arms.terms hb htof hsv hall hne side hfuture hP hcov hwf hsb.2
        (ih side' hfuture hP hcov hwf hsb.2)
  | frame L hb0 hbody ih0 ihbody =>
      intro Psi _side _hfuture _hP _hcov _hwf hsb
      exact False.elim hsb

/-- Canonical positive layer: source progress at depth `n` closes COB at
depth `n+1`.  There is no global side supply, COB oracle, or external arm
parameter in this statement. -/
theorem checkedCobToStdDepth_succ_of_termProgress
    (hprogress :
      RawCertifiedSelectedProgressMaster.CheckedTermProgressDepth Psi0 n) :
    CheckedCobToStdDepth Psi0 (n + 1) :=
  checkedCobToStdDepth_of_termArms Psi0 n
    (checkedCobTermArmsDepth_of_termProgress hprogress)

/-- Depth zero contains only the five term-free structural basis forms, so
COB closes without any source-progress re-entry. -/
theorem checkedCobToStdDepth_zero (Psi0 : EvalCtx) :
    CheckedCobToStdDepth Psi0 0 := by
  intro Gamma Psi b hb side hfuture hP hcov hwf hsb
  have side' : CheckedLocalSideBasisZero hb := by
    simpa only [CheckedLocalSideBasisDepth] using side
  clear side
  induction side' with
  | empty =>
      exact ⟨_, .refl .empty rfl .empty⟩
  | one =>
      exact ⟨_, .refl .one rfl .real⟩
  | @dual b hb _ side ih =>
      obtain ⟨env, henv⟩ := ih hsb
      exact ⟨_, by
        simpa only [Basis.std, Basis.tof, Basis.sof] using
          checkedCob_dual_toStdSpace hb hsb henv⟩
  | @dsum b0 b1 hb0 hb1 _ _ side0 side1 ih0 ih1 =>
      obtain ⟨hs0, hs1⟩ := hsb
      obtain ⟨env0, h0⟩ := ih0 hs0
      obtain ⟨env1, h1⟩ := ih1 hs1
      have h0' := checkedCob_stdSpace_of_stdTof hs0 h0
      have h1' := checkedCob_stdSpace_of_stdTof hs1 h1
      exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hs0, hs1⟩
        (checkedCob_dsum_toStdSpace hb0 hb1 hs0 hs1 h0' h1')⟩
  | @tprod b0 b1 hb0 hb1 _ _ side0 side1 ih0 ih1 =>
      obtain ⟨hs0, hs1⟩ := hsb
      obtain ⟨env0, h0⟩ := ih0 hs0
      obtain ⟨env1, h1⟩ := ih1 hs1
      have h0' := checkedCob_stdSpace_of_stdTof hs0 h0
      have h1' := checkedCob_stdSpace_of_stdTof hs1 h1
      exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hs0, hs1⟩
        (checkedCob_tprod_toStdSpace hb0 hb1 hs0 hs1 h0' h1')⟩

end RawCertifiedCobDepthLayerSpike
end GLang
