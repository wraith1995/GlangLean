import GLang.Proofs.Progress.Certificates.RawCertifiedWeaken
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardCertificate
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedExactAnchorStore
import GLang.Proofs.Progress.Certificates.RawCertifiedPiBasisTransport
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactBasisTyProgress

set_option maxHeartbeats 3200000
set_option maxRecDepth 6000

namespace GLang
namespace RawCertifiedPairFreeStandardServices

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedPiBasisTransport
open RawCertifiedExactBasisTyProgress
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate
open RawCertifiedPairFreeStandardCertificate
open RawCertifiedExactAnchorStore

/-- EvalCtx.avoidB already contains every evaluator key name.  Frame services
pick their binder outside it, so the pair certificate's explicit current-world
name-freshness premise costs no additional assumption. -/
private theorem not_mem_names_of_not_mem_avoidB
    {Psi : EvalCtx} {x : VName} (hx : x ∉ EvalCtx.avoidB Psi) :
    x ∉ Psi.names := by
  classical
  intro hname
  obtain ⟨⟨x', b⟩, hkey, hx'⟩ := Finset.mem_image.mp hname
  simp only at hx'
  subst x'
  exact (EvalCtx.avoidB_spec hx).1 b (Finmap.mem_keys.mp hkey)

/-- Exactness needed by transport is directional: the incoming checked term
already contains exactness for `source`, so only `target` must be built. -/
def CheckedFreeStdPairTargetExactDepth (depth : Nat) : Prop :=
  forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
    (Gamma : NLCtx) (Psi : EvalCtx) (source target : Basis),
    CheckedFreeStdPairBasisDepth Psi0 depth Gamma source target ->
    Basis.BasisValid Gamma source -> Basis.BasisValid Gamma target ->
    CheckedStdFuture Psi0 Psi ->
    CheckedExactLookupStore Gamma Psi ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> forall (Delta : LCtx), V2.CtxWF' Delta Gamma ->
    Basis.IsTyBasis source -> Basis.IsTyBasis target ->
    Basis.tof target = Basis.tof source ->
    exists tauV, C.TyAt Gamma Psi target tauV

/-- The space branch asks for conversions of precisely the two endpoints of
the current pair.  This is not a global COB supply. -/
def CheckedFreeStdPairSpaceCobDepth (depth : Nat) : Prop :=
  forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
    (Gamma : NLCtx) (Psi : EvalCtx) (source target : Basis),
    CheckedFreeStdPairBasisDepth Psi0 depth Gamma source target ->
    Basis.BasisValid Gamma source -> Basis.BasisValid Gamma target ->
    CheckedStdFuture Psi0 Psi ->
    CheckedExactLookupStore Gamma Psi ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.CtxWF' (∅ : LCtx) Gamma ->
    Basis.IsSpaceBasis source -> Basis.IsSpaceBasis target ->
    (exists env, C.Cob Gamma Psi source env
      (Basis.std (Basis.tof source))) /\
    (exists env, C.Cob Gamma Psi target env
      (Basis.std (Basis.tof target)))

/-- The zero certificate admits exactly the five term-free structural basis
forms. -/
private theorem checkedCobToStd_of_zeroSide
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    (hb : Basis.BasisValid Gamma b)
    (side : CheckedLocalSideBasisZero hb)
    (hsb : Basis.IsSpaceBasis b) :
    exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b)) := by
  induction side with
  | empty =>
      exact ⟨_, .refl .empty rfl .empty⟩
  | one =>
      exact ⟨_, .refl .one rfl .real⟩
  | @dual b hb _ _ ih =>
      obtain ⟨env, henv⟩ := ih hsb
      exact ⟨_, by
        simpa only [Basis.std, Basis.tof, Basis.sof] using
          checkedCob_dual_toStdSpace hb hsb henv⟩
  | @dsum b0 b1 hb0 hb1 _ _ _ _ ih0 ih1 =>
      obtain ⟨hs0, hs1⟩ := hsb
      obtain ⟨env0, h0⟩ := ih0 hs0
      obtain ⟨env1, h1⟩ := ih1 hs1
      have h0' := checkedCob_stdSpace_of_stdTof hs0 h0
      have h1' := checkedCob_stdSpace_of_stdTof hs1 h1
      exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hs0, hs1⟩
        (checkedCob_dsum_toStdSpace hb0 hb1 hs0 hs1 h0' h1')⟩
  | @tprod b0 b1 hb0 hb1 _ _ _ _ ih0 ih1 =>
      obtain ⟨hs0, hs1⟩ := hsb
      obtain ⟨env0, h0⟩ := ih0 hs0
      obtain ⟨env1, h1⟩ := ih1 hs1
      have h0' := checkedCob_stdSpace_of_stdTof hs0 h0
      have h1' := checkedCob_stdSpace_of_stdTof hs1 h1
      exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hs0, hs1⟩
        (checkedCob_tprod_toStdSpace hb0 hb1 hs0 hs1 h0' h1')⟩

/-- Depth zero is directly executable: both endpoints contain only the five
term-free structural basis forms accepted by `CheckedLocalSideBasisZero`. -/
theorem checkedFreeStdPairSpaceCobDepth_zero : CheckedFreeStdPairSpaceCobDepth 0 := by
  intro _Psi0 _hrootStored Gamma Psi source target pair _hsource _htarget
    _hfuture _hanchors _hP _hcov _hwf hsSource hsTarget
  simp only [CheckedFreeStdPairBasisDepth] at pair
  obtain ⟨_htof, ⟨hsource, sourceZero⟩,
    ⟨htarget, targetZero⟩⟩ := pair
  constructor
  · exact checkedCobToStd_of_zeroSide hsource sourceZero hsSource
  · exact checkedCobToStd_of_zeroSide htarget targetZero hsTarget

/-- Concrete pair transport, uniform only over worlds and terms carrying the
same literal pair certificate. -/
def CheckedFreeStdPairTermTransportDepth (depth : Nat) : Prop :=
  forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx) (e : Term)
    (source target : Basis) (v : ValExpr) (tauV : ValTy),
    CheckedFreeStdPairBasisDepth Psi0 depth Gamma source target ->
    Basis.BasisValid Gamma source -> Basis.BasisValid Gamma target ->
    CheckedStdFuture Psi0 Psi ->
    CheckedExactLookupStore Gamma Psi ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
    Basis.IsTyBasis source -> Basis.IsTyBasis target ->
    Basis.tof target = Basis.tof source ->
    C.Term Delta Gamma Psi e source v tauV ->
    exists w tauW, C.Term Delta Gamma Psi e target w tauW

private theorem checkedFreeStdPairSpaceTermTransport
    (depth : Nat) (hcob : CheckedFreeStdPairSpaceCobDepth depth)
    {Psi0 : EvalCtx} (hrootStored : V2.StoredWF Psi0)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {e : Term}
    {source target : Basis} {v : ValExpr} {sv : ValSpace}
    (pair : CheckedFreeStdPairBasisDepth Psi0 depth Gamma source target)
    (hsource : Basis.BasisValid Gamma source)
    (htarget : Basis.BasisValid Gamma target)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hanchors : CheckedExactLookupStore Gamma Psi)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' Delta Gamma)
    (hiSource : Basis.IsSpaceBasis source)
    (hiTarget : Basis.IsSpaceBasis target)
    (htof : Basis.tof target = Basis.tof source)
    (hterm : C.Term Delta Gamma Psi e source v (.space sv)) :
    exists w tauW, C.Term Delta Gamma Psi e target w tauW := by
  have hwf0 := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
  obtain ⟨⟨envSource, hcobSource⟩, ⟨envTarget, hcobTarget⟩⟩ :=
    hcob Psi0 hrootStored Gamma Psi source target pair hsource htarget hfuture
      hanchors hP hcov hwf0 hiSource hiTarget
  have hspaceSource : C.Space Gamma Psi (Basis.sof source) sv := by
    obtain ⟨sv', heq, hspace⟩ :=
      checkedTyAt_space_inv_full hiSource.tof_eq hterm.tyAt
    injection heq with heq'
    subst sv'
    exact hspace
  have hsof : Basis.sof target = Basis.sof source :=
    V2.sof_of_tof_eq_space (htof.trans hiSource.tof_eq)
  have hspaceTarget : C.Space Gamma Psi (Basis.sof target) sv := by
    rw [hsof]
    exact hspaceSource
  rw [htof] at hcobTarget
  obtain ⟨_k, ⟨htvalid⟩⟩ := hsource.tof_tvalid
  have hstdValid : Basis.BasisValid Gamma
      (Basis.std (Basis.tof source)) := Basis.std_valid _ htvalid
  obtain ⟨env, hbetween⟩ : exists env,
      C.Cob Gamma Psi source env target :=
    ⟨_, .trans hsource htarget hcobSource
      (.inverse hstdValid htarget hcobTarget) hspaceSource⟩
  have htypedTarget : Nonempty
      (HasType Delta Gamma e (Basis.tof target)) := by
    rw [htof]
    exact hterm.hasType
  have htypeTarget : C.TyAt Gamma Psi target (.space sv) :=
    .space hiTarget.tof_eq htarget hspaceTarget
  exact ⟨_, .space sv,
    .cob hiTarget.tof_eq hiSource.tof_eq htypedTarget htarget
      htypeTarget hterm hbetween hspaceTarget⟩

private def CheckedFreeStdPairTargetExactN (depth size : Nat) : Prop :=
  forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
    (Gamma : NLCtx) (Psi : EvalCtx) (source target : Basis),
    CheckedFreeStdPairBasisDepth Psi0 depth Gamma source target ->
    Basis.BasisValid Gamma source -> Basis.BasisValid Gamma target ->
    CheckedStdFuture Psi0 Psi ->
    CheckedExactLookupStore Gamma Psi ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> forall (Delta : LCtx), V2.CtxWF' Delta Gamma ->
    Basis.IsTyBasis source -> Basis.IsTyBasis target ->
    Basis.tof target = Basis.tof source ->
    Ty.size (Basis.tof target) <= size ->
    exists tauV, C.TyAt Gamma Psi target tauV

private theorem checkedFreeStdPairTargetExactN_of_spaceCob
    (depth : Nat) (hcob : CheckedFreeStdPairSpaceCobDepth depth)
    (hren : CheckedRenameLaws) :
    forall size, CheckedFreeStdPairTargetExactN depth size := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
    intro Psi0 hrootStored Gamma Psi source target pair
      hsource htarget hfuture hanchors hP hcov hstored Delta hwf
      hiSource hiTarget htof hsize
    cases htargetTy : Basis.tof target with
    | space s =>
        have hsTarget : Basis.IsSpaceBasis target :=
          hiTarget.toIsSpaceBasis (Basis.ne_frame_of_tof_space htargetTy)
        have hsSource : Basis.IsSpaceBasis source :=
          hiSource.toIsSpaceBasis
            (Basis.ne_frame_of_tof_space (htof.symm.trans htargetTy))
        obtain ⟨_sourceCob, ⟨envTarget, htargetCob⟩⟩ :=
          hcob Psi0 hrootStored Gamma Psi source target pair hsource htarget hfuture
            hanchors hP hcov (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
            hsSource hsTarget
        obtain ⟨sv, hsv⟩ := checkedCob_sourceSpace htargetCob
        exact ⟨.space sv,
          .space hsTarget.tof_eq htarget hsv⟩
    | piTy tau0 tau1 =>
        obtain ⟨b10, b11, rfl, htof10, htof11⟩ :=
          Basis.tof_piTy_inv (htof.symm.trans htargetTy)
        obtain ⟨b20, b21, rfl, htof20, htof21⟩ :=
          Basis.tof_piTy_inv htargetTy
        rw [htargetTy] at hsize
        simp only [Ty.size] at hsize
        have hsmall0 : Ty.size tau0 < size := by omega
        have hsmall1 : Ty.size tau1 < size := by omega
        have hdepth : depth ≠ 0 := by
          intro hz
          subst depth
          simp only [CheckedFreeStdPairBasisDepth] at pair
          obtain ⟨_, _, ⟨_, hzero⟩⟩ := pair
          cases hzero
        obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdepth
        simp only [CheckedFreeStdPairBasisDepth] at pair
        obtain ⟨_hdomTof, _hcodTof, _sourceAvoid, targetAvoid,
          _sourceDomainValid, targetDomainValid, _sourceBodyValid,
          targetBodyValid, _sourceSelfDomain, targetSelfDomain,
          _sourceOwn, targetOwn, _transportUnder⟩ := pair
        obtain ⟨hi10, hi11⟩ := hiSource
        obtain ⟨hi20, hi21⟩ := hiTarget
        obtain ⟨tauV20, hdom20⟩ :=
          ih (Ty.size tau0) hsmall0 Psi0 hrootStored Gamma Psi
            b20 b20 targetSelfDomain targetDomainValid targetDomainValid
            hfuture hanchors hP hcov hstored (∅ : LCtx)
            (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
            hi20 hi20 rfl (by rw [htof20])
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
          (EvalCtx.avoidB Psi ∪ Gamma.keys ∪ targetAvoid ∪
            Basis.fv b20 ∪ Basis.fv b21 ∪ ValTy.fv tauV20)
        simp only [Finset.mem_union, not_or] at hx
        obtain ⟨⟨⟨⟨⟨hxPsi, hxGammaKeys⟩, hxTargetAvoid⟩,
          hxb20⟩, hxb21⟩, hxtauV20⟩ := hx
        have hxGamma : x ∉ Gamma := by
          intro hm
          exact hxGammaKeys (Finmap.mem_keys.mpr hm)
        have hfresh : (x, b20) ∉ Psi :=
          (EvalCtx.avoidB_spec hxPsi).1 b20
        obtain ⟨hPx, hcovx, hstoredx⟩ :=
          V2.pcarrier_extend_transport
            (V2.transportN (Ty.size (Basis.tof b20)))
            hP hcov hstored targetDomainValid hi20 hdom20.erase
            hfresh le_rfl
        let PsiX := Psi.extend x b20 (.var x tauV20)
        let GammaX := Finmap.insert x (Basis.tof b20) Gamma
        have hinc : NLCtxIncl Gamma GammaX :=
          (NLCtxIncl.refl Gamma).insert_right hxGamma (Basis.tof b20)
        have hanchorsX : CheckedExactLookupStore GammaX PsiX :=
          CheckedExactLookupStore.nlMono
            (CheckedExactLookupStore.extend hanchors
              (not_mem_names_of_not_mem_avoidB hxPsi) hdom20)
            hinc
        have hwf0 := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
        have hwfx : V2.CtxWF' (∅ : LCtx) GammaX :=
          RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
            (b := b20) hwf0 Finmap.notMem_empty hxGamma
            targetDomainValid
        have hb21x : Basis.BasisValid GammaX (Basis.openVar x b21) :=
          targetBodyValid x hxTargetAvoid
        have codomainSelfX :=
          targetOwn Psi hfuture x
            (not_mem_names_of_not_mem_avoidB hxPsi)
            hxTargetAvoid tauV20 hdom20
        have hsizeCod : Ty.size (Basis.tof (Basis.openVar x b21)) <=
            Ty.size tau1 := by
          show Ty.size (Basis.tof (Basis.openRec 0 (.var x) b21)) <=
            Ty.size tau1
          rw [Basis.tof_openRec, htof21]
          exact le_of_eq (Ty.size_openVar 0 x tau1)
        obtain ⟨tauVOut, hout⟩ :=
          ih (Ty.size tau1) hsmall1 PsiX hstoredx GammaX PsiX
            (Basis.openVar x b21) (Basis.openVar x b21)
            codomainSelfX hb21x hb21x (CheckedStdFuture.refl _)
            hanchorsX hPx hcovx hstoredx (∅ : LCtx) hwfx
            (Basis.IsTyBasis.openRec (.var x) 0 hi21)
            (Basis.IsTyBasis.openRec (.var x) 0 hi21) rfl hsizeCod
        have hlctauV20 : ValTy.lc tauV20 :=
          evalT_lc hdom20.erase hP.1.toEvalCtxLc
        have hlctauVOut : ValTy.lc tauVOut :=
          evalT_lc hout.erase hPx.1.toEvalCtxLc
        have hout' : C.TyAt (Finmap.insert x tau0 Gamma) PsiX
            (Basis.openVar x b21) tauVOut := by
          rw [← htof20]
          exact hout
        obtain ⟨Lout, hcodOut⟩ :=
          checkedTyAt_arbitrary_cofinite_of_fresh hren hwf0
            (by
              obtain ⟨k, ⟨ht0⟩⟩ := targetDomainValid.tof_tvalid
              exact ⟨k, ⟨by simpa only [htof20] using ht0⟩⟩)
            htof20 targetDomainValid hxGamma hout' hxPsi hxb20
            hxtauV20 hxb21 hlctauV20 hlctauVOut
        rw [← htof20] at hcodOut
        exact ⟨.piTy tauV20 (ValTy.closeRec 0 x tauVOut),
          .frame htarget hdom20 Lout hcodOut⟩

/-- The enriched self-domain/self-codomain fields make target exactness
fully executable from the pair-aware space COB service. -/
theorem checkedFreeStdPairTargetExactDepth_of_spaceCob
    (depth : Nat) (hcob : CheckedFreeStdPairSpaceCobDepth depth)
    (hren : CheckedRenameLaws) : CheckedFreeStdPairTargetExactDepth depth := by
  intro Psi0 hrootStored Gamma Psi source target pair
    hsource htarget hfuture hanchors hP hcov hstored Delta hwf
    hiSource hiTarget htof
  exact checkedFreeStdPairTargetExactN_of_spaceCob depth hcob hren
    (Ty.size (Basis.tof target)) Psi0 hrootStored Gamma Psi source target
    pair hsource htarget hfuture hanchors hP hcov hstored Delta hwf
    hiSource hiTarget htof le_rfl

/-- Source-endpoint companion. -/
def CheckedFreeStdPairSourceExactDepth (depth : Nat) : Prop :=
  forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
    (Gamma : NLCtx) (Psi : EvalCtx) (source target : Basis),
    CheckedFreeStdPairBasisDepth Psi0 depth Gamma source target ->
    Basis.BasisValid Gamma source -> Basis.BasisValid Gamma target ->
    CheckedStdFuture Psi0 Psi ->
    CheckedExactLookupStore Gamma Psi ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> forall (Delta : LCtx), V2.CtxWF' Delta Gamma ->
    Basis.IsTyBasis source -> Basis.IsTyBasis target ->
    Basis.tof target = Basis.tof source ->
    exists tauV, C.TyAt Gamma Psi source tauV

private def CheckedFreeStdPairSourceExactN (depth size : Nat) : Prop :=
  forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
    (Gamma : NLCtx) (Psi : EvalCtx) (source target : Basis),
    CheckedFreeStdPairBasisDepth Psi0 depth Gamma source target ->
    Basis.BasisValid Gamma source -> Basis.BasisValid Gamma target ->
    CheckedStdFuture Psi0 Psi ->
    CheckedExactLookupStore Gamma Psi ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> forall (Delta : LCtx), V2.CtxWF' Delta Gamma ->
    Basis.IsTyBasis source -> Basis.IsTyBasis target ->
    Basis.tof target = Basis.tof source ->
    Ty.size (Basis.tof source) <= size ->
    exists tauV, C.TyAt Gamma Psi source tauV

private theorem checkedFreeStdPairSourceExactN_of_spaceCob
    (depth : Nat) (hcob : CheckedFreeStdPairSpaceCobDepth depth)
    (hren : CheckedRenameLaws) :
    forall size, CheckedFreeStdPairSourceExactN depth size := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
    intro Psi0 hrootStored Gamma Psi source target pair
      hsource htarget hfuture hanchors hP hcov hstored Delta hwf
      hiSource hiTarget htof hsize
    cases hsourceTy : Basis.tof source with
    | space s =>
        have hsSource : Basis.IsSpaceBasis source :=
          hiSource.toIsSpaceBasis (Basis.ne_frame_of_tof_space hsourceTy)
        have hsTarget : Basis.IsSpaceBasis target :=
          hiTarget.toIsSpaceBasis
            (Basis.ne_frame_of_tof_space (htof.trans hsourceTy))
        obtain ⟨⟨envSource, hsourceCob⟩, _targetCob⟩ :=
          hcob Psi0 hrootStored Gamma Psi source target pair hsource htarget hfuture
            hanchors hP hcov (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
            hsSource hsTarget
        obtain ⟨sv, hsv⟩ := checkedCob_sourceSpace hsourceCob
        exact ⟨.space sv,
          .space hsSource.tof_eq hsource hsv⟩
    | piTy tau0 tau1 =>
        obtain ⟨b10, b11, rfl, htof10, htof11⟩ :=
          Basis.tof_piTy_inv hsourceTy
        obtain ⟨b20, b21, rfl, htof20, htof21⟩ :=
          Basis.tof_piTy_inv (htof.trans hsourceTy)
        rw [hsourceTy] at hsize
        simp only [Ty.size] at hsize
        have hsmall0 : Ty.size tau0 < size := by omega
        have hsmall1 : Ty.size tau1 < size := by omega
        have hdepth : depth ≠ 0 := by
          intro hz
          subst depth
          simp only [CheckedFreeStdPairBasisDepth] at pair
          obtain ⟨_, ⟨_, hzero⟩, _⟩ := pair
          cases hzero
        obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdepth
        simp only [CheckedFreeStdPairBasisDepth] at pair
        obtain ⟨_hdomTof, _hcodTof, sourceAvoid, _targetAvoid,
          sourceDomainValid, _targetDomainValid, sourceBodyValid,
          _targetBodyValid, sourceSelfDomain, _targetSelfDomain,
          sourceOwn, _targetOwn, _transportUnder⟩ := pair
        obtain ⟨hi10, hi11⟩ := hiSource
        obtain ⟨hi20, hi21⟩ := hiTarget
        obtain ⟨tauV10, hdom10⟩ :=
          ih (Ty.size tau0) hsmall0 Psi0 hrootStored Gamma Psi
            b10 b10 sourceSelfDomain sourceDomainValid sourceDomainValid
            hfuture hanchors hP hcov hstored (∅ : LCtx)
            (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
            hi10 hi10 rfl (by rw [htof10])
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
          (EvalCtx.avoidB Psi ∪ Gamma.keys ∪ sourceAvoid ∪
            Basis.fv b10 ∪ Basis.fv b11 ∪ ValTy.fv tauV10)
        simp only [Finset.mem_union, not_or] at hx
        obtain ⟨⟨⟨⟨⟨hxPsi, hxGammaKeys⟩, hxSourceAvoid⟩,
          hxb10⟩, hxb11⟩, hxtauV10⟩ := hx
        have hxGamma : x ∉ Gamma := by
          intro hm
          exact hxGammaKeys (Finmap.mem_keys.mpr hm)
        have hfresh : (x, b10) ∉ Psi :=
          (EvalCtx.avoidB_spec hxPsi).1 b10
        obtain ⟨hPx, hcovx, hstoredx⟩ :=
          V2.pcarrier_extend_transport
            (V2.transportN (Ty.size (Basis.tof b10)))
            hP hcov hstored sourceDomainValid hi10 hdom10.erase
            hfresh le_rfl
        let PsiX := Psi.extend x b10 (.var x tauV10)
        let GammaX := Finmap.insert x (Basis.tof b10) Gamma
        have hinc : NLCtxIncl Gamma GammaX :=
          (NLCtxIncl.refl Gamma).insert_right hxGamma (Basis.tof b10)
        have hanchorsX : CheckedExactLookupStore GammaX PsiX :=
          CheckedExactLookupStore.nlMono
            (CheckedExactLookupStore.extend hanchors
              (not_mem_names_of_not_mem_avoidB hxPsi) hdom10)
            hinc
        have hwf0 := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
        have hwfx : V2.CtxWF' (∅ : LCtx) GammaX :=
          RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
            (b := b10) hwf0 Finmap.notMem_empty hxGamma
            sourceDomainValid
        have hb11x : Basis.BasisValid GammaX (Basis.openVar x b11) :=
          sourceBodyValid x hxSourceAvoid
        have codomainSelfX :=
          sourceOwn Psi hfuture x
            (not_mem_names_of_not_mem_avoidB hxPsi)
            hxSourceAvoid tauV10 hdom10
        have hsizeCod : Ty.size (Basis.tof (Basis.openVar x b11)) <=
            Ty.size tau1 := by
          show Ty.size (Basis.tof (Basis.openRec 0 (.var x) b11)) <=
            Ty.size tau1
          rw [Basis.tof_openRec, htof11]
          exact le_of_eq (Ty.size_openVar 0 x tau1)
        obtain ⟨tauVOut, hout⟩ :=
          ih (Ty.size tau1) hsmall1 PsiX hstoredx GammaX PsiX
            (Basis.openVar x b11) (Basis.openVar x b11)
            codomainSelfX hb11x hb11x (CheckedStdFuture.refl _)
            hanchorsX hPx hcovx hstoredx (∅ : LCtx) hwfx
            (Basis.IsTyBasis.openRec (.var x) 0 hi11)
            (Basis.IsTyBasis.openRec (.var x) 0 hi11) rfl hsizeCod
        have hlctauV10 : ValTy.lc tauV10 :=
          evalT_lc hdom10.erase hP.1.toEvalCtxLc
        have hlctauVOut : ValTy.lc tauVOut :=
          evalT_lc hout.erase hPx.1.toEvalCtxLc
        have hout' : C.TyAt (Finmap.insert x tau0 Gamma) PsiX
            (Basis.openVar x b11) tauVOut := by
          rw [← htof10]
          exact hout
        obtain ⟨Lout, hcodOut⟩ :=
          checkedTyAt_arbitrary_cofinite_of_fresh hren hwf0
            (by
              obtain ⟨k, ⟨ht0⟩⟩ := sourceDomainValid.tof_tvalid
              exact ⟨k, ⟨by simpa only [htof10] using ht0⟩⟩)
            htof10 sourceDomainValid hxGamma hout' hxPsi hxb10
            hxtauV10 hxb11 hlctauV10 hlctauVOut
        rw [← htof10] at hcodOut
        exact ⟨.piTy tauV10 (ValTy.closeRec 0 x tauVOut),
          .frame hsource hdom10 Lout hcodOut⟩

theorem checkedFreeStdPairSourceExactDepth_of_spaceCob
    (depth : Nat) (hcob : CheckedFreeStdPairSpaceCobDepth depth)
    (hren : CheckedRenameLaws) : CheckedFreeStdPairSourceExactDepth depth := by
  intro Psi0 hrootStored Gamma Psi source target pair
    hsource htarget hfuture hanchors hP hcov hstored Delta hwf
    hiSource hiTarget htof
  exact checkedFreeStdPairSourceExactN_of_spaceCob depth hcob hren
    (Ty.size (Basis.tof source)) Psi0 hrootStored Gamma Psi source target
    pair hsource htarget hfuture hanchors hP hcov hstored Delta hwf
    hiSource hiTarget htof le_rfl

private def CheckedFreeStdPairTermTransportN
    (depth size : Nat) : Prop :=
  forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx) (e : Term)
    (source target : Basis) (v : ValExpr) (tauV : ValTy),
    CheckedFreeStdPairBasisDepth Psi0 depth Gamma source target ->
    Basis.BasisValid Gamma source -> Basis.BasisValid Gamma target ->
    CheckedStdFuture Psi0 Psi ->
    CheckedExactLookupStore Gamma Psi ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
    Basis.IsTyBasis source -> Basis.IsTyBasis target ->
    Basis.tof target = Basis.tof source ->
    Ty.size (Basis.tof source) <= size ->
    C.Term Delta Gamma Psi e source v tauV ->
    exists w tauW, C.Term Delta Gamma Psi e target w tauW

private theorem checkedFreeStdPairTermTransportN_of_targetExact_spaceCob
    (depth : Nat)
    (hexact : CheckedFreeStdPairTargetExactDepth depth)
    (hcob : CheckedFreeStdPairSpaceCobDepth depth)
    (hren : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    forall size, CheckedFreeStdPairTermTransportN depth size := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
    intro Psi0' hrootStored' Delta' Gamma' Psi' e'
      source' target' v' tauV' pair' hsource' htarget'
      hfuture' hanchors' hP' hcov' hstored' hwf' hiSource' hiTarget'
      htof' hsize' hterm'
    cases hsourceTy : Basis.tof source' with
    | space s =>
        have hsSource : Basis.IsSpaceBasis source' :=
          hiSource'.toIsSpaceBasis (Basis.ne_frame_of_tof_space hsourceTy)
        have hsTarget : Basis.IsSpaceBasis target' :=
          hiTarget'.toIsSpaceBasis
            (Basis.ne_frame_of_tof_space (htof'.trans hsourceTy))
        obtain ⟨sv, htau, _⟩ :=
          checkedTyAt_space_inv_full hsourceTy hterm'.tyAt
        subst tauV'
        exact checkedFreeStdPairSpaceTermTransport depth hcob hrootStored'
          pair' hsource' htarget' hfuture' hanchors' hP' hcov' hstored' hwf'
          hsSource hsTarget htof' hterm'
    | piTy tau0 tau1 =>
        obtain ⟨hsourceTyping⟩ := hterm'.hasType
        have hsourceTyping' : HasType Delta' Gamma' e' (.piTy tau0 tau1) := by
          rwa [hsourceTy] at hsourceTyping
        have hDelta : Delta' = ∅ := HasType.pi_linear_empty hsourceTyping'
        subst Delta'
        obtain ⟨b10, b11, rfl, htof10, htof11⟩ :=
          Basis.tof_piTy_inv hsourceTy
        obtain ⟨b20, b21, rfl, htof20, htof21⟩ :=
          Basis.tof_piTy_inv (htof'.trans hsourceTy)
        rw [hsourceTy] at hsize'
        simp only [Ty.size] at hsize'
        have hsmall0 : Ty.size tau0 < size := by omega
        have hsmall1 : Ty.size tau1 < size := by omega
        have hdepth : depth ≠ 0 := by
          intro hz
          subst depth
          simp only [CheckedFreeStdPairBasisDepth] at pair'
          obtain ⟨_, ⟨_, hzero⟩, _⟩ := pair'
          cases hzero
        obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdepth
        obtain ⟨tauV2, htargetAt⟩ :=
          hexact Psi0' hrootStored' Gamma' Psi'
            (.frame b10 b11) (.frame b20 b21) pair'
            hsource' htarget' hfuture' hanchors' hP' hcov' hstored'
            (∅ : LCtx) hwf' hiSource' hiTarget' htof'
        simp only [CheckedFreeStdPairBasisDepth] at pair'
        obtain ⟨_hdomTof, _hcodTof, sourceAvoid, targetAvoid,
          sourceDomainValid, targetDomainValid, sourceBodyValid,
          targetBodyValid, _sourceSelfDomain, _targetSelfDomain,
          _sourceOwn, _targetOwn, underBinder⟩ := pair'
        obtain ⟨hi10, hi11⟩ := hiSource'
        obtain ⟨hi20, hi21⟩ := hiTarget'
        obtain ⟨tauV10, tauV11, rfl, hdom10, Lsrc, hcod10⟩ :=
          checkedTyAt_frame_inv_full hterm'.tyAt
        obtain ⟨tauV20, tauV21, rfl, hdom20, Ltgt, hcod20⟩ :=
          checkedTyAt_frame_inv_full htargetAt
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
          (EvalCtx.avoidB Psi' ∪ Gamma'.keys ∪ sourceAvoid ∪
            targetAvoid ∪ Lsrc ∪ Ltgt ∪ Basis.fv b20 ∪ Basis.fv b21 ∪
            Term.fv e' ∪ ValTy.fv tauV20)
        simp only [Finset.mem_union, not_or] at hx
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hxPsi, hxGammaKeys⟩, hxSourceAvoid⟩,
          hxTargetAvoid⟩, hxLsrc⟩, hxLtgt⟩, hxb20⟩, hxb21⟩, hxe⟩,
          hxtauV20⟩ := hx
        have hxGamma : x ∉ Gamma' := by
          intro hm
          exact hxGammaKeys (Finmap.mem_keys.mpr hm)
        have hfresh : (x, b20) ∉ Psi' :=
          (EvalCtx.avoidB_spec hxPsi).1 b20
        obtain ⟨hPx, hcovx, hstoredx⟩ :=
          V2.pcarrier_extend_transport
            (V2.transportN (Ty.size (Basis.tof b20)))
            hP' hcov' hstored' targetDomainValid hi20 hdom20.erase
            hfresh le_rfl
        let GammaX := Finmap.insert x (Basis.tof b20) Gamma'
        let PsiX := Psi'.extend x b20 (.var x tauV20)
        have hwfx : V2.CtxWF' (∅ : LCtx) GammaX :=
          RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
            (b := b20) hwf' Finmap.notMem_empty hxGamma targetDomainValid
        have hinc : NLCtxIncl Gamma' GammaX :=
          (NLCtxIncl.refl Gamma').insert_right hxGamma (Basis.tof b20)
        have hanchorsX : CheckedExactLookupStore GammaX PsiX :=
          CheckedExactLookupStore.nlMono
            (CheckedExactLookupStore.extend hanchors'
              (not_mem_names_of_not_mem_avoidB hxPsi) hdom20)
            hinc
        have hb20x : Basis.BasisValid GammaX b20 :=
          raw_basisValid_mono targetDomainValid hinc
        have hb10x : Basis.BasisValid GammaX b10 :=
          raw_basisValid_mono sourceDomainValid hinc
        have hdom20x : C.TyAt GammaX PsiX b20 tauV20 :=
          C.TyAt.weaken (checkedTyAt_extend hdom20 hxPsi) hinc
        have hvar20 : C.Term (∅ : LCtx) GammaX PsiX (.var x) b20
            (.var x tauV20) tauV20 := by
          apply C.Term.var_nlin
          · simp [PsiX, EvalCtx.lookup, EvalCtx.extend,
              Finmap.lookup_insert]
          · simp [GammaX, Finmap.lookup_insert]
          · exact hb20x
          · exact hdom20x
        obtain ⟨domainPair, codomainPair⟩ :=
          underBinder Psi' hfuture' x
            (not_mem_names_of_not_mem_avoidB hxPsi)
            hxSourceAvoid hxTargetAvoid
            tauV20 hdom20
        obtain ⟨arg10, tauVArg, harg10⟩ :=
          ih (Ty.size tau0) hsmall0
            PsiX hstoredx (∅ : LCtx) GammaX PsiX (.var x)
            b20 b10 (.var x tauV20) tauV20 domainPair hb20x hb10x
            (CheckedStdFuture.refl _) hanchorsX hPx hcovx hstoredx hwfx
            hi20 hi10 (htof10.trans htof20.symm)
            (by rw [htof20]) hvar20
        have htypedX : Nonempty (HasType (∅ : LCtx) GammaX e'
            (Basis.tof (.frame b10 b11))) :=
          hasType_mono_nl_checked hterm'.hasType hinc
            (fun _ hm => False.elim (Finmap.notMem_empty hm))
        have hsourceAtX : C.TyAt GammaX PsiX (.frame b10 b11)
            (.piTy tauV10 tauV11) :=
          C.TyAt.weaken (checkedTyAt_extend hterm'.tyAt hxPsi) hinc
        have hfunX : C.Term (∅ : LCtx) GammaX PsiX e'
            (.frame b10 b11) v' (.piTy tauV10 tauV11) :=
          C.Term.weaken (checkedTerm_extend hterm' hxPsi) hinc (Graded.CtxDisj.empty _)
        obtain ⟨_tauV10x, _tauV11x, _hsrcV, hdom10x,
          LsrcX, hcodSrcX⟩ := checkedTyAt_frame_inv_full hfunX.tyAt
        obtain ⟨arg10', tauVCut, harg10', hcut⟩ :=
          checkedCodomainCut happCut hPx hcovx hwfx harg10 hdom10x
            LsrcX hcodSrcX
        have happTyped : Nonempty (HasType (∅ : LCtx) GammaX
            (.appN e' (.var x))
            (Basis.tof (Basis.instantiate (.var x) b11))) := by
          obtain ⟨hf⟩ := hfunX.hasType
          obtain ⟨ha⟩ := harg10'.hasType
          refine ⟨?_⟩
          simpa only [Basis.tof, Basis.instantiate, Basis.tof_openRec,
            Ty.instantiate] using HasType.app_nonlinear hf ha
        have hb11x : Basis.BasisValid GammaX (Basis.openVar x b11) := by
          simpa only [GammaX, htof10, htof20] using
            sourceBodyValid x hxSourceAvoid
        have hb21x : Basis.BasisValid GammaX (Basis.openVar x b21) :=
          targetBodyValid x hxTargetAvoid
        have happ : C.Term (∅ : LCtx) GammaX PsiX
            (.appN e' (.var x)) (Basis.openVar x b11)
            (.applyAt v' arg10' tauVCut) tauVCut := by
          have happ0 := C.Term.appN_val happTyped hb11x hcut hfunX harg10'
          simpa only [Basis.instantiate] using happ0
        have htofcod : Basis.tof (Basis.openVar x b21) =
            Basis.tof (Basis.openVar x b11) := by
          show Basis.tof (Basis.openRec 0 (.var x) b21) =
            Basis.tof (Basis.openRec 0 (.var x) b11)
          rw [Basis.tof_openRec, Basis.tof_openRec, htof21, htof11]
        have hsizecod : Ty.size (Basis.tof (Basis.openVar x b11)) <=
            Ty.size tau1 := by
          show Ty.size (Basis.tof (Basis.openRec 0 (.var x) b11)) <=
            Ty.size tau1
          rw [Basis.tof_openRec, htof11]
          exact le_of_eq (Ty.size_openVar 0 x tau1)
        obtain ⟨w, tauVW, hw⟩ :=
          ih (Ty.size tau1) hsmall1
            PsiX hstoredx (∅ : LCtx) GammaX PsiX
            (.appN e' (.var x)) (Basis.openVar x b11)
            (Basis.openVar x b21) (.applyAt v' arg10' tauVCut) tauVCut
            codomainPair hb11x hb21x (CheckedStdFuture.refl _)
            hanchorsX hPx hcovx hstoredx hwfx
            (Basis.IsTyBasis.openRec (.var x) 0 hi11)
            (Basis.IsTyBasis.openRec (.var x) 0 hi21)
            htofcod hsizecod happ
        have htargetCodX := hcod20 x hxLtgt
        rw [htof20] at htargetCodX
        have hw' : C.Term (∅ : LCtx)
            (Finmap.insert x tau0 Gamma') PsiX
            (.appN e' (.var x)) (Basis.openVar x b21) _
            (ValTy.openVar x tauV20 tauV21) :=
          RawCertifiedProgressScratch.retag
            (by simpa only [GammaX, htof20] using hw) htargetCodX
        have hlctauV20 : ValTy.lc tauV20 :=
          evalT_lc hdom20.erase hP'.1.toEvalCtxLc
        have hlcw : ValExpr.lc _ :=
          opStep_lc hw'.erase hPx.1.toEvalCtxLc
        have hlctauVW : ValTy.lc (ValTy.openVar x tauV20 tauV21) :=
          evalT_lc htargetCodX.erase hPx.1.toEvalCtxLc
        obtain ⟨Lbody, hbody⟩ :=
          checkedTerm_arbitrary_frameEta_cofinite_of_fresh hren hwf'
            (by
              obtain ⟨k, ⟨ht0⟩⟩ := targetDomainValid.tof_tvalid
              exact ⟨k, ⟨by simpa only [htof20] using ht0⟩⟩)
            htof20 targetDomainValid hxGamma hw' hxPsi hxb20 hxtauV20
            hxe hxb21 hlctauV20 hlcw hlctauVW
        rw [← htof20] at hbody
        let tauVOut :=
          ValTy.closeRec 0 x (ValTy.openVar x tauV20 tauV21)
        let bodyOut := ValExpr.closeRec 0 x
          (ValExpr.reshap w (ValTy.openVar x tauV20 tauV21) tauVW)
        have htargetAt' : C.TyAt Gamma' Psi' (.frame b20 b21)
            (.piTy tauV20 tauVOut) := by
          apply C.TyAt.frame htarget' hdom20 Lbody _
          intro y hy
          exact (hbody y hy).tyAt
        have htypedTarget : Nonempty (HasType (∅ : LCtx) Gamma' e'
            (Basis.tof (.frame b20 b21))) := by
          rw [htof']
          exact hterm'.hasType
        exact ⟨.vlam tauV20 tauVOut
            (.reshap bodyOut tauVOut tauVOut),
          .piTy tauV20 tauVOut,
          C.Term.frame_eta htypedTarget htarget' htargetAt' hdom20
            Lbody hbody (fun y hy => (hbody y hy).tyAt)⟩

/-- The complete concrete-pair transport executor, conditional only on the
two directional services used at its leaves.  The recursive frame calls keep
`depth` fixed and strictly decrease source type size. -/
theorem checkedFreeStdPairTermTransportDepth_of_targetExact_spaceCob
    (depth : Nat)
    (hexact : CheckedFreeStdPairTargetExactDepth depth)
    (hcob : CheckedFreeStdPairSpaceCobDepth depth)
    (hren : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    CheckedFreeStdPairTermTransportDepth depth := by
  intro Psi0 hrootStored Delta Gamma Psi e source target v tauV
    pair hsource htarget hfuture hanchors hP hcov hstored hwf
    hiSource hiTarget htof hterm
  exact checkedFreeStdPairTermTransportN_of_targetExact_spaceCob
    depth hexact hcob hren happCut (Ty.size (Basis.tof source))
    Psi0 hrootStored Delta Gamma Psi e source target v tauV
    pair hsource htarget hfuture hanchors hP hcov hstored hwf
    hiSource hiTarget htof le_rfl hterm

/-- After endpoint-own frame recursion was added to the certificate, space
COB is the only semantic service still needed by concrete transport: target
exactness is derived internally and then consumed by the frame branch. -/
theorem checkedFreeStdPairTermTransportDepth_of_spaceCob
    (depth : Nat) (hcob : CheckedFreeStdPairSpaceCobDepth depth)
    (hren : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    CheckedFreeStdPairTermTransportDepth depth :=
  checkedFreeStdPairTermTransportDepth_of_targetExact_spaceCob depth
    (checkedFreeStdPairTargetExactDepth_of_spaceCob depth hcob hren)
    hcob hren happCut

theorem checkedFreeStdPairTargetExactDepth_zero
    (hren : CheckedRenameLaws) : CheckedFreeStdPairTargetExactDepth 0 :=
  checkedFreeStdPairTargetExactDepth_of_spaceCob 0 checkedFreeStdPairSpaceCobDepth_zero hren

theorem checkedFreeStdPairSourceExactDepth_zero
    (hren : CheckedRenameLaws) : CheckedFreeStdPairSourceExactDepth 0 :=
  checkedFreeStdPairSourceExactDepth_of_spaceCob 0 checkedFreeStdPairSpaceCobDepth_zero hren

theorem checkedFreeStdPairTermTransportDepth_zero
    (hren : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    CheckedFreeStdPairTermTransportDepth 0 :=
  checkedFreeStdPairTermTransportDepth_of_spaceCob 0
    checkedFreeStdPairSpaceCobDepth_zero hren happCut

end RawCertifiedPairFreeStandardServices
end GLang
