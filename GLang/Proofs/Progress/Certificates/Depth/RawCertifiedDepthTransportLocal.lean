import GLang.Proofs.Progress.Certificates.RawCertifiedWeaken
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedDepthExactLocal

/-!
# Call-local checked basis transport

This is the higher-order source-to-target transport induction with one
proof-indexed depth certificate for each basis actually involved.  It does
not quantify over unrelated bases or evaluator worlds.  Frame recursion
uses the re-rooted body fields in those two certificates, at the evaluator
extended by the target domain basis.
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 6000

namespace GLang
namespace RawCertifiedDepthTransportLocal

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedSelectedProgressMaster
open RawCertifiedCobDepthLayerSpike
open RawCertifiedPiBasisTransport
open RawCertifiedDepthExact
open RawCertifiedDepthExactLocal

/-- Space-typed transport using only the two basis certificates appearing in
this call. -/
private theorem checkedSpaceTermTransportDepth_local
    (depth : Nat) (hcob : CheckedCobToStdDepthAll depth)
    {Psi0 : EvalCtx} (hrootStored : V2.StoredWF Psi0)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {e : Term}
    {b1 b2 : Basis} {v1 : ValExpr} {sv : ValSpace}
    (hb1 : Basis.BasisValid Gamma b1)
    (side1 : CheckedLocalSideBasisDepth Psi0 depth hb1)
    (hb2 : Basis.BasisValid Gamma b2)
    (side2 : CheckedLocalSideBasisDepth Psi0 depth hb2)
    (hfuture : CheckedStdFuture Psi0 Psi)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi) (hwf : V2.CtxWF' Delta Gamma)
    (hs1 : Basis.IsSpaceBasis b1) (hs2 : Basis.IsSpaceBasis b2)
    (htofeq : Basis.tof b2 = Basis.tof b1)
    (hterm : C.Term Delta Gamma Psi e b1 v1 (.space sv)) :
    exists v2 tauV2, C.Term Delta Gamma Psi e b2 v2 tauV2 := by
  have hwf0 := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
  obtain ⟨env1, hcob1⟩ := hcob Psi0 hrootStored hb1 side1
    hfuture hP hcov hwf0 hs1
  obtain ⟨env2, hcob2⟩ := hcob Psi0 hrootStored hb2 side2
    hfuture hP hcov hwf0 hs2
  have hspace1 : C.Space Gamma Psi (Basis.sof b1) sv := by
    obtain ⟨sv', heq, hspace⟩ :=
      checkedTyAt_space_inv_full hs1.tof_eq hterm.tyAt
    injection heq with heq'
    subst sv'
    exact hspace
  have hsof : Basis.sof b2 = Basis.sof b1 :=
    V2.sof_of_tof_eq_space (htofeq.trans hs1.tof_eq)
  have hspace2 : C.Space Gamma Psi (Basis.sof b2) sv := by
    rw [hsof]
    exact hspace1
  rw [htofeq] at hcob2
  obtain ⟨_k, ⟨htvalid⟩⟩ := hb1.tof_tvalid
  have hstdValid : Basis.BasisValid Gamma (Basis.std (Basis.tof b1)) :=
    Basis.std_valid _ htvalid
  obtain ⟨env, hbetween⟩ : exists env, C.Cob Gamma Psi b1 env b2 :=
    ⟨_, .trans hb1 hb2 hcob1 (.inverse hstdValid hb2 hcob2) hspace1⟩
  have htyped2 : Nonempty (HasType Delta Gamma e (Basis.tof b2)) := by
    rw [htofeq]
    exact hterm.hasType
  have htype2 : C.TyAt Gamma Psi b2 (.space sv) :=
    .space hs2.tof_eq hb2 hspace2
  exact ⟨_, .space sv,
    .cob hs2.tof_eq hs1.tof_eq htyped2 hb2 htype2 hterm
      hbetween hspace2⟩

/-- Transport at one source-type size, with local certificates for the two
bases. -/
private def CheckedTermTransportLocalN (depth size : Nat) : Prop :=
  forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx) (e : Term)
    (b1 b2 : Basis) (v1 : ValExpr) (tauV1 : ValTy),
    (hb1 : Basis.BasisValid Gamma b1) ->
    CheckedLocalSideBasisDepth Psi0 depth hb1 ->
    (hb2 : Basis.BasisValid Gamma b2) ->
    CheckedLocalSideBasisDepth Psi0 depth hb2 ->
    CheckedStdFuture Psi0 Psi ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
    Basis.IsTyBasis b1 -> Basis.IsTyBasis b2 ->
    Basis.tof b2 = Basis.tof b1 -> Ty.size (Basis.tof b1) <= size ->
    C.Term Delta Gamma Psi e b1 v1 tauV1 ->
    exists v2 tauV2, C.Term Delta Gamma Psi e b2 v2 tauV2

/-- Strong type-size induction for local checked transport.  Exact target
types are obtained from the already-local exact theorem, so no simultaneous
global TyAt transport premise is required. -/
private theorem checkedTermTransportLocalN_of_allCob
    (depth : Nat) (hcob : CheckedCobToStdDepthAll depth)
    (hren : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    forall size, CheckedTermTransportLocalN depth size := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
    intro Psi0 hrootStored Delta Gamma Psi e b1 b2 v1 tauV1
      hb1 side1 hb2 side2 hfuture hP hcov hstored hwf
      hi1 hi2 htofeq hsize hterm
    cases hsource : Basis.tof b1 with
    | space s =>
        have hs1 : Basis.IsSpaceBasis b1 :=
          hi1.toIsSpaceBasis (Basis.ne_frame_of_tof_space hsource)
        have hs2 : Basis.IsSpaceBasis b2 :=
          hi2.toIsSpaceBasis
            (Basis.ne_frame_of_tof_space (htofeq.trans hsource))
        obtain ⟨sv, htauV1, _⟩ :=
          checkedTyAt_space_inv_full hsource hterm.tyAt
        subst tauV1
        exact checkedSpaceTermTransportDepth_local depth hcob hrootStored
          hb1 side1 hb2 side2 hfuture hP hcov hstored hwf
          hs1 hs2 htofeq hterm
    | piTy tau0 tau1 =>
        obtain ⟨hsourceTyping⟩ := hterm.hasType
        have hsourceTyping' : HasType Delta Gamma e (.piTy tau0 tau1) := by
          rwa [hsource] at hsourceTyping
        have hDelta : Delta = ∅ := HasType.pi_linear_empty hsourceTyping'
        subst Delta
        obtain ⟨b10, b11, rfl, htof10, htof11⟩ :=
          Basis.tof_piTy_inv hsource
        obtain ⟨b20, b21, rfl, htof20, htof21⟩ :=
          Basis.tof_piTy_inv (htofeq.trans hsource)
        rw [hsource] at hsize
        simp only [Ty.size] at hsize
        have hsmall0 : Ty.size tau0 < size := by omega
        have hsmall1 : Ty.size tau1 < size := by omega
        have hdepth : depth ≠ 0 := by
          intro hz
          subst depth
          have hzero : CheckedLocalSideBasisZero hb1 := by
            simpa only [CheckedLocalSideBasisDepth] using side1
          cases hzero
        obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdepth
        obtain ⟨_ks0, _ks1, Ls1, hb10, hbody11,
          side10, sideBody11, _hts, _sideTs⟩ := side1.frame_parts
        obtain ⟨_kt0, _kt1, Ls2, hb20, hbody21,
          side20, sideBody21, _htt, _sideTt⟩ := side2.frame_parts
        obtain ⟨hi10, hi11⟩ := hi1
        obtain ⟨hi20, hi21⟩ := hi2
        have hexact : CheckedExactBasisTyProgressDepth Psi0 (d + 1) :=
          checkedExactBasisTyProgressDepth_of_allCob_local
            (d + 1) hcob hren Psi0 hrootStored
        obtain ⟨tauV2, htargetAt⟩ := hexact hb2 hfuture side2
          hP hcov hstored (∅ : LCtx) hwf ⟨hi20, hi21⟩
        obtain ⟨tauV10, tauV11, rfl, hdom10, Lsrc, hcod10⟩ :=
          checkedTyAt_frame_inv_full hterm.tyAt
        obtain ⟨tauV20, tauV21, rfl, hdom20, Ltgt, hcod20⟩ :=
          checkedTyAt_frame_inv_full htargetAt
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
          (EvalCtx.avoidB Psi ∪ Gamma.keys ∪ Ls1 ∪ Ls2 ∪ Lsrc ∪ Ltgt ∪
            Basis.fv b20 ∪ Basis.fv b21 ∪ Term.fv e ∪ ValTy.fv tauV20)
        simp only [Finset.mem_union, not_or] at hx
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hxPsi, hxGammaKeys⟩, hxLs1⟩, hxLs2⟩,
          hxLsrc⟩, hxLtgt⟩, hxb20⟩, hxb21⟩, hxe⟩, hxtauV20⟩ := hx
        have hxGamma : x ∉ Gamma := by
          intro hm
          exact hxGammaKeys (Finmap.mem_keys.mpr hm)
        have hfresh : (x, b20) ∉ Psi :=
          (EvalCtx.avoidB_spec hxPsi).1 b20
        obtain ⟨hPx, hcovx, hstoredx⟩ :=
          V2.pcarrier_extend_transport (V2.transportN (Ty.size tau0))
            hP hcov hstored hb20 hi20 hdom20.erase hfresh
            (by rw [htof20])
        have hwfx : V2.CtxWF' (∅ : LCtx)
            (Finmap.insert x (Basis.tof b20) Gamma) :=
          RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
            (b := b20) hwf Finmap.notMem_empty hxGamma hb20
        have hinc : NLCtxIncl Gamma
            (Finmap.insert x (Basis.tof b20) Gamma) :=
          (NLCtxIncl.refl Gamma).insert_right hxGamma (Basis.tof b20)
        have hb20x : Basis.BasisValid
            (Finmap.insert x (Basis.tof b20) Gamma) b20 :=
          raw_basisValid_mono hb20 hinc
        have hb10x : Basis.BasisValid
            (Finmap.insert x (Basis.tof b20) Gamma) b10 := by
          have h := raw_basisValid_mono hb10 hinc
          exact h
        have hdom20x : C.TyAt
            (Finmap.insert x (Basis.tof b20) Gamma)
            (Psi.extend x b20 (.var x tauV20)) b20 tauV20 :=
          C.TyAt.weaken (checkedTyAt_extend hdom20 hxPsi) hinc
        have hvar20 : C.Term (∅ : LCtx)
            (Finmap.insert x (Basis.tof b20) Gamma)
            (Psi.extend x b20 (.var x tauV20)) (.var x) b20
            (.var x tauV20) tauV20 := by
          apply C.Term.var_nlin
          · rw [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert]
          · rw [Finmap.lookup_insert]
          · exact hb20x
          · exact hdom20x
        obtain ⟨side20At, side21x⟩ :=
          sideBody21 Psi hfuture x hxLs2 b20
            (.var x tauV20) hb20 rfl
        have side20x : CheckedLocalSideBasisDepth
            (Psi.extend x b20 (.var x tauV20)) (d + 1) hb20x :=
          side20At hb20x
        obtain ⟨side10At, side11At⟩ :=
          sideBody11 Psi hfuture x hxLs1 b20
            (.var x tauV20) hb20 (htof20.trans htof10.symm)
        have hb10ForSide : Basis.BasisValid
            (Finmap.insert x (Basis.tof b10) Gamma) b10 := by
          simpa only [htof10, htof20] using hb10x
        have side10x : CheckedLocalSideBasisDepth
            (Psi.extend x b20 (.var x tauV20)) (d + 1) hb10x := by
          simpa only [htof10, htof20] using side10At hb10ForSide
        obtain ⟨arg10, tauVArg, harg10⟩ :=
          ih (Ty.size tau0) hsmall0
            (Psi.extend x b20 (.var x tauV20)) hstoredx
            (∅ : LCtx) (Finmap.insert x (Basis.tof b20) Gamma)
            (Psi.extend x b20 (.var x tauV20)) (.var x)
            b20 b10 (.var x tauV20) tauV20
            hb20x side20x hb10x side10x (CheckedStdFuture.refl _)
            hPx hcovx hstoredx hwfx hi20 hi10
            (htof10.trans htof20.symm) (by rw [htof20]) hvar20
        have htypedX : Nonempty (HasType (∅ : LCtx)
            (Finmap.insert x (Basis.tof b20) Gamma) e
            (Basis.tof (.frame b10 b11))) := by
          have hs := hasType_mono_nl_checked hterm.hasType hinc
            (fun _ hm => False.elim (Finmap.notMem_empty hm))
          exact hs
        have hsourceAtX : C.TyAt
            (Finmap.insert x (Basis.tof b20) Gamma)
            (Psi.extend x b20 (.var x tauV20)) (.frame b10 b11)
            (.piTy tauV10 tauV11) :=
          C.TyAt.weaken (checkedTyAt_extend hterm.tyAt hxPsi) hinc
        have hfunX : C.Term (∅ : LCtx)
            (Finmap.insert x (Basis.tof b20) Gamma)
            (Psi.extend x b20 (.var x tauV20)) e (.frame b10 b11) v1
            (.piTy tauV10 tauV11) :=
          C.Term.weaken (checkedTerm_extend hterm hxPsi) hinc (Graded.CtxDisj.empty _)
        obtain ⟨_tauV10x, _tauV11x, _hsrcV, hdom10x,
          LsrcX, hcodSrcX⟩ := checkedTyAt_frame_inv_full hfunX.tyAt
        obtain ⟨arg10', tauVCut, harg10', hcut⟩ :=
          checkedCodomainCut happCut hPx hcovx hwfx harg10 hdom10x
            LsrcX hcodSrcX
        have happTyped : Nonempty (HasType (∅ : LCtx)
            (Finmap.insert x (Basis.tof b20) Gamma) (.appN e (.var x))
            (Basis.tof (Basis.instantiate (.var x) b11))) := by
          obtain ⟨hf⟩ := hfunX.hasType
          obtain ⟨ha⟩ := harg10'.hasType
          refine ⟨?_⟩
          simpa only [Basis.tof, Basis.instantiate, Basis.tof_openRec,
            Ty.instantiate] using HasType.app_nonlinear hf ha
        have hb11x : Basis.BasisValid
            (Finmap.insert x (Basis.tof b20) Gamma)
            (Basis.openVar x b11) := by
          simpa only [htof10, htof20] using hbody11 x hxLs1
        have hb21x : Basis.BasisValid
            (Finmap.insert x (Basis.tof b20) Gamma)
            (Basis.openVar x b21) := hbody21 x hxLs2
        have side11x : CheckedLocalSideBasisDepth
            (Psi.extend x b20 (.var x tauV20)) (d + 1) hb11x := by
          simpa only [htof10, htof20] using side11At
        have side21x' : CheckedLocalSideBasisDepth
            (Psi.extend x b20 (.var x tauV20)) (d + 1) hb21x := by
          exact side21x
        have happ : C.Term (∅ : LCtx)
            (Finmap.insert x (Basis.tof b20) Gamma)
            (Psi.extend x b20 (.var x tauV20)) (.appN e (.var x))
            (Basis.openVar x b11) (.applyAt v1 arg10' tauVCut) tauVCut := by
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
            (Psi.extend x b20 (.var x tauV20)) hstoredx
            (∅ : LCtx) (Finmap.insert x (Basis.tof b20) Gamma)
            (Psi.extend x b20 (.var x tauV20)) (.appN e (.var x))
            (Basis.openVar x b11) (Basis.openVar x b21)
            (.applyAt v1 arg10' tauVCut) tauVCut
            hb11x side11x hb21x side21x' (CheckedStdFuture.refl _)
            hPx hcovx hstoredx hwfx
            (Basis.IsTyBasis.openRec (.var x) 0 hi11)
            (Basis.IsTyBasis.openRec (.var x) 0 hi21)
            htofcod hsizecod happ
        have htargetCodX := hcod20 x hxLtgt
        rw [htof20] at htargetCodX
        have hw' : C.Term (∅ : LCtx)
            (Finmap.insert x tau0 Gamma)
            (Psi.extend x b20 (.var x tauV20)) (.appN e (.var x))
            (Basis.openVar x b21) _ (ValTy.openVar x tauV20 tauV21) :=
          RawCertifiedProgressScratch.retag (by simpa only [htof20] using hw)
            htargetCodX
        have hlctauV20 : ValTy.lc tauV20 :=
          evalT_lc hdom20.erase hP.1.toEvalCtxLc
        have hlcw : ValExpr.lc _ :=
          opStep_lc hw'.erase hPx.1.toEvalCtxLc
        have hlctauVW : ValTy.lc (ValTy.openVar x tauV20 tauV21) :=
          evalT_lc htargetCodX.erase hPx.1.toEvalCtxLc
        obtain ⟨Lbody, hbody⟩ :=
          checkedTerm_arbitrary_frameEta_cofinite_of_fresh hren hwf
            (by
              obtain ⟨k, ⟨ht0⟩⟩ := hb20.tof_tvalid
              exact ⟨k, ⟨by simpa only [htof20] using ht0⟩⟩)
            htof20 hb20 hxGamma hw' hxPsi hxb20 hxtauV20 hxe hxb21
            hlctauV20 hlcw hlctauVW
        rw [← htof20] at hbody
        let tauVOut :=
          ValTy.closeRec 0 x (ValTy.openVar x tauV20 tauV21)
        let bodyOut := ValExpr.closeRec 0 x
          (ValExpr.reshap w (ValTy.openVar x tauV20 tauV21) tauVW)
        have htargetAt' : C.TyAt Gamma Psi (.frame b20 b21)
            (.piTy tauV20 tauVOut) := by
          apply C.TyAt.frame hb2 hdom20 Lbody _
          intro y hy
          exact (hbody y hy).tyAt
        have htypedTarget : Nonempty (HasType (∅ : LCtx) Gamma e
            (Basis.tof (.frame b20 b21))) := by
          rw [htofeq]
          exact hterm.hasType
        exact ⟨.vlam tauV20 tauVOut (.reshap bodyOut tauVOut tauVOut),
          .piTy tauV20 tauVOut,
          C.Term.frame_eta htypedTarget hb2 htargetAt' hdom20 Lbody
            hbody (fun y hy => (hbody y hy).tyAt)⟩

/-- Fully local transport between the two explicitly certified bases. -/
theorem checkedTermTransportDepth_local
    (depth : Nat) (hcob : CheckedCobToStdDepthAll depth)
    (hren : CheckedRenameLaws) (happCut : CheckedTyAtAppCut) :
    forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
      (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx) (e : Term)
      (b1 b2 : Basis) (v1 : ValExpr) (tauV1 : ValTy),
      (hb1 : Basis.BasisValid Gamma b1) ->
      CheckedLocalSideBasisDepth Psi0 depth hb1 ->
      (hb2 : Basis.BasisValid Gamma b2) ->
      CheckedLocalSideBasisDepth Psi0 depth hb2 ->
      CheckedStdFuture Psi0 Psi ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
      Basis.IsTyBasis b1 -> Basis.IsTyBasis b2 ->
      Basis.tof b2 = Basis.tof b1 ->
      C.Term Delta Gamma Psi e b1 v1 tauV1 ->
      exists v2 tauV2, C.Term Delta Gamma Psi e b2 v2 tauV2 := by
  intro Psi0 hrootStored Delta Gamma Psi e b1 b2 v1 tauV1
    hb1 side1 hb2 side2 hfuture hP hcov hstored hwf hi1 hi2 htof hterm
  exact checkedTermTransportLocalN_of_allCob depth hcob hren happCut
    (Ty.size (Basis.tof b1)) Psi0 hrootStored Delta Gamma Psi e b1 b2
    v1 tauV1 hb1 side1 hb2 side2 hfuture hP hcov hstored hwf
    hi1 hi2 htof le_rfl hterm

end RawCertifiedDepthTransportLocal
end GLang
