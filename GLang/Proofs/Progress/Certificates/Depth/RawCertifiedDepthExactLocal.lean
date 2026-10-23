import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedDepthExact

namespace GLang
namespace RawCertifiedDepthExactLocal

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedSelectedProgressMaster
open RawCertifiedCobDepthLayerSpike
open RawCertifiedPiBasisTransport
open RawCertifiedExactBasisTyProgress
open RawCertifiedDepthExact

/-- The exact result at a bounded source-type size, consuming one local
basis-depth certificate.  The root evaluator is explicit because frame
recursion creates a new root. -/
private def CheckedExactLocalN (n size : Nat) : Prop :=
  forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0)
    (Gamma : NLCtx) (Psi : EvalCtx) (b : Basis),
    (hb : Basis.BasisValid Gamma b) ->
    CheckedStdFuture Psi0 Psi ->
    CheckedLocalSideBasisDepth Psi0 n hb ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> forall (Delta : LCtx), V2.CtxWF' Delta Gamma ->
    Basis.IsTyBasis b -> Ty.size (Basis.tof b) <= size ->
    exists tauv, C.TyAt Gamma Psi b tauv

/-- Strong induction on source type size.  Cross-language recursion is
already bounded by `n`; the frame domain/codomain calls strictly decrease
`Ty.size`, and the frame certificate changes its root to the evaluator
actually installed by the checked rule. -/
private theorem checkedExactLocalN_of_allCob
    (n : Nat)
    (hcob : CheckedCobToStdDepthAll n)
    (hren : CheckedRenameLaws) :
    forall size, CheckedExactLocalN n size := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
    intro Psi0 hrootStored Gamma Psi b hb hfuture hside
      hP hcov hstored Delta hwf hisTy hsize
    have hwf0 := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
    cases htof : Basis.tof b with
    | space s =>
        have hspace : Basis.IsSpaceBasis b :=
          hisTy.toIsSpaceBasis (Basis.ne_frame_of_tof_space htof)
        obtain ⟨env, hbb⟩ := hcob Psi0 hrootStored hb hside
          hfuture hP hcov hwf0 hspace
        obtain ⟨sv, hsv⟩ := checkedCob_sourceSpace hbb
        exact ⟨.space sv, .space hspace.tof_eq hb hsv⟩
    | piTy tau0 tau1 =>
        obtain ⟨b0, b1, rfl, htof0, htof1⟩ :=
          Basis.tof_piTy_inv htof
        rw [htof] at hsize
        simp only [Ty.size] at hsize
        have hsmall0 : Ty.size tau0 < size := by omega
        have hsmall1 : Ty.size tau1 < size := by omega
        have hn : n ≠ 0 := by
          intro hn
          subst n
          have hz : CheckedLocalSideBasisZero hb := by
            simpa only [CheckedLocalSideBasisDepth] using hside
          cases hz
        obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        obtain ⟨k0, k1, Lb, hb0, hbody, side0, sideBody,
          htPi, ⟨_sidePi⟩⟩ := hside.frame_parts
        obtain ⟨hi0, hi1⟩ := hisTy
        obtain ⟨tauV0, hdom⟩ :=
          ih (Ty.size tau0) hsmall0 Psi0 hrootStored Gamma Psi b0 hb0
            hfuture side0 hP hcov hstored (∅ : LCtx) hwf0 hi0
            (by rw [htof0])
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
          (EvalCtx.avoidB Psi ∪ Gamma.keys ∪ Lb ∪
            Basis.fv b0 ∪ Basis.fv b1 ∪ ValTy.fv tauV0)
        simp only [Finset.mem_union, not_or] at hx
        obtain ⟨⟨⟨⟨⟨hxPsi, hxGammaKeys⟩, hxLb⟩, hxb0⟩, hxb1⟩,
          hxtauV0⟩ := hx
        have hxGamma : x ∉ Gamma := by
          intro hm
          exact hxGammaKeys (Finmap.mem_keys.mpr hm)
        have hfresh : (x, b0) ∉ Psi :=
          (EvalCtx.avoidB_spec hxPsi).1 b0
        obtain ⟨hPx, hcovx, hstoredx⟩ :=
          V2.pcarrier_extend_transport (V2.transportN (Ty.size tau0))
            hP hcov hstored hb0 hi0 hdom.erase hfresh (by rw [htof0])
        have hwfx : V2.CtxWF' (∅ : LCtx)
            (Finmap.insert x (Basis.tof b0) Gamma) :=
          RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
            (b := b0) hwf0 Finmap.notMem_empty hxGamma hb0
        have hside1 :=
          (sideBody Psi hfuture x hxLb b0 (.var x tauV0) hb0 rfl).2
        have hsize1 : Ty.size (Basis.tof (Basis.openVar x b1)) <=
            Ty.size tau1 := by
          show Ty.size (Basis.tof (Basis.openRec 0 (.var x) b1)) <=
            Ty.size tau1
          rw [Basis.tof_openRec, htof1]
          exact le_of_eq (Ty.size_openVar 0 x tau1)
        obtain ⟨tauVOut, hout⟩ :=
          ih (Ty.size tau1) hsmall1
            (Psi.extend x b0 (.var x tauV0)) hstoredx
            (Finmap.insert x (Basis.tof b0) Gamma)
            (Psi.extend x b0 (.var x tauV0)) (Basis.openVar x b1)
            (hbody x hxLb) (CheckedStdFuture.refl _)
            hside1 hPx hcovx hstoredx (∅ : LCtx) hwfx
            (Basis.IsTyBasis.openRec (.var x) 0 hi1) hsize1
        have hlctauV0 : ValTy.lc tauV0 :=
          evalT_lc hdom.erase hP.1.toEvalCtxLc
        have hlctauVOut : ValTy.lc tauVOut :=
          evalT_lc hout.erase hPx.1.toEvalCtxLc
        have hout' : C.TyAt (Finmap.insert x tau0 Gamma)
            (Psi.extend x b0 (.var x tauV0))
            (Basis.openVar x b1) tauVOut := by
          rw [← htof0]
          exact hout
        obtain ⟨Lout, hcodOut⟩ :=
          checkedTyAt_arbitrary_cofinite_of_fresh hren hwf0
            (by
              obtain ⟨k, ⟨ht0⟩⟩ := hb0.tof_tvalid
              exact ⟨k, ⟨by simpa only [htof0] using ht0⟩⟩)
            htof0 hb0 hxGamma hout' hxPsi hxb0 hxtauV0 hxb1
            hlctauV0 hlctauVOut
        rw [← htof0] at hcodOut
        exact ⟨.piTy tauV0 (ValTy.closeRec 0 x tauVOut),
          .frame hb hdom Lout hcodOut⟩

/-- Exact checked realization at one local basis-depth certificate, uniformly
over roots.  This replaces the global fixed-depth supply in the exact half
of the mutual construction. -/
theorem checkedExactBasisTyProgressDepth_of_allCob_local
    (n : Nat)
    (hcob : CheckedCobToStdDepthAll n)
    (hren : CheckedRenameLaws) :
    forall (Psi0 : EvalCtx) (hrootStored : V2.StoredWF Psi0),
      CheckedExactBasisTyProgressDepth Psi0 n := by
  intro Psi0 hrootStored Gamma Psi b hb hfuture hside hP hcov hstored
    Delta hwf hisTy
  exact checkedExactLocalN_of_allCob n hcob hren
    (Ty.size (Basis.tof b)) Psi0 hrootStored Gamma Psi b hb hfuture
    hside hP hcov hstored Delta hwf hisTy le_rfl

end RawCertifiedDepthExactLocal
end GLang
