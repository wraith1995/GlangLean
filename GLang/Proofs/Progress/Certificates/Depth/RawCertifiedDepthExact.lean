import GLang.Proofs.Progress.Certificates.RawCertifiedSelectedProgressMaster
import GLang.Proofs.Progress.BasisDepthStep
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactBasisTyProgress

/-!
# Exact checked types at a finite side-basis depth

The history/depth index controls source-term-to-selected-basis calls.  A
dependent frame has a second, independent decrease: its domain and opened
codomain have smaller source type than the enclosing Pi type.  This module
keeps that existing strong induction and uses a purely syntactic depth
supply whenever the frame recursion changes the evaluator root.

No semantic payload is stored in a future world, and no axiom or admission
is introduced.
-/

namespace GLang
namespace RawCertifiedDepthExact

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedSelectedProgressMaster
open RawCertifiedCobDepthLayerSpike
open RawCertifiedPiBasisTransport
open RawCertifiedExactBasisTyProgress

/-- Syntactic side evidence can be reconstructed after an internal frame
extension.  The operational/WF hypotheses restrict the quantification to
the roots actually used by checked progress. -/
def CheckedBasisDepthSupply (n : Nat) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis},
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
    (hb : Basis.BasisValid Gamma b) ->
    CheckedLocalSideBasisDepth Psi n hb

/-- COB progress at depth `n`, uniformly at every possible current root.
This is what permits the type-size induction to enter an arbitrary frame
domain extension and then continue at that new root. -/
def CheckedCobToStdDepthAll (n : Nat) : Prop :=
  forall (Psi : EvalCtx), V2.StoredWF Psi ->
    RawCertifiedCobDepthLayerSpike.CheckedCobToStdDepth Psi n

private def CheckedExactDepthN (n depth : Nat) : Prop :=
  forall (Gamma : NLCtx) (Psi : EvalCtx) (b : Basis),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> forall (Delta : LCtx), V2.CtxWF' Delta Gamma ->
    Basis.BasisValid Gamma b -> Basis.IsTyBasis b ->
    Ty.size (Basis.tof b) <= n ->
    exists tauv, C.TyAt Gamma Psi b tauv

/-- Exact realization with the frame recursion justified by `Ty.size` and
all term/basis crossings justified by the fixed `depth` supply. -/
private theorem checkedExactDepthN_of_allCob
    (depth : Nat)
    (hcob : CheckedCobToStdDepthAll depth)
    (hsupply : CheckedBasisDepthSupply depth)
    (hren : CheckedRenameLaws) :
    forall n, CheckedExactDepthN n depth := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Gamma Psi b hP hcov hstored Delta hwf hb hisTy hsize
    have hwf0 := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
    cases htof : Basis.tof b with
    | space s =>
        have hspace : Basis.IsSpaceBasis b :=
          hisTy.toIsSpaceBasis (Basis.ne_frame_of_tof_space htof)
        have hside : CheckedLocalSideBasisDepth Psi depth hb :=
          hsupply hP hcov hstored hwf0 hb
        obtain ⟨env, hbb⟩ := hcob Psi hstored hb hside
          (CheckedStdFuture.refl Psi) hP hcov hwf0 hspace
        obtain ⟨sv, hsv⟩ := checkedCob_sourceSpace hbb
        exact ⟨.space sv, .space hspace.tof_eq hb hsv⟩
    | piTy tau0 tau1 =>
        obtain ⟨b0, b1, rfl, htof0, htof1⟩ := Basis.tof_piTy_inv htof
        rw [htof] at hsize
        simp only [Ty.size] at hsize
        have hsmall0 : Ty.size tau0 < n := by omega
        have hsmall1 : Ty.size tau1 < n := by omega
        obtain ⟨hb0, ⟨Lb, hb1⟩, k0, k1, ⟨hTpi⟩⟩ := hb.frame_inv
        rw [htof0, htof1] at hTpi
        cases hTpi with
        | piTy LT hT0 hT1 =>
        obtain ⟨hi0, hi1⟩ := hisTy
        obtain ⟨tauV0, hdom⟩ :=
          ih (Ty.size tau0) hsmall0 Gamma Psi b0 hP hcov hstored
            (∅ : LCtx) hwf0 hb0 hi0 (by rw [htof0])
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
          (EvalCtx.avoidB Psi ∪ Gamma.keys ∪ Lb ∪
            Basis.fv b0 ∪ Basis.fv b1 ∪ ValTy.fv tauV0)
        simp only [Finset.mem_union, not_or] at hx
        obtain ⟨⟨⟨⟨⟨hxPsi, hxGammaKeys⟩, hxLb⟩, hxb0⟩, hxb1⟩,
          hxtauV0⟩ := hx
        have hxGamma : x ∉ Gamma := by
          intro hm
          exact hxGammaKeys (Finmap.mem_keys.mpr hm)
        have hfresh : (x, b0) ∉ Psi := (EvalCtx.avoidB_spec hxPsi).1 b0
        obtain ⟨hPx, hcovx, hstoredx⟩ :=
          V2.pcarrier_extend_transport (V2.transportN (Ty.size tau0))
            hP hcov hstored hb0 hi0 hdom.erase hfresh (by rw [htof0])
        rw [htof0] at hcovx
        have hwfx : V2.CtxWF' (∅ : LCtx)
            (Finmap.insert x tau0 Gamma) := by
          have h := RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
            (b := b0) hwf0 Finmap.notMem_empty hxGamma hb0
          rwa [htof0] at h
        have hb1x : Basis.BasisValid (Finmap.insert x tau0 Gamma)
            (Basis.openVar x b1) := by
          have h := hb1 x hxLb
          rwa [htof0] at h
        have hsize1 : Ty.size (Basis.tof (Basis.openVar x b1)) <=
            Ty.size tau1 := by
          show Ty.size (Basis.tof (Basis.openRec 0 (.var x) b1)) <=
            Ty.size tau1
          rw [Basis.tof_openRec, htof1]
          exact le_of_eq (Ty.size_openVar 0 x tau1)
        obtain ⟨tauVOut, hout⟩ :=
          ih (Ty.size tau1) hsmall1 (Finmap.insert x tau0 Gamma)
            (Psi.extend x b0 (.var x tauV0)) (Basis.openVar x b1)
            hPx hcovx hstoredx (∅ : LCtx) hwfx hb1x
            (Basis.IsTyBasis.openRec (.var x) 0 hi1) hsize1
        have hlctauV0 : ValTy.lc tauV0 :=
          evalT_lc hdom.erase hP.1.toEvalCtxLc
        have hlctauVOut : ValTy.lc tauVOut :=
          evalT_lc hout.erase hPx.1.toEvalCtxLc
        obtain ⟨Lout, hcodOut⟩ :=
          checkedTyAt_arbitrary_cofinite_of_fresh hren hwf0
            ⟨k0, ⟨hT0⟩⟩ htof0 hb0 hxGamma hout hxPsi hxb0
            hxtauV0 hxb1 hlctauV0 hlctauVOut
        rw [← htof0] at hcodOut
        exact ⟨.piTy tauV0 (ValTy.closeRec 0 x tauVOut),
          .frame hb hdom Lout hcodOut⟩

/-- Uniform exact progress at depth `n`. -/
theorem checkedExactBasisTyProgressWFDepth_of_allCob
    (n : Nat)
    (hcob : CheckedCobToStdDepthAll n)
    (hsupply : CheckedBasisDepthSupply n)
    (hren : CheckedRenameLaws) :
    forall (Gamma : NLCtx) (Psi : EvalCtx) (b : Basis),
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.StoredWF Psi -> forall (Delta : LCtx), V2.CtxWF' Delta Gamma ->
      Basis.BasisValid Gamma b -> Basis.IsTyBasis b ->
      exists tauv, C.TyAt Gamma Psi b tauv := by
  intro Gamma Psi b hP hcov hstored Delta hwf hb hi
  exact checkedExactDepthN_of_allCob n hcob hsupply hren
    (Ty.size (Basis.tof b)) Gamma Psi b hP hcov hstored Delta hwf
    hb hi le_rfl

/-- Root/future adapter consumed by the selected variable master. -/
theorem checkedExactBasisTyProgressDepth_of_allCob
    (n : Nat)
    (hcob : CheckedCobToStdDepthAll n)
    (hsupply : CheckedBasisDepthSupply n)
    (hren : CheckedRenameLaws)
    (Psi0 : EvalCtx) : CheckedExactBasisTyProgressDepth Psi0 n := by
  intro Gamma Psi b hb _hfuture _hside hP hcov hstored Delta hwf hi
  exact checkedExactBasisTyProgressWFDepth_of_allCob n hcob hsupply hren
    Gamma Psi b hP hcov hstored Delta hwf hb hi

end RawCertifiedDepthExact
end GLang
