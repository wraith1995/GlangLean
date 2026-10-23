import GLang.Proofs.Progress.Certificates.Context.RawCertifiedHereditaryStore
import GLang.Proofs.Progress.Certificates.RawCertifiedPiBasisTransport
import GLang.Proofs.Progress.ContextExtension

/-!
# Exact checked type progress at an arbitrary well-shaped basis

A checked change of basis contains enough checked space evidence to recover a
source-space realization.  For a frame, exact type progress recurses on the
strictly smaller domain and codomain types and packages one fresh codomain
realization cofinally using `CheckedRenameLaws`.

This discharges `CheckedExactBasisTyProgress` from checked COB progress and
the already-reviewed renaming interface.  The explicit local `CtxWF'` premise
is essential only in the dependent frame case; callers already carry it.
-/

namespace GLang
namespace RawCertifiedExactBasisTyProgress

open Basis (BasisValid)
open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedPiBasisTransport

private theorem ctxWF_dropLin
    (h : V2.CtxWF' Delta Gamma) : V2.CtxWF' (∅ : LCtx) Gamma where
  disjoint := fun _ hm => absurd hm Finmap.notMem_empty
  lin_fv := fun _ _ hm => absurd
    (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
  nl_fv := h.nl_fv
  lin_valid := fun _ _ hm => absurd
    (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
  nl_valid := h.nl_valid

private theorem sValid_img_of_coker
    (h : Nonempty (SValid Gamma (.coker s0 s1 e))) :
    Nonempty (SValid Gamma (.img s0 s1 e)) := by
  obtain ⟨h⟩ := h
  cases h with
  | coker hs0 hs1 he => exact ⟨.img hs0 hs1 he⟩

/-- A checked cokernel realization can be rebuilt as the corresponding image
realization from the same checked parent and witness. -/
private theorem checkedSpace_img_of_coker
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
    {sv : ValSpace}
    (h : C.Space Gamma Psi (.coker s0 s1 e) sv) :
    exists svi, C.Space Gamma Psi (.img s0 s1 e) svi := by
  refine C.Space.rec
    (motive_1 := fun Gamma Psi s _ _ =>
      forall s0 s1 e, s = .coker s0 s1 e ->
        exists svi, C.Space Gamma Psi (.img s0 s1 e) svi)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
    ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
    ?tySpace ?tyPi
    ?tyAtSpace ?tyAtFrame
    ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
    ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
    ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
    ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
    ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
    ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
    ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
    ?termAppL ?termAppI ?termNllam ?termAppNVal
    ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
    ?termZero ?termRlit h s0 s1 e rfl
  case spaceCoker =>
    intro Gamma Psi a0 a1 t b leev svb hs hb hcompat hsvb he _ _
      s0 s1 e heq
    injection heq with h0 h1 het
    subst a0; subst a1; subst t
    exact ⟨_, .img (sValid_img_of_coker hs) hb hcompat hsvb he⟩
  case spaceReal => intros; simp_all
  case spaceEmpty => intros; simp_all
  case spaceDual => intros; simp_all
  case spaceKer => intros; simp_all
  case spaceImg => intros; simp_all
  case spaceCoimg => intros; simp_all
  case spaceTprod => intros; simp_all
  case spaceDsum => intros; simp_all
  all_goals intros; trivial

private theorem checkedCob_sof_eq
    (h : C.Cob Gamma Psi b0 env b1) : Basis.sof b0 = Basis.sof b1 :=
  S.Cob.sof_eq h.toS

/-- Every checked conversion carries enough recursive checked evidence to
realize its source space. -/
theorem checkedCob_sourceSpace
    (h : C.Cob Gamma Psi b0 env b1) :
    exists sv, C.Space Gamma Psi (Basis.sof b0) sv := by
  refine C.Cob.rec
    (motive_1 := fun Gamma Psi s sv _ => C.Space Gamma Psi s sv)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun Gamma Psi b0 _ _ _ =>
      exists sv, C.Space Gamma Psi (Basis.sof b0) sv)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
    ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
    ?tySpace ?tyPi
    ?tyAtSpace ?tyAtFrame
    ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
    ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
    ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
    ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
    ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
    ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
    ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
    ?termAppL ?termAppI ?termNllam ?termAppNVal
    ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
    ?termZero ?termRlit h
  case cobInverse =>
    intro _ _ _ _ _ _ _ h ih
    obtain ⟨sv, hs⟩ := ih
    exact ⟨sv, by rwa [checkedCob_sof_eq h] at hs⟩
  case cobTrans =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ hsv _ _ _
    exact ⟨_, hsv⟩
  case cobTprod =>
    intro _ _ _ _ _ _ _ _ hbS _ _ _ ih0 ih1
    obtain ⟨sv0, hs0⟩ := ih0
    obtain ⟨sv1, hs1⟩ := ih1
    exact ⟨_, .tprod hbS.sof_valid hs0 hs1⟩
  case cobDsum =>
    intro _ _ _ _ _ _ _ _ hbS _ _ _ ih0 ih1
    obtain ⟨sv0, hs0⟩ := ih0
    obtain ⟨sv1, hs1⟩ := ih1
    exact ⟨_, .dsum hbS.sof_valid hs0 hs1⟩
  case cobDualStd =>
    intro _ _ _ _ _ hbS _ _ ih
    obtain ⟨sv, hs⟩ := ih
    exact ⟨sv, .dual hbS.sof_valid hs⟩
  case cobImage =>
    intro _ _ _ _ _ _ _ hcoker _ ih
    obtain ⟨s0, s1, e, heq⟩ := hcoker
    obtain ⟨sv, hs⟩ := ih
    rw [heq] at hs
    obtain ⟨svi, hi⟩ := checkedSpace_img_of_coker hs
    exact ⟨svi, by simp only [Basis.sof, heq]; exact hi⟩
  case cobImageSvds =>
    intro Gamma Psi b0 b1 e env s0 s1 svb hbS _ hs0 hs1 _ _
      hsvb he _ _
    have hi : C.Space Gamma Psi (.img s0 s1 e)
        (.ffs .image svb (ValExpr.reshapBase env svb)) :=
      .img hbS.sof_valid (by simp only [Basis.sof, hs0, hs1])
        ⟨b0, b1, rfl⟩ hsvb he
    exact ⟨_, by simpa only [Basis.sof] using hi⟩
  case cobProjKerCoker =>
    intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env2 env3 sv0 sv1 sv sv'
      sv0' hbS hbT hs hsof0 hsof1 hsv0 hsv1 hsv hsv' hsv0' hcob hembd
      hproj ihsv0 ihsv1 ihsv ihsv' ihsv0' ihc ihE ihP
    exact ⟨_, by simpa only [Basis.sof] using hsv⟩
  case cobProjImgCoimg =>
    intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env2 env3 sv0 sv1 sv sv'
      sv1' hbS hbT hs hsof0 hsof1 hsv0 hsv1 hsv hsv' hsv1' hcob hembd
      hproj ihsv0 ihsv1 ihsv ihsv' ihsv1' ihc ihE ihP
    exact ⟨_, by simpa only [Basis.sof] using hsv⟩
  case cobTermsRref =>
    intro Gamma Psi b b' e es env0 env1 sv tv hbS hbT hbb hch hsv
      ihb ihch ihsv
    exact ⟨_, hsv⟩
  case cobRefl =>
    intro Gamma Psi b sv hb htof hsv ihsv
    exact ⟨_, hsv⟩
  case cobProjKerCokerCod =>
    intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env3 sv0 sv sv' hbS hbT hs
      hsof0 hsof1 hsof1' hsv0 hsv hsv' hembd hproj ihsv0 ihsv ihsv' ihE ihP
    exact ⟨_, by simpa only [Basis.sof] using hsv⟩
  case cobProjImgCoimgDom =>
    intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env3 sv1 sv sv' hbS hbT hs
      hsof0 hsof1 hsof0' hsv1 hsv hsv' hembd hproj ihsv1 ihsv ihsv' ihE ihP
    exact ⟨_, by simpa only [Basis.sof] using hsv⟩
  all_goals intros; first | assumption | (constructor <;> assumption) | trivial

private def CheckedExactBasisTyProgressN (n : Nat) : Prop :=
  forall (Gamma : NLCtx) (Psi : EvalCtx) (b : Basis),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> forall (Delta : LCtx), V2.CtxWF' Delta Gamma ->
    Basis.BasisValid Gamma b -> Basis.IsTyBasis b ->
    Ty.size (Basis.tof b) <= n ->
    exists tauv, C.TyAt Gamma Psi b tauv

/-- Strong-induction implementation.  The frame case recurses at the domain,
extends the carrier by that checked result, recurses at one opened codomain,
then closes the result with the reviewed arbitrary-key rename law. -/
private theorem checkedExactBasisTyProgressN_of_cob
    (hcob : CheckedCobToStd)
    (hren : CheckedRenameLaws) :
    forall n, CheckedExactBasisTyProgressN n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Gamma Psi b hP hcov hstored Delta hwf hb hisTy hsize
    have hwf0 := ctxWF_dropLin hwf
    cases htof : Basis.tof b with
    | space s =>
        have hspace : Basis.IsSpaceBasis b :=
          hisTy.toIsSpaceBasis (Basis.ne_frame_of_tof_space htof)
        obtain ⟨env, hbb⟩ := hcob Gamma Psi b hP hcov hstored hb hspace
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

/-- Checked COB progress plus the reviewed checked rename law constructively
discharge the exact-basis type-progress input of the local master. -/
theorem checkedExactBasisTyProgress_of_cob
    (hcob : CheckedCobToStd)
    (hren : CheckedRenameLaws) : CheckedExactBasisTyProgress := by
  intro Gamma Psi b hP hcov hstored Delta hwf hb hi
  exact checkedExactBasisTyProgressN_of_cob hcob hren
    (Ty.size (Basis.tof b)) Gamma Psi b hP hcov hstored Delta hwf hb hi le_rfl

end RawCertifiedExactBasisTyProgress
end GLang
