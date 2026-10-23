import GLang.Proofs.Adequacy.Raw.RawDirectMutualMaster
import GLang.Proofs.Adequacy.Raw.RawSpaceTypeMaster

/-!
# Arbitrary-root raw COB adequacy assembly

`S.Term.rawDirectMutualMaster` proves every COB constructor encountered below
a term root.  This module exports the same completed COB motive for an
arbitrary `S.Cob` root.  Recursive COB premises use the generated mutual
induction hypotheses; space and term premises are discharged by the already
assembled term-rooted providers.  Thus this assembly introduces no new
semantic premise or proof boundary.
-/

namespace GLang

/-- Full raw agreement and inferred-matrix facts for any strengthened
change-of-basis derivation, independent of whether it occurs below a term. -/
theorem S.Cob.rawDirectMutualMaster
    {orc : FFSOracleSem} (hspec : RawApplicationOracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {bSrc bTgt : Basis} {env : ValExpr}
    (h : S.Cob Gamma Psi bSrc env bTgt) :
    RawCobFactsSubctx orc Gamma Psi bSrc env bTgt := by
  let hterm : RawTermFactsProvider orc := by
    intro Gamma Psi e b v sv he
    exact he.rawDirectMutualMaster hspec
  let hspace : RawSpaceProvider orc :=
    S.Space.rawMasterOfTerm
      hspec.toOracleSpec hterm
  refine h.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun Gamma Psi bSrc env bTgt _ =>
      RawCobFactsSubctx orc Gamma Psi bSrc env bTgt)
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
    ?termZero ?termRlit

  case cobInverse =>
    intro Gamma Psi b0 b1 env hb0 hb1 hcob ih
    exact raw_arm_cob_inverse_facts orc
      hspec.toOracleSpec hb0 hb1 hcob ih
  case cobTrans =>
    intro Gamma Psi b0 b1 b2 env0 env1 sv hb0 hb2 h0 h1 hsv
      ih0 ih1 _ihSpace
    exact raw_arm_cob_facts_trans hb0 hb2 h0 h1 hsv ih0 ih1
      (hspace hsv)
  case cobTprod =>
    intro Gamma Psi b0 b1 b0' b1' env0 env1 hbS hbT h0 h1 ih0 ih1
    exact raw_arm_cob_facts_tprod hbS hbT h0 h1 ih0 ih1
  case cobDsum =>
    intro Gamma Psi b0 b1 b0' b1' env0 env1 hbS hbT h0 h1 ih0 ih1
    exact raw_arm_cob_facts_dsum hbS hbT h0 h1 ih0 ih1
  case cobDualStd =>
    intro Gamma Psi b0 env htof hbS hbT hcob ih
    exact raw_arm_cob_dual_std_facts orc
      hspec.toOracleSpec htof hbS hbT hcob ih
  case cobImage =>
    intro Gamma Psi b0 b0' env hbS hbT hcoker hcob ih
    exact raw_arm_cob_facts_image hbS hbT hcoker hcob ih
  case cobImageSvds =>
    intro Gamma Psi b0 b1 e env s0 s1 svb hbS hbT hs0 hs1 hb0 hb1
      hsvb he _ihSpace _ihTerm
    exact RawCobImageSVDs.raw_arm_cob_image_svds_facts
      hspec.toOracleSpec hbS hbT hs0 hs1 hb0 hb1
        hsvb he (hspace hsvb) (hterm he)
  case cobProjKerCoker =>
    intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env2 env3
      sv0 sv1 sv sv' sv0' hbS hbT hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv0' hcob hembd hproj
      _ihsv0 _ihsv1 _ihsv _ihsv' _ihsv0' ihcob _ihembd _ihproj
    exact raw_arm_cob_facts_proj_ker_coker hbS hbT hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv0' hcob hembd hproj
      (hspace hsv0) (hspace hsv1) (hspace hsv) (hspace hsv')
      (hspace hsv0') ihcob (hterm hembd) (hterm hproj)
  case cobProjImgCoimg =>
    intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env2 env3
      sv0 sv1 sv sv' sv1' hbS hbT hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv1' hcob hembd hproj
      _ihsv0 _ihsv1 _ihsv _ihsv' _ihsv1' ihcob _ihembd _ihproj
    exact raw_arm_cob_facts_proj_img_coimg hbS hbT hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv1' hcob hembd hproj
      (hspace hsv0) (hspace hsv1) (hspace hsv) (hspace hsv')
      (hspace hsv1') ihcob (hterm hembd) (hterm hproj)
  case cobTermsRref =>
    intro Gamma Psi b b' e es env0 env1 sv tauV hbS hbT hbb hch hsv
      ihCob _ihTerm _ihSpace
    exact ⟨raw_arm_cob_terms_rref_boundary hbS hbT hbb hch hsv ihCob
        (hch.rawDirectMutualMaster hspec) (hspace hsv),
      raw_arm_cob_infer_terms_rref hbS (hspace hsv)⟩
  case cobRefl =>
    intro Gamma Psi b sv hb htof hsv _ihSpace
    exact raw_arm_cob_facts_refl hb htof hsv (hspace hsv)
  case cobProjKerCokerCod =>
    intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env3 sv0 sv sv'
      hbS hbT hs hsofb0 hsofb1 hsofb1' hsv0 hsv hsv' hembd hproj
      _ihsv0 _ihsv _ihsv' _ihembd _ihproj
    exact raw_arm_cob_facts_proj_ker_coker_cod hbS hbT hs hsofb0
      hsofb1 hsofb1' hsv0 hsv hsv' hembd hproj (hspace hsv0)
      (hspace hsv) (hspace hsv') (hterm hembd) (hterm hproj)
  case cobProjImgCoimgDom =>
    intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env3 sv1 sv sv'
      hbS hbT hs hsofb0 hsofb1 hsofb0' hsv1 hsv hsv' hembd hproj
      _ihsv1 _ihsv _ihsv' _ihembd _ihproj
    exact raw_arm_cob_facts_proj_img_coimg_dom hbS hbT hs hsofb0
      hsofb1 hsofb0' hsv1 hsv hsv' hembd hproj (hspace hsv1)
      (hspace hsv) (hspace hsv') (hterm hembd) (hterm hproj)
  all_goals intros; trivial

end GLang
