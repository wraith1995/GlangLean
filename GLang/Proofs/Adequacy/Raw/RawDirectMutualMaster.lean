import GLang.Proofs.Adequacy.Raw.RawApplicationOracleSpec
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacySimple
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyComposite
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyCob
import GLang.Proofs.Adequacy.Raw.RawSpaceFFSAdequacy
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobProducts
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobInverse
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobProjections
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobFFSInference
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyLlam
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyEmbed
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyPinv
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyGPinvT
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyGPinvD
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobImageSVDs
import GLang.Proofs.Adequacy.Raw.Terms.RawTermsRREFBoundary

/-!
# Direct five-way raw adequacy assembly

The strengthened semantics is mutually inductive across spaces, types,
exact-basis types, changes of basis, and terms.  This module specializes its
generated five-way recursor to the raw adequacy motives. Every constructor is
discharged by a current arm.  The proved `terms_rref` arm uses the narrow
coordinate-level numerical boundary `standardRREFLexInd`.
-/

namespace GLang

/-! ## Five-way assembly -/

/-- The term-rooted entry point of the direct mutual adequacy proof.

The generated recursor traverses all five strengthened judgments at once.
The four semantic back-edges from FFS spaces therefore receive the paired
term IH directly, while term constructors receive their exact-basis type,
space, and COB IHs directly. The RREF constructor uses the proved semantic
arm, whose only additional RREF-selection input is `standardRREFLexInd`, while
retaining its constructive inference proof. -/
theorem S.Term.rawDirectMutualMaster
    {orc : FFSOracleSem} (hspec : RawApplicationOracleSpec orc)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {e : GLang.Term}
    {b : Basis} {v : ValExpr} {tauV : ValTy}
    (h : S.Term Delta Gamma Psi e b v tauV) :
    RawTermDofFactsSubctx orc Delta Gamma Psi e b v tauV := by
  let hirr := hspec.toOracleSpec.fvIrrel
  refine h.rec
    (motive_1 := fun Gamma Psi s sv _ =>
      RawMSpaceSubctx orc Gamma Psi s sv)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun Gamma Psi b tauV _ =>
      RawMTyAtSubctx orc Gamma Psi b tauV)
    (motive_4 := fun Gamma Psi bSrc env bTgt _ =>
      RawCobFactsSubctx orc Gamma Psi bSrc env bTgt)
    (motive_5 := fun Delta Gamma Psi e b v tauV _ =>
      RawTermDofFactsSubctx orc Delta Gamma Psi e b v tauV)
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

  case spaceReal =>
    exact raw_arm_space_real
  case spaceEmpty =>
    exact raw_arm_space_empty
  case spaceDual =>
    intro Gamma Psi s sv hs h ih
    exact raw_arm_space_dual hs h ih
  case spaceKer =>
    intro Gamma Psi s0 s1 e b v svb hs hb hcompat hsvb he
      ihSpace ihTerm
    exact raw_arm_space_ker hspec.toOracleSpec
      hs hb hcompat hsvb he ihSpace ihTerm
  case spaceCoker =>
    intro Gamma Psi s0 s1 e b v svb hs hb hcompat hsvb he
      ihSpace ihTerm
    exact raw_arm_space_coker hspec.toOracleSpec
      hs hb hcompat hsvb he ihSpace ihTerm
  case spaceImg =>
    intro Gamma Psi s0 s1 e b v svb hs hb hcompat hsvb he
      ihSpace ihTerm
    exact raw_arm_space_img hspec.toOracleSpec
      hs hb hcompat hsvb he ihSpace ihTerm
  case spaceCoimg =>
    intro Gamma Psi s0 s1 e b v svb hs hb hcompat hsvb he
      ihSpace ihTerm
    exact raw_arm_space_coimg hspec.toOracleSpec
      hs hb hcompat hsvb he ihSpace ihTerm
  case spaceTprod =>
    intro Gamma Psi s0 s1 sv0 sv1 hs h0 h1 ih0 ih1
    exact raw_arm_space_tprod hs h0 h1 ih0 ih1
  case spaceDsum =>
    intro Gamma Psi s0 s1 sv0 sv1 hs h0 h1 ih0 ih1
    exact raw_arm_space_dsum hs h0 h1 ih0 ih1
  case tySpace =>
    intros
    trivial
  case tyPi =>
    intros
    trivial
  case tyAtSpace =>
    intro Gamma Psi b sv htof hbv hs ihSpace
    exact raw_arm_tyAt_space htof hbv hs ihSpace
  case tyAtFrame =>
    intro Gamma Psi b0 b1 tauV0 tauV1 hbv hdom L hcod ihdom ihcod
    have hisTy := hbv.isTyBasis
    intro Psi' hsub
    exact raw_arm_tyAt_frame hspec hbv hdom L hcod hisTy @ihdom @ihcod hsub
  case cobInverse =>
    intro Gamma Psi b0 b1 env hb0 hb1 hcob ih
    exact raw_arm_cob_inverse_facts orc
      hspec.toOracleSpec hb0 hb1 hcob ih
  case cobTrans =>
    intro Gamma Psi b0 b1 b2 env0 env1 sv hb0 hb2 h0 h1 hsv
      ih0 ih1 ihSpace
    exact raw_arm_cob_facts_trans hb0 hb2 h0 h1 hsv ih0 ih1 ihSpace
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
      hsvb he ihSpace ihTerm
    exact RawCobImageSVDs.raw_arm_cob_image_svds_facts
      hspec.toOracleSpec hbS hbT hs0 hs1 hb0 hb1
        hsvb he ihSpace ihTerm
  case cobProjKerCoker =>
    intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env2 env3
      sv0 sv1 sv sv' sv0' hbS hbT hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv0' hcob hembd hproj
      ihsv0 ihsv1 ihsv ihsv' ihsv0' ihcob ihembd ihproj
    exact raw_arm_cob_facts_proj_ker_coker hbS hbT hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv0' hcob hembd hproj
      ihsv0 ihsv1 ihsv ihsv' ihsv0' ihcob ihembd ihproj
  case cobProjImgCoimg =>
    intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env2 env3
      sv0 sv1 sv sv' sv1' hbS hbT hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv1' hcob hembd hproj
      ihsv0 ihsv1 ihsv ihsv' ihsv1' ihcob ihembd ihproj
    exact raw_arm_cob_facts_proj_img_coimg hbS hbT hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv1' hcob hembd hproj
      ihsv0 ihsv1 ihsv ihsv' ihsv1' ihcob ihembd ihproj
  case cobTermsRref =>
    intro Gamma Psi b b' e es env0 env1 sv tauV hbS hbT hbb hch hsv
      ihCob ihTerm ihSpace
    exact ⟨raw_arm_cob_terms_rref_boundary
        hbS hbT hbb hch hsv ihCob ihTerm ihSpace,
      raw_arm_cob_infer_terms_rref hbS ihSpace⟩
  case cobRefl =>
    intro Gamma Psi b sv hb htof hsv ihSpace
    exact raw_arm_cob_facts_refl hb htof hsv ihSpace
  case cobProjKerCokerCod =>
    intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env3 sv0 sv sv'
      hbS hbT hs hsofb0 hsofb1 hsofb1' hsv0 hsv hsv' hembd hproj
      ihsv0 ihsv ihsv' ihembd ihproj
    exact raw_arm_cob_facts_proj_ker_coker_cod hbS hbT hs hsofb0
      hsofb1 hsofb1' hsv0 hsv hsv' hembd hproj ihsv0 ihsv ihsv'
      ihembd ihproj
  case cobProjImgCoimgDom =>
    intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env3 sv1 sv sv'
      hbS hbT hs hsofb0 hsofb1 hsofb0' hsv1 hsv hsv' hembd hproj
      ihsv1 ihsv ihsv' ihembd ihproj
    exact raw_arm_cob_facts_proj_img_coimg_dom hbS hbT hs hsofb0
      hsofb1 hsofb0' hsv1 hsv hsv' hembd hproj ihsv1 ihsv ihsv'
      ihembd ihproj
  case termVarLin =>
    intro Gamma Psi x b v s tauV hlookup htof hbv hTy ihTy
    exact ⟨arm_var_lin hirr hlookup htof hbv hTy ihTy,
      arm_var_lin_dof hirr hlookup htof hbv hTy ihTy⟩
  case termVarNlin =>
    intro Gamma Psi x b v tauV hlookup hGamma hbv hTy ihTy
    exact ⟨arm_var_nlin hirr hlookup hGamma hbv hTy ihTy,
      arm_var_nlin_dof hirr hlookup hGamma hbv hTy ihTy⟩
  case termPromote =>
    intro Delta Gamma Gamma'' Psi e b v tauV lin hdDelta hdGamma hfr hle ht hbv hTy he
      ihTy ihE
    exact ⟨arm_promote hdDelta hdGamma hfr hle ht hbv hTy he ihE.trace,
      arm_promote_dof lin hdGamma hle ihE.dof⟩
  case termCob =>
    intro Delta Gamma Psi e b0 b1 v env0 sv tauV htof0 htof1 ht hbv
      hTy he hbb hes ihTy ihE ihCob ihSpace
    exact arm_cob_facts htof0 htof1 ht hbv hTy he hbb hes
      ihTy ihE ihCob ihSpace
  case termReshape =>
    intro Delta Gamma Psi e b v tauV tauV' ht hbv hTy he ihTy ihE
    exact ⟨arm_reshape ht hbv hTy he ihTy ihE.trace, arm_reshape_dof⟩
  case termScale =>
    intro Delta0 Delta1 Gamma Psi e0 e1 b v0 v1 sv hdisj htof ht hbv
      hTy he0 he1 ihTy ih0 ih1
    exact ⟨arm_scale hdisj htof ht hbv hTy he0 he1 ihTy ih0.trace ih1,
      arm_scale_dof ih1.dof⟩
  case termAdd =>
    intro Delta Gamma Psi e0 e1 b v0 v1 sv sv0 sv1 htof ht hbv hTy
      he0 he1 ihTy ih0 ih1
    exact ⟨arm_add htof ht hbv hTy he0 he1 ihTy ih0.trace ih1.trace,
      arm_add_dof⟩
  case termDsum =>
    intro Delta Gamma Psi e0 e1 b0 b1 v0 v1 sv0 sv1 htof0 htof1 ht
      hbv hTy he0 he1 ihTy ih0 ih1
    exact ⟨arm_dsumE htof0 htof1 ht hbv hTy he0 he1 ihTy ih0 ih1,
      arm_dsumE_dof ih0.dof ih1.dof⟩
  case termTprod =>
    intro Delta0 Delta1 Gamma Psi e0 e1 b0 b1 v0 v1 sv0 sv1 hdisj
      htof0 htof1 ht hbv hTy he0 he1 ihTy ih0 ih1
    exact ⟨arm_tprodE hdisj htof0 htof1 ht hbv hTy he0 he1
        ihTy ih0 ih1,
      arm_tprodE_dof ih0.dof ih1.dof⟩
  case termPinvTStd =>
    intro Gamma Psi b0 b1 e v sv0 sv1 hb0 hb1 ht hbv hTy he ihTy ihE
    exact arm_pinvT_std_facts hb0 hb1 ht hbv hTy he ihTy ihE
  case termPinvTGpinv =>
    intro Gamma Psi b0 b1 e v env0 env1 sv0 sv1 ht hbv hTy he hi0 hi1
      ihTy ihE ihI0 ihI1
    exact arm_pinvT_gpinv_facts ht hbv hTy he hi0 hi1
      ihTy ihE ihI0 ihI1
  case termPinvDStd =>
    intro Gamma Psi b0 b1 e v sv1 hsofb0 hb0 hb1 ht hbv hTy he ihTy ihE
    exact arm_pinvD_std_facts hsofb0 hb0 hb1 ht hbv hTy he ihTy ihE
  case termPinvDGpinv =>
    intro Gamma Psi b0 b1 e v env0 env1 sv1 hsofb0 hb0 ht hbv hTy he hi0 hi1
      ihTy ihE ihI0 ihI1
    exact arm_pinvD_gpinv_of_std_codomain_facts hsofb0 hb0 ht hbv hTy he hi0 hi1
      ihTy ihE ihI0 ihI1
  case termInnerStd =>
    intro Gamma Psi b0 s sv hb0 hsof ht hbv hTy hsv ihTy ihSpace
    exact ⟨arm_inner_std hb0 hsof ht hbv hTy hsv ihTy ihSpace,
      arm_inner_std_dof⟩
  case termEmbedKer =>
    intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
      hTy hi0 hi1 he ihTy ihI0 ihI1 ihE
    exact RawTermEmbed.raw_arm_term_embed_kernel_facts
      hspec.toOracleSpec hs0 hs1 ht hbv hTy hi0 hi1 he
        ihTy ihI0 ihI1 ihE
  case termEmbedCoker =>
    intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
      hTy hi0 hi1 he ihTy ihI0 ihI1 ihE
    exact RawTermEmbed.raw_arm_term_embed_cokernel_facts
      hspec.toOracleSpec hs0 hs1 ht hbv hTy hi0 hi1 he
        ihTy ihI0 ihI1 ihE
  case termEmbedImg =>
    intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
      hTy hi0 hi1 he ihTy ihI0 ihI1 ihE
    exact RawTermEmbed.raw_arm_term_embed_image_facts
      hspec.toOracleSpec hs0 hs1 ht hbv hTy hi0 hi1 he
        ihTy ihI0 ihI1 ihE
  case termEmbedCoimg =>
    intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
      hTy hi0 hi1 he ihTy ihI0 ihI1 ihE
    exact RawTermEmbed.raw_arm_term_embed_coimage_facts
      hspec.toOracleSpec hs0 hs1 ht hbv hTy hi0 hi1 he
        ihTy ihI0 ihI1 ihE
  case termAppL =>
    intro Delta0 Delta1 Gamma Psi b0 b1 n0 n1 env0 env1
      sv svOut svMat0 svMat1 svArg
      hdisj htof1 ht hbv hsv hTy h0 h1 ihSpace ihTy ih0 ih1
    exact ⟨arm_appL_lin hdisj htof1 ht hbv hsv hTy h0 h1
        ihSpace ihTy ih0 ih1,
      arm_appL_lin_dof⟩
  case termAppI =>
    intro Delta0 Delta1 Gamma Psi b0 n0 n1 env0 env1 sv svFun svArg
      hdisj ht hsv hTy h0 h1 ihSpace ihTy ih0 ih1
    exact ⟨arm_appI_lin hdisj ht hsv hTy h0 h1
        ihSpace ihTy ih0.trace ih1,
      arm_appI_lin_dof⟩
  case termNllam =>
    intro Gamma Psi b0 b1 tau0 tau1 e tauV0 tauV1 env hb0 hb1 ht hbv
      hTy hdom L he hcod ihTy ihDom ihBody ihCod
    exact ⟨arm_nllam hspec hb0 hb1 ht hbv hTy hdom L he hcod
        ihTy ihDom (fun y hy => (ihBody y hy).trace) ihCod,
      arm_nllam_dof⟩
  case termAppNVal =>
    intro Gamma Psi b0 b1 n0 n1 env0 env1
      tauFun0 tauFun1 tauArg tauOut ht hbv
      hTy h0 h1 ihTy ih0 ih1
    exact ⟨arm_appN_val hspec.codomainSubstitution hspec.toOracleSpec.fvIrrel ht hbv hTy h0 h1 ihTy ih0.trace ih1.trace ih1.dof,
      arm_appN_val_dof⟩
  case termFrameReanchor =>
    intro Gamma Psi b0 b0' b1 n0 env0 env1 tauV0 tauV0' tauV1 tauV1'
      htof ht hbv hTy h0 hfn hdom L hx hcod
      ihTy ih0 ihFn ihDom ihX ihCod
    exact ⟨arm_frame_reanchor hspec htof ht hbv hTy h0 hfn hdom L hx hcod
        ihTy ih0 ihFn.trace ihDom (fun y hy => (ihX y hy).trace) ihCod,
      arm_frame_reanchor_dof⟩
  case termFrameEta =>
    intro Gamma Psi b0 b1 n0 tauV0 tauV1 env ht hbv hTy h0 L he h1
      ihTy ih0 ihE ih1
    exact ⟨arm_frame_eta hspec ht hbv hTy h0 L he h1 ihTy ih0
        (fun y hy => (ihE y hy).trace) ih1,
      arm_frame_eta_dof⟩
  case termLlam =>
    intro Delta Gamma Psi b' b e sv' sv env htof' ht hbv hTy
      hsv' hsv L hfam ihTy ihsv' ihsv ihFam
    exact ⟨arm_llam_assemble hspec htof' ht hbv hTy hsv' hsv L hfam
        ihTy ihsv' ihsv ihFam,
      arm_llam_assemble_dof⟩
  case termLlamReal =>
    intro Delta Gamma Psi b' e sv' env htof' ht hbv hTy hsv' L hfam
      ihTy ihsv' ihFam
    exact ⟨arm_llam_assemble_real hspec htof' ht hbv hTy hsv' L hfam
        ihTy ihsv' ihFam,
      arm_llam_assemble_real_dof⟩
  case termZero =>
    intro Delta Gamma Psi b sv htof ht hbv hTy hsv ihTy ihSpace
    exact ⟨arm_zero htof ht hbv hTy hsv ihTy, arm_zero_dof⟩
  case termRlit =>
    intro Gamma Psi r ht hTy ihTy
    exact ⟨arm_rlit r ht hTy ihTy, arm_rlit_dof⟩
end GLang
