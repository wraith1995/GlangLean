import GLang.Proofs.Adequacy.Raw.RawSpaceTypeMaster
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobFFSInference

/-!
# Provider-parameterized raw COB inference recursion

This is the complete syntactic-inference component for strengthened
change-of-basis derivations.  It deliberately proves only
`RawCobInferSubctx`; semantic `CobAgree` remains an independent component.
The two non-COB back-edges are explicit providers for strengthened spaces and
the closed, space-valued witness terms used by `image_svds`.
-/

namespace GLang

/-- The inferred matrix-factor dimensions for every strengthened COB
derivation.  The target basis remains in the derivation index even though the
inference conclusion measures both factors against the source basis. -/
def RawCobInferProvider (orc : FFSOracleSem) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {bSrc bTgt : Basis}
    {env : ValExpr},
    S.Cob Gamma Psi bSrc env bTgt ->
      RawCobInferSubctx orc Gamma Psi env bSrc

/-- Genuine five-way-recursion specialization closing all fourteen `S.Cob`
inference constructors. -/
theorem S.Cob.rawInferMaster
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    (hspace : RawSpaceProvider orc)
    (hterm : RawTermFactsProvider orc) :
    RawCobInferProvider orc := by
  intro Gamma Psi bSrc bTgt env h
  refine h.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun Gamma Psi bSrc env _ _ =>
      RawCobInferSubctx orc Gamma Psi env bSrc)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    -- `S.Space` (9)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    -- `S.Ty` (2)
    ?_ ?_
    -- `S.TyAt` (2)
    ?_ ?_
    -- `S.Cob` (13)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    -- `S.Term` (28)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  rotate_left 13
  · intro Gamma Psi b0 b1 leev hb0 hb1 hcob ih
    exact raw_arm_cob_infer_inverse hb0 hb1 hcob ih
  · intro Gamma Psi b0 b1 b2 env0 env1 sv hb0 _hb2 h0 h1 hsv
      _ih0 ih1 _ihSpace
    exact raw_arm_cob_infer_trans hb0 h0 h1 hsv (hspace hsv) ih1
  · intro Gamma Psi b0 b1 b0' b1' env0 env1 _hbSrc _hbTgt h0 h1
      ih0 ih1
    exact raw_arm_cob_infer_tprod (b0 := b0) (b1 := b1) ih0 ih1
  · intro Gamma Psi b0 b1 b0' b1' env0 env1 _hbSrc _hbTgt h0 h1
      ih0 ih1
    exact raw_arm_cob_infer_dsum (b0 := b0) (b1 := b1) ih0 ih1
  · intro Gamma Psi b0 leev _htof _hbSrc _hbTgt hcob ih
    exact raw_arm_cob_infer_dual_std ih
  · intro Gamma Psi b0 b0' leev hbSrc _hbTgt hcoker hcob ih
    exact raw_arm_cob_infer_image hbSrc hcoker ih
  · intro Gamma Psi b0 b1 e leev s0 s1 svb hbSrc hbTgt hs0 hs1
      hb0 hb1 hsvb he _ihSpace _ihTerm
    exact raw_arm_cob_infer_image_svds hspec hbSrc hbTgt hs0 hs1
      hb0 hb1 hsvb he (hspace hsvb) (hterm he)
  · intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env2 env3
      sv0 sv1 sv sv' sv0' hbSrc _hbTgt _hs _hsofb0 _hsofb1
      _hsv0 _hsv1 hsv hsv' _hsv0' _hcob _hembd _hproj
      _ihSpace0 _ihSpace1 _ihSpace _ihSpace' _ihSpace0' _ihCob
      _ihEmbd _ihProj
    exact raw_arm_cob_infer_proj_ker_coker hbSrc
      (hspace hsv) (hspace hsv')
  · intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env2 env3
      sv0 sv1 sv sv' sv1' hbSrc _hbTgt _hs _hsofb0 _hsofb1
      _hsv0 _hsv1 hsv hsv' _hsv1' _hcob _hembd _hproj
      _ihSpace0 _ihSpace1 _ihSpace _ihSpace' _ihSpace1' _ihCob
      _ihEmbd _ihProj
    exact raw_arm_cob_infer_proj_img_coimg hbSrc
      (hspace hsv) (hspace hsv')
  · intro Gamma Psi b b' e es env0 env1 sv tauV hbSrc _hbTgt
      _hbb _hchain hsv _ihCob _ihTerm _ihSpace
    exact raw_arm_cob_infer_terms_rref hbSrc (hspace hsv)
  · intro Gamma Psi b sv hb htof hsv _ihSpace
    exact raw_arm_cob_infer_refl hb htof (hspace hsv)
  · intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env3 sv0 sv sv'
      hbSrc _hbTgt _hs _hsofb0 _hsofb1 _hsofb1' _hsv0 hsv hsv'
      _hembd _hproj _ihSpace0 _ihSpace _ihSpace' _ihEmbd _ihProj
    exact raw_arm_cob_infer_proj_ker_coker_cod hbSrc
      (hspace hsv) (hspace hsv')
  · intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env3 sv1 sv sv'
      hbSrc _hbTgt _hs _hsofb0 _hsofb1 _hsofb0' _hsv1 hsv hsv'
      _hembd _hproj _ihSpace1 _ihSpace _ihSpace' _ihEmbd _ihProj
    exact raw_arm_cob_infer_proj_img_coimg_dom hbSrc
      (hspace hsv) (hspace hsv')
  all_goals (intros; trivial)

end GLang
