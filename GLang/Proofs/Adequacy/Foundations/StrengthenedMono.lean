import GLang.Proofs.Adequacy.Foundations.EvalCtxSubctx
import GLang.Proofs.Adequacy.Foundations.Strengthened

/-!
# Evaluation-context monotonicity for the strengthened semantics

Every member of the five-way strengthened semantics is stable under a
lookup-preserving extension of its operational evaluation context.  Source
typing, basis validity, and realization premises remain unchanged; only the
recursive strengthened premises are transported.
-/

namespace GLang

/- `S.Space.rec`, `S.Ty.rec`, `S.TyAt.rec`, `S.Cob.rec`, and `S.Term.rec` are
rooted entry points of the same generated mutual recursor.  Keeping the
handler proof in one tactic macro avoids five copies of its 54 cases. -/
macro "solve_strengthened_mono" "(" rec:term "," h:term "," psi:term "," sub:term ")" : tactic =>
  `(tactic| (
    refine ($rec
      (motive_1 := fun Gamma Psi s sv _ =>
        forall Psi', Psi.Subctx Psi' -> S.Space Gamma Psi' s sv)
      (motive_2 := fun Gamma Psi tau tauv _ =>
        forall Psi', Psi.Subctx Psi' -> S.Ty Gamma Psi' tau tauv)
      (motive_3 := fun Gamma Psi b tauv _ =>
        forall Psi', Psi.Subctx Psi' -> S.TyAt Gamma Psi' b tauv)
      (motive_4 := fun Gamma Psi b0 env b1 _ =>
        forall Psi', Psi.Subctx Psi' -> S.Cob Gamma Psi' b0 env b1)
      (motive_5 := fun Delta Gamma Psi e b v tauv _ =>
        forall Psi', Psi.Subctx Psi' -> S.Term Delta Gamma Psi' e b v tauv)
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
      ?termZero ?termRlit $h $psi $sub)
    case cobProjKerCoker =>
      intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env2 env3
        sv0 sv1 sv sv' sv0' hbS hbT hs hsofb0 hsofb1
        hsv0 hsv1 hsv hsv' hsv0' hcob hembd hproj
        ihsv0 ihsv1 ihsv ihsv' ihsv0' ihcob ihembd ihproj Psi' hsub
      exact .proj_ker_coker hbS hbT hs hsofb0 hsofb1
        (ihsv0 Psi' hsub) (ihsv1 Psi' hsub) (ihsv Psi' hsub)
        (ihsv' Psi' hsub) (ihsv0' Psi' hsub) (ihcob Psi' hsub)
        (ihembd Psi' hsub) (ihproj Psi' hsub)
    case cobProjImgCoimg =>
      intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env2 env3
        sv0 sv1 sv sv' sv1' hbS hbT hs hsofb0 hsofb1
        hsv0 hsv1 hsv hsv' hsv1' hcob hembd hproj
        ihsv0 ihsv1 ihsv ihsv' ihsv1' ihcob ihembd ihproj Psi' hsub
      exact .proj_img_coimg hbS hbT hs hsofb0 hsofb1
        (ihsv0 Psi' hsub) (ihsv1 Psi' hsub) (ihsv Psi' hsub)
        (ihsv' Psi' hsub) (ihsv1' Psi' hsub) (ihcob Psi' hsub)
        (ihembd Psi' hsub) (ihproj Psi' hsub)
    case cobProjKerCokerCod =>
      intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env3 sv0 sv sv'
        hbS hbT hs hsofb0 hsofb1 hsofb1' hsv0 hsv hsv' hembd hproj
        ihsv0 ihsv ihsv' ihembd ihproj Psi' hsub
      exact .proj_ker_coker_cod hbS hbT hs hsofb0 hsofb1 hsofb1'
        (ihsv0 Psi' hsub) (ihsv Psi' hsub) (ihsv' Psi' hsub)
        (ihembd Psi' hsub) (ihproj Psi' hsub)
    case cobProjImgCoimgDom =>
      intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env3 sv1 sv sv'
        hbS hbT hs hsofb0 hsofb1 hsofb0' hsv1 hsv hsv' hembd hproj
        ihsv1 ihsv ihsv' ihembd ihproj Psi' hsub
      exact .proj_img_coimg_dom hbS hbT hs hsofb0 hsofb1 hsofb0'
        (ihsv1 Psi' hsub) (ihsv Psi' hsub) (ihsv' Psi' hsub)
        (ihembd Psi' hsub) (ihproj Psi' hsub)
    case tyPi =>
      intro Gamma Psi b0 tau0 tau1 tauv0 tauv1 k0 k1 ht hb hbv h0 L h1
        ih0 ih1 Psi' hsub
      exact .piTy ht hb hbv (ih0 Psi' hsub) L fun y hy =>
        ih1 y hy _ (hsub.extend y b0 (.var y tauv0))
    case tyAtFrame =>
      intro Gamma Psi b0 b1 tauv0 tauv1 hbv hdom L hcod
        ihdom ihcod Psi' hsub
      exact .frame hbv (ihdom Psi' hsub) L
        (fun y hy => ihcod y hy _ (hsub.extend y b0 (.var y tauv0)))
    case termVarLin =>
      intro Gamma Psi x b v s tauv h htof hbv htauv ihtauv Psi' hsub
      exact .var_lin (hsub (x, b) v h) htof hbv (ihtauv Psi' hsub)
    case termVarNlin =>
      intro Gamma Psi x b v tauv h hGamma hbv htauv ihtauv Psi' hsub
      exact .var_nlin (hsub (x, b) v h) hGamma hbv (ihtauv Psi' hsub)
    case termNllam =>
      intro Gamma Psi b0 b1 tau0 tau1 e tauv0 tauv1 env
        hb0 hb1 ht hbv htauv h0 L he h1 ihtauv ih0 ihe ih1 Psi' hsub
      exact .nllam hb0 hb1 ht hbv (ihtauv Psi' hsub) (ih0 Psi' hsub) L
        (fun y hy => ihe y hy _ (hsub.extend y b0 (.var y tauv0)))
        (fun y hy => ih1 y hy _ (hsub.extend y b0 (.var y tauv0)))
    case termFrameReanchor =>
      intro Gamma Psi b0 b0' b1 n0 leev env1 tauv0 tauv0' tauv1 tauv1'
        htof ht hbv htauv h0 hfn hdom L hx hcod
        ihtauv ih0 ihfn ihdom ihx ihcod Psi' hsub
      exact .frame_reanchor htof ht hbv (ihtauv Psi' hsub) (ih0 Psi' hsub)
        (ihfn Psi' hsub) (ihdom Psi' hsub) L
        (fun y hy => ihx y hy _ (hsub.extend y b0 (.var y tauv0)))
        (fun y hy => ihcod y hy _ (hsub.extend y b0 (.var y tauv0)))
    case termFrameEta =>
      intro Gamma Psi b0 b1 n0 tauv0 tauv1 env ht hbv htauv h0 L he h1
        ihtauv ih0 ihe ih1 Psi' hsub
      exact .frame_eta ht hbv (ihtauv Psi' hsub) (ih0 Psi' hsub) L
        (fun y hy => ihe y hy _ (hsub.extend y b0 (.var y tauv0)))
        (fun y hy => ih1 y hy _ (hsub.extend y b0 (.var y tauv0)))
    case termLlam =>
      intro Delta Gamma Psi b' b e sv' sv env htof' ht hbv htauv hsv' hsv
        L hfam ihtauv ihsv' ihsv ihfam Psi' hsub
      exact .llam_assemble htof' ht hbv (ihtauv Psi' hsub)
        (ihsv' Psi' hsub) (ihsv Psi' hsub) L fun y hy i =>
          ihfam y hy i _ (hsub.extend y b' (.delta i.val sv'))
    case termLlamReal =>
      intro Delta Gamma Psi b' e sv' env htof' ht hbv htauv hsv' L hfam
        ihtauv ihsv' ihfam Psi' hsub
      exact .llam_assemble_real htof' ht hbv (ihtauv Psi' hsub)
        (ihsv' Psi' hsub) L fun y hy i =>
          ihfam y hy i _ (hsub.extend y b' (.delta i.val sv'))
    case termAppL =>
      intro Delta0 Delta1 Gamma Psi b0 b1 n0 n1 env0 env1
        sv svOut svMat0 svMat1 svArg
        hdisj htof1 ht hbv hsv htv h0 h1 ihsv ihtv ih0 ih1 Psi' hsub
      exact .appL_lin hdisj htof1 ht hbv (ihsv Psi' hsub) (ihtv Psi' hsub)
        (ih0 Psi' hsub) (ih1 Psi' hsub)
    case termAppI =>
      intro Delta0 Delta1 Gamma Psi b0 n0 n1 env0 env1 sv svFun svArg
        hdisj ht hsv htv h0 h1 ihsv ihtv ih0 ih1 Psi' hsub
      exact .appI_lin hdisj ht (ihsv Psi' hsub) (ihtv Psi' hsub)
        (ih0 Psi' hsub) (ih1 Psi' hsub)
    all_goals
      aesop (config := { maxRuleApplications := 1000, maxRuleApplicationDepth := 100 })
        (add safe [S.Space.real, S.Space.empty, S.Space.dual,
          S.Space.ker, S.Space.coker, S.Space.img, S.Space.coimg,
          S.Space.tprod, S.Space.dsum])
        (add safe [S.Ty.space, S.Ty.piTy])
        (add safe [S.TyAt.space, S.TyAt.frame])
        (add safe [S.Cob.inverse, S.Cob.trans, S.Cob.tprod, S.Cob.dsum,
          S.Cob.dual_std, S.Cob.image, S.Cob.image_svds,
          S.Cob.proj_ker_coker, S.Cob.proj_img_coimg, S.Cob.terms_rref,
          S.Cob.refl, S.Cob.proj_ker_coker_cod, S.Cob.proj_img_coimg_dom])
        (add safe [S.Term.var_lin, S.Term.var_nlin, S.Term.promote,
          S.Term.cob, S.Term.reshape_cob, S.Term.scale, S.Term.add,
          S.Term.dsumE, S.Term.tprodE, S.Term.pinvT_std,
          S.Term.pinvT_gpinv, S.Term.pinvD_std, S.Term.pinvD_gpinv,
          S.Term.inner_std, S.Term.embed_ker, S.Term.embed_coker,
          S.Term.embed_img, S.Term.embed_coimg, S.Term.appL_lin,
          S.Term.appI_lin, S.Term.nllam, S.Term.appN_val,
          S.Term.frame_reanchor, S.Term.frame_eta, S.Term.llam_assemble,
          S.Term.llam_assemble_real, S.Term.zero, S.Term.rlit])
        (add safe EvalCtx.Subctx.extend)))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4000 in
theorem S.Space.mono
    {Gamma : NLCtx} {Psi Psi' : EvalCtx} {s : GLang.Space} {sv : ValSpace}
    (h : S.Space Gamma Psi s sv) (hsub : Psi.Subctx Psi') :
    S.Space Gamma Psi' s sv := by
  solve_strengthened_mono(S.Space.rec, h, Psi', hsub)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4000 in
theorem S.Ty.mono
    {Gamma : NLCtx} {Psi Psi' : EvalCtx} {tau : GLang.Ty} {tauv : ValTy}
    (h : S.Ty Gamma Psi tau tauv) (hsub : Psi.Subctx Psi') :
    S.Ty Gamma Psi' tau tauv := by
  solve_strengthened_mono(S.Ty.rec, h, Psi', hsub)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4000 in
theorem S.TyAt.mono
    {Gamma : NLCtx} {Psi Psi' : EvalCtx} {b : Basis} {tauv : ValTy}
    (h : S.TyAt Gamma Psi b tauv) (hsub : Psi.Subctx Psi') :
    S.TyAt Gamma Psi' b tauv := by
  solve_strengthened_mono(S.TyAt.rec, h, Psi', hsub)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4000 in
theorem S.Cob.mono
    {Gamma : NLCtx} {Psi Psi' : EvalCtx} {b0 b1 : Basis} {env : ValExpr}
    (h : S.Cob Gamma Psi b0 env b1) (hsub : Psi.Subctx Psi') :
    S.Cob Gamma Psi' b0 env b1 := by
  solve_strengthened_mono(S.Cob.rec, h, Psi', hsub)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4000 in
theorem S.Term.mono
    {Delta : LCtx} {Gamma : NLCtx} {Psi Psi' : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauv : ValTy}
    (h : S.Term Delta Gamma Psi e b v tauv) (hsub : Psi.Subctx Psi') :
    S.Term Delta Gamma Psi' e b v tauv := by
  solve_strengthened_mono(S.Term.rec, h, Psi', hsub)

end GLang
