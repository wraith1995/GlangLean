import GLang.Proofs.Adequacy.Partial.Source.PartialSourceStructural
import GLang.Proofs.Adequacy.Partial.Functions.PartialSourceFunctions
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceReshape
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceValueBridge

namespace GLang.PartialAdequacy
open Basis (BasisValid)

theorem arm_nllam
    {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    (hpush : PartialDirectOpenPush.OracleOpenPush orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {tau0 tau1 : Ty} {sourceBody : Term}
    {tauv0 tauv1 : ValTy} {env : ValExpr}
    (hb0 : Basis.tof b0 = tau0) (hb1 : Basis.tof b1 = tau1)
    (_ht : Nonempty (HasType ∅ Gamma (.nllam tau0 sourceBody)
      (Basis.tof (.frame b0 b1))))
    (hbv : BasisValid Gamma (.frame b0 b1))
    (hTy : S.TyAt Gamma Psi (.frame b0 b1) (.piTy tauv0 tauv1))
    (hDom : S.TyAt Gamma Psi b0 tauv0)
    (L : Finset Name)
    (he : forall y, y ∉ L ->
      S.Term ∅ (Finmap.insert y tau0 Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Term.openVar y sourceBody) (Basis.openVar y b1)
        (ValExpr.openVar y tauv0 env)
        (ValTy.openVar y tauv0 tauv1))
    (_hCod : forall y, y ∉ L ->
      S.TyAt (Finmap.insert y tau0 Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1) (ValTy.openVar y tauv0 tauv1))
    (ihTy : MTyAtSubctx orc Gamma Psi (.frame b0 b1)
      (.piTy tauv0 tauv1))
    (_ihDom : MTyAtSubctx orc Gamma Psi b0 tauv0)
    (ihBody : forall y, y ∉ L ->
      MTermSubctx orc ∅ (Finmap.insert y tau0 Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Term.openVar y sourceBody) (Basis.openVar y b1)
        (ValExpr.openVar y tauv0 env)
        (ValTy.openVar y tauv0 tauv1))
    (_ihCod : forall y, y ∉ L ->
      MTyAtSubctx orc (Finmap.insert y tau0 Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1) (ValTy.openVar y tauv0 tauv1)) :
    MTermSubctx orc ∅ Gamma Psi
      (.nllam tau0 sourceBody) (.frame b0 b1)
      (.vlam tauv0 tauv1 (.reshap env tauv1 tauv1))
      (.piTy tauv0 tauv1) := by
  subst tau0
  subst tau1
  intro Psi' hsub _hdisj rho Delta' Gamma' sigma GammaV hle hc
  have hdFun : DimsAt orc sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
      (denotBasis sigma (.frame b0 b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hresult : ResultAgree orc sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
      (denotBasis sigma (.frame b0 b1))
      (denotTerm sigma (.nllam (Basis.tof b0) sourceBody))
      (denotValB_partial orc rho [] []
        (.vlam tauv0 tauv1 (.reshap env tauv1 tauv1))) := by
    apply lambda_result hdFun
    intro x' arg harg
    let d := (denotTy sigma (Basis.tof b0)).embed x'
    let w := tauv0.carrierToVal arg
    have hdPi := hdFun
    simp only [Basis.tof, DimsAt] at hdPi
    have hdDom : DimsAt orc sigma rho [] [] []
        (Basis.tof b0) tauv0 (denotBasis sigma b0) := by
      simpa only [denotBasis_frame_domainBasis] using hdPi.1
    have hargDom : Agree orc sigma rho [] [] []
        (Basis.tof b0) tauv0 (denotBasis sigma b0) d w := by
      simpa only [denotBasis_frame_domainBasis, d, w] using harg
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
      (L ∪ Delta'.keys ∪ Gamma'.keys ∪ Psi'.keyNames ∪
        Term.fv sourceBody ∪ Basis.fv b1 ∪ ValExpr.fv env ∪
        ValTy.fv tauv0 ∪ ValTy.fv tauv1)
    simp only [Finset.mem_union, not_or] at hy
    rcases hy with
      ⟨⟨⟨⟨⟨⟨⟨⟨hyL, hyDeltaKeys⟩, hyGammaKeys⟩, hyPsiNames⟩,
        hySourceBody⟩, hyb1⟩, hyEnv⟩, hytauv0⟩, hytauv1⟩
    have hyDelta : y ∉ Delta' :=
      fun hym => hyDeltaKeys (Finmap.mem_keys.mpr hym)
    have hyGamma : y ∉ Gamma' :=
      fun hym => hyGammaKeys (Finmap.mem_keys.mpr hym)
    have hyPsi : forall b, (y, b) ∉ Psi' := by
      intro b hym
      exact hyPsiNames
        (EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hym⟩)
    have hle' : RawCtxIncl ∅
        (Finmap.insert y (Basis.tof b0) Gamma) Delta'
        (Finmap.insert y (Basis.tof b0) Gamma') := by
      refine ⟨?_, ?_⟩
      · intro z s hz
        rw [Finmap.lookup_empty] at hz
        contradiction
      · intro z tau hz
        by_cases hzy : z = y
        · subst z
          simpa only [Finmap.lookup_insert] using hz
        · rw [Finmap.lookup_insert_of_ne _ hzy] at hz ⊢
          exact hle.2 z tau hz
    obtain ⟨hbv0, _hbv1, _k0, _k1, _htFrame⟩ := hbv.frame_inv
    have hc' : TypedHistory orc Delta'
        (Finmap.insert y (Basis.tof b0) Gamma')
        (Psi'.extend y b0 (.var y tauv0))
        (Finmap.insert y tauv0 GammaV) (sigma.bind y d)
        (rho.update y w) := by
      exact TypedHistory.worldExtendNLAt hirr hc hle.2
        ⟨hyDelta, hyGamma, hyPsi⟩ hbv0 hDom.isTyBasis (hDom.mono hsub)
        x' w hargDom hdDom
    let opened := ihBody y hyL
      (hsub.extend y b0 (.var y tauv0))
      (Graded.CtxDisj.empty _)
      (rho.update y w) Delta'
      (Finmap.insert y (Basis.tof b0) Gamma')
      (sigma.bind y d) (Finmap.insert y tauv0 GammaV) hle' hc'
    let openedReshaped : TermTraceAt orc (sigma.bind y d)
        (rho.update y w)
        (.reshap (ValExpr.openVar y tauv0 env)
          (ValTy.openVar y tauv0 tauv1)
          (ValTy.openVar y tauv0 tauv1))
        (Basis.tof (Basis.openVar y b1))
        (ValTy.openVar y tauv0 tauv1)
        (denotBasis (sigma.bind y d) (Basis.openVar y b1))
        (denotTerm (sigma.bind y d) (Term.openVar y sourceBody)) :=
      reshape_compiled ((he y hyL).mono (hsub.extend y b0 (.var y tauv0))) hc'.history hirr opened.dims opened
    obtain ⟨_kind, htOpen⟩ := (he y hyL).ty.tvalid
    have hlcOpen : Ty.lc (Ty.openVar y (Basis.tof b1)) := by
      simpa only [Basis.openVar, Basis.tof_openRec] using
        TValid.lc htOpen.some
    let Bopen := denotBasis (sigma.bind y d) (Basis.openVar y b1)
    obtain ⟨out, hout, hagreeOpen0⟩ := openedReshaped.result
    have hagreeOpenStack : Agree orc (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1) Bopen
        (denotTerm (sigma.bind y d) (Term.openVar y sourceBody)) out := by
      apply (Agree.lc_irrel_src orc hlcOpen
        (ValTy.openVar y tauv0 tauv1) (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen
        (denotTerm (sigma.bind y d) (Term.openVar y sourceBody)) out).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using
        hagreeOpen0
    have hdOpenStack : DimsAt orc (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1) Bopen := by
      apply (DimsAt.lc_irrel_src orc hlcOpen
        (ValTy.openVar y tauv0 tauv1) (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using
        openedReshaped.dims
    have hytof1 : y ∉ Ty.fv (Basis.tof b1) :=
      fun hym => hyb1 (Basis.fv_tof_subset b1 hym)
    have hsourceBridge := Agree.openRec_bind_src orc (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1) [d] [] [] 0 Bopen
      (denotTerm (sigma.bind y d) (Term.openVar y sourceBody)) out hytof1
    simp only [List.getD_cons_zero] at hsourceBridge
    have hagreeSource : Agree orc sigma (rho.update y w) [d] [] []
        (Basis.tof b1) (ValTy.openVar y tauv0 tauv1) Bopen
        (denotTerm (sigma.bind y d) (Term.openVar y sourceBody)) out :=
      hsourceBridge.mp hagreeOpenStack
    have hdSourceBridge := DimsAt.openRec_bind_src orc (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1) [d] [] [] 0 Bopen hytof1
    simp only [List.getD_cons_zero] at hdSourceBridge
    have hdSource : DimsAt orc sigma (rho.update y w) [d] [] []
        (Basis.tof b1) (ValTy.openVar y tauv0 tauv1) Bopen :=
      hdSourceBridge.mp hdOpenStack
    have hsourceOut :
        denotTerm (sigma.bind y d) (Term.openVar y sourceBody) =
          (denotTerm sigma
            (.nllam (Basis.tof b0) sourceBody)).applyEl x' := by
      rw [denotTerm_openVar_bind (he y hyL).hasType.some.lc hySourceBody,
        denotTerm_nllam_applyEl]
    have hbasisOut : Bopen =
        (denotBasis sigma (.frame b0 b1)).applyEl x' := by
      exact (denotBasis_frame_applyEl_openVar y hyb1 x').symm
    have hopenResult : ResultAgree orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1)
        ((denotBasis sigma (.frame b0 b1)).applyEl x')
        ((denotTerm sigma (.nllam (Basis.tof b0) sourceBody)).applyEl x')
        (denotValB_partial orc (rho.update y w) [] []
          (ValExpr.openVar y tauv0 (.reshap env tauv1 tauv1))) := by
      refine ⟨out, ?_, ?_⟩
      · simpa only [ValExpr.openVar, ValExpr.openRec] using hout
      · simpa only [hsourceOut, hbasisOut] using hagreeSource
    have hopenDims : DimsAt orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1)
        ((denotBasis sigma (.frame b0 b1)).applyEl x') := by
      simpa only [hbasisOut] using hdSource
    have htauv0Lc : ValTy.lc tauv0 :=
      evalT_lc (hDom.mono hsub).toEvalT hc.evalCtxLc
    exact ResultAgree.valueOpenPush (G := []) (D := []) hpush htauv0Lc
      hytauv0 (by intro t ht; cases ht) rfl hytauv1
      (by simpa only [ValExpr.fv, Finset.mem_union, not_or] using
        ⟨⟨hyEnv, hytauv1⟩, hytauv1⟩)
      hopenDims hopenResult
  exact ⟨hresult, hdFun⟩

end GLang.PartialAdequacy
