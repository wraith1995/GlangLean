import GLang.Proofs.Adequacy.Raw.RawInferredAgreement

set_option maxHeartbeats 1200000
namespace GLang
open Basis (BasisValid)

/-! ## Direct-mutual rule arms -/

/-- Exact nonlinear lookup.  The stored raw value is transported only
between two realizations of the same source type; it is never decoded and
re-encoded. -/
theorem arm_var_nlin
    {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} {tauv : ValTy}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (_hGamma : Gamma.lookup x = some (Basis.tof b))
    (_hbv : BasisValid Gamma b)
    (hTy : S.TyAt Gamma Psi b tauv)
    (ihTy : RawMTyAtSubctx orc Gamma Psi b tauv) :
    RawMTermTraceSubctx orc ∅ Gamma Psi (.var x) b v tauv := by
  intro Psi' hsub _hdisj rho Delta' Gamma' sigma GammaV hle hc
  have hlookup' : EvalCtx.lookup Psi' (x, b) = some v :=
    hsub (x, b) v hlookup
  obtain ⟨tauStored, xs, Gamma0, Psi0, _hsigma, hStoredTy,
      _hinferSpace, hresult, hdimsStored⟩ :=
    hc.raw.lookup_current_result hirr hlookup'
  have hdimsTarget : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof b) tauv (denotBasis sigma b) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hshape : ValSoundOfDenot.ValTy.SameShape tauStored tauv :=
    evalT_sameShape hStoredTy (hTy.mono hsub).toEvalT
  obtain ⟨out, hout, hagree⟩ := hresult
  exact ⟨⟨out, hout,
    (RawNonBetaValueKernel.holds orc).realize hshape hdimsStored hdimsTarget hagree⟩, hdimsTarget⟩

/-- Checked reshape is a forward consumer of the ordinary child trace. -/
theorem arm_reshape
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauv tauv' : ValTy}
    (_ht : Nonempty (HasType Delta Gamma e (Basis.tof b)))
    (_hbv : BasisValid Gamma b)
    (_hTy : S.TyAt Gamma Psi b tauv')
    (_he : S.Term Delta Gamma Psi e b v tauv)
    (ihTy : RawMTyAtSubctx orc Gamma Psi b tauv')
    (ihE : RawMTermTraceSubctx orc Delta Gamma Psi e b v tauv) :
    RawMTermTraceSubctx orc Delta Gamma Psi e b
      (.reshap v tauv' tauv) tauv' := by
  intro Psi' hsub hdisj rho Delta' Gamma' sigma GammaV hle hc
  let child := ihE hsub hdisj rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof b) tauv' (denotBasis sigma b) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  exact ⟨(RawNonBetaValueKernel.holds orc).reshape targetDims child.dims child.result, targetDims⟩

/-- Nonlinear abstraction closes from the ordinary opened-body IH alone.

The body IH is invoked at a fresh named extension of the current world.  Its
empty-stack result is first wrapped by the identity reshape that occurs in
the strengthened `nllam` result, then transported from the named source and
value presentations to the de Bruijn stacks expected by `vlam`. -/
theorem arm_nllam
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc)
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
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.frame b0 b1)
      (.piTy tauv0 tauv1))
    (_ihDom : RawMTyAtSubctx orc Gamma Psi b0 tauv0)
    (ihBody : forall y, y ∉ L ->
      RawMTermTraceSubctx orc ∅ (Finmap.insert y tau0 Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Term.openVar y sourceBody) (Basis.openVar y b1)
        (ValExpr.openVar y tauv0 env)
        (ValTy.openVar y tauv0 tauv1))
    (_ihCod : forall y, y ∉ L ->
      RawMTyAtSubctx orc (Finmap.insert y tau0 Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1) (ValTy.openVar y tauv0 tauv1)) :
    RawMTermTraceSubctx orc ∅ Gamma Psi
      (.nllam tau0 sourceBody) (.frame b0 b1)
      (.vlam tauv0 tauv1 (.reshap env tauv1 tauv1))
      (.piTy tauv0 tauv1) := by
  subst tau0
  subst tau1
  intro Psi' hsub _hdisj rho Delta' Gamma' sigma GammaV hle hc
  have hdFun : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
      (denotBasis sigma (.frame b0 b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hresult : RawResultAgree orc sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
      (denotBasis sigma (.frame b0 b1))
      (denotTerm sigma (.nllam (Basis.tof b0) sourceBody))
      (denotValB_semS orc rho [] []
        (.vlam tauv0 tauv1 (.reshap env tauv1 tauv1))) := by
    apply (RawNonBetaValueKernel.holds orc).vlam (.reshap env tauv1 tauv1) hdFun
    intro x' arg harg
    let d := (denotTy sigma (Basis.tof b0)).embed x'
    let w := ValValSem.fromEl (denotValTyS orc rho [] [] tauv0) arg
    have hdPi := hdFun
    simp only [Basis.tof, RawAgreeDimsAt] at hdPi
    have hdDom : RawAgreeDimsAt orc sigma rho [] [] []
        (Basis.tof b0) tauv0 (denotBasis sigma b0) := by
      simpa only [denotBasis_frame_domainBasis] using hdPi.1
    have hargDom : RawAgree orc sigma rho [] [] []
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
    have hc' : RawTypedConsistent orc Delta'
        (Finmap.insert y (Basis.tof b0) Gamma')
        (Psi'.extend y b0 (.var y tauv0))
        (Finmap.insert y tauv0 GammaV) (sigma.bind y d)
        (rho.update y w) := by
      exact RawTypedConsistent.worldExtendNLAt
        hspec.toOracleSpec.fvIrrel hc hle.2
        ⟨hyDelta, hyGamma, hyPsi⟩ hbv0 hDom.isTyBasis (hDom.mono hsub)
        x' w hargDom hdDom
    let opened := ihBody y hyL
      (hsub.extend y b0 (.var y tauv0))
      (Graded.CtxDisj.empty _)
      (rho.update y w) Delta'
      (Finmap.insert y (Basis.tof b0) Gamma')
      (sigma.bind y d) (Finmap.insert y tauv0 GammaV) hle' hc'
    let openedReshaped : RawTermTraceAt orc (sigma.bind y d)
        (rho.update y w)
        (.reshap (ValExpr.openVar y tauv0 env)
          (ValTy.openVar y tauv0 tauv1)
          (ValTy.openVar y tauv0 tauv1))
        (Basis.tof (Basis.openVar y b1))
        (ValTy.openVar y tauv0 tauv1)
        (denotBasis (sigma.bind y d) (Basis.openVar y b1))
        (denotTerm (sigma.bind y d) (Term.openVar y sourceBody)) :=
      ⟨(RawNonBetaValueKernel.holds orc).reshape opened.dims opened.dims opened.result, opened.dims⟩
    obtain ⟨_kind, htOpen⟩ := (he y hyL).ty.tvalid
    have hlcOpen : Ty.lc (Ty.openVar y (Basis.tof b1)) := by
      simpa only [Basis.openVar, Basis.tof_openRec] using
        TValid.lc htOpen.some
    let Bopen := denotBasis (sigma.bind y d) (Basis.openVar y b1)
    obtain ⟨out, hout, hagreeOpen0⟩ := openedReshaped.result
    have hagreeOpenStack : RawAgree orc (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1) Bopen
        (denotTerm (sigma.bind y d) (Term.openVar y sourceBody)) out := by
      apply (RawAgree.lc_irrel_src orc hlcOpen
        (ValTy.openVar y tauv0 tauv1) (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen
        (denotTerm (sigma.bind y d) (Term.openVar y sourceBody)) out).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using
        hagreeOpen0
    have hdOpenStack : RawAgreeDimsAt orc (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1) Bopen := by
      apply (RawAgreeDimsAt.lc_irrel_src orc hlcOpen
        (ValTy.openVar y tauv0 tauv1) (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using
        openedReshaped.dims
    have hytof1 : y ∉ Ty.fv (Basis.tof b1) :=
      fun hym => hyb1 (Basis.fv_tof_subset b1 hym)
    have hsourceBridge := RawAgree.openRec_bind_src orc (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1) [d] [] [] 0 Bopen
      (denotTerm (sigma.bind y d) (Term.openVar y sourceBody)) out hytof1
    simp only [List.getD_cons_zero] at hsourceBridge
    have hagreeSource : RawAgree orc sigma (rho.update y w) [d] [] []
        (Basis.tof b1) (ValTy.openVar y tauv0 tauv1) Bopen
        (denotTerm (sigma.bind y d) (Term.openVar y sourceBody)) out :=
      hsourceBridge.mp hagreeOpenStack
    have hdSourceBridge := RawAgreeDimsAt.openRec_bind_src orc (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1) [d] [] [] 0 Bopen hytof1
    simp only [List.getD_cons_zero] at hdSourceBridge
    have hdSource : RawAgreeDimsAt orc sigma (rho.update y w) [d] [] []
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
    have hopenResult : RawResultAgree orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1)
        ((denotBasis sigma (.frame b0 b1)).applyEl x')
        ((denotTerm sigma (.nllam (Basis.tof b0) sourceBody)).applyEl x')
        (denotValB_semS orc (rho.update y w) [] []
          (ValExpr.openVar y tauv0 (.reshap env tauv1 tauv1))) := by
      refine ⟨out, ?_, ?_⟩
      · simpa only [ValExpr.openVar, ValExpr.openRec] using hout
      · simpa only [hsourceOut, hbasisOut] using hagreeSource
    have hopenDims : RawAgreeDimsAt orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1)
        ((denotBasis sigma (.frame b0 b1)).applyEl x') := by
      simpa only [hbasisOut] using hdSource
    have htauv0Lc : ValTy.lc tauv0 :=
      evalT_lc (hDom.mono hsub).toEvalT hc.evalCtxLc
    have hopenEnvLc : ValExpr.lc (ValExpr.openVar y tauv0 env) :=
      opStep_lc
        ((he y hyL).mono (hsub.extend y b0 (.var y tauv0))).toOpStep
        hc'.evalCtxLc
    have hopenTauv1Lc : ValTy.lc (ValTy.openVar y tauv0 tauv1) :=
      evalT_lc
        ((he y hyL).mono (hsub.extend y b0 (.var y tauv0))).ty.toEvalT
        hc'.evalCtxLc
    have hopenBodyLc : ValExpr.lc
        (ValExpr.openVar y tauv0 (.reshap env tauv1 tauv1)) := by
      simpa only [ValExpr.openVar, ValExpr.openRec] using
        ValExpr.lc.reshap hopenEnvLc hopenTauv1Lc hopenTauv1Lc
    exact hspec.rawResultBinderCoherent htauv0Lc hopenBodyLc
      hytauv0 hytauv1
      (by simpa only [ValExpr.fv, Finset.mem_union, not_or] using
        ⟨⟨hyEnv, hytauv1⟩, hytauv1⟩)
      hopenDims hopenResult
  exact ⟨hresult, hdFun⟩

/-- Ordinary nonlinear application consumes only the ordinary traces of its
function and argument.  Source soundness recovers the raw function carrier;
the two structural lemmas above recover the value-level domain and codomain
skeletons; and the exact type IH supplies the independently compiled output
dimensions. -/
theorem arm_appN_val
    {orc : FFSOracleSem} (hsubst : RuntimeValue.TotalSubstitution.CodomainLaw orc)
    (hirr : OracleFvIrrel orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {n0 n1 : Term}
    {env0 env1 : ValExpr}
    {tauFun0 tauFun1 tauArg tauOut : ValTy}
    (_ht : Nonempty (HasType ∅ Gamma (.appN n0 n1)
      (Basis.tof (Basis.instantiate n1 b1))))
    (_hbv : BasisValid Gamma (Basis.instantiate n1 b1))
    (hTy : S.TyAt Gamma Psi (Basis.instantiate n1 b1) tauOut)
    (h0 : S.Term ∅ Gamma Psi n0 (.frame b0 b1) env0
      (.piTy tauFun0 tauFun1))
    (h1 : S.Term ∅ Gamma Psi n1 b0 env1 tauArg)
    (ihTy : RawMTyAtSubctx orc Gamma Psi
      (Basis.instantiate n1 b1) tauOut)
    (ih0 : RawMTermTraceSubctx orc ∅ Gamma Psi n0
      (.frame b0 b1) env0 (.piTy tauFun0 tauFun1))
    (ih1 : RawMTermTraceSubctx orc ∅ Gamma Psi n1
      b0 env1 tauArg)
    (ih1Dof : RawMDofTraceSubctx orc Gamma Psi env1 tauArg) :
    RawMTermTraceSubctx orc ∅ Gamma Psi (.appN n0 n1)
      (Basis.instantiate n1 b1) (.applyAt env0 env1 tauOut) tauOut := by
  intro Psi' hsub _hdisj rho Delta' Gamma' sigma GammaV hle hc
  let function := ih0 hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  let argument := ih1 hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof (Basis.instantiate n1 b1)) tauOut
      (denotBasis sigma (Basis.instantiate n1 b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨ht1⟩ := hasType_mono_nl_raw h1.hasType hle.2
  have hmatch : (denotTerm sigma n1).matchesShape
      (denotTy sigma (Basis.tof b0)) :=
    (soundness ht1 hc.ctxWF_nl hc.envWF_nl).1
  obtain ⟨ht0⟩ := hasType_mono_nl_raw h0.hasType hle.2
  have hfunShape : (denotTerm sigma n0).matchesShape
      (denotTy sigma (Basis.tof (.frame b0 b1))) :=
    (soundness ht0 hc.ctxWF_nl hc.envWF_nl).1
  obtain ⟨g, hpi, _hg⟩ := DVal.matchesShape_sec_eq hfunShape
  have function' := RawTermTraceAt.inferred (h0.mono hsub) hc.raw hirr function
    (by intro sv hs; cases hs)
  have argument' := RawTermTraceAt.inferred (h1.mono hsub) hc.raw hirr argument
    (fun sv hs => ih1Dof hs hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have hshape := raw_inferType_sameShape (h0.mono hsub) hc.raw
  have hcshape := appN_codomain_sameShape h0 hTy
  cases hi : ValExpr.inferTypeCtx [] env0 with
  | space s => simp only [hi,ValSoundOfDenot.ValTy.SameShape] at hshape
  | piTy d c =>
    rw [hi] at function'
    simp only [hi,ValSoundOfDenot.ValTy.SameShape] at hshape
    have hv := hc.context.evalContext.valid.some
    have hft := (RuntimeValue.preservation_mutual.2.2.2
      (h0.mono hsub).toOpStep GammaV hc.context.evalContext).at
      (by simpa only [ValExpr.inferTypeCtx_nil] using hi)
    have hat := (RuntimeValue.preservation_mutual.2.2.2
      (h1.mono hsub).toOpStep GammaV hc.context.evalContext).some
    obtain ⟨k,hpiValid⟩ := hft.regular hv
    have hd : ∃ kd, Nonempty (RuntimeValue.ValTValid GammaV d kd) := by
      cases hpiValid with
      | piTy L hd hc => exact ⟨_,⟨hd⟩⟩
    have hfk := RuntimeValue.operational_kind_of_context
      (h0.mono hsub).toOpStep hc.context.evalContext.regular
    have hak := RuntimeValue.operational_kind_of_context
      (h1.mono hsub).toOpStep hc.context.evalContext.regular
    have hi' : ValExpr.inferType env0 = .piTy d c := by
      simpa only [ValExpr.inferTypeCtx_nil] using hi
    simp only [hi',ValTy.structuralKind,Basis.tof,Ty.sourceKind,ValKind.arrow.injEq] at hfk
    have hkind := hak.trans hfk.1.symm
    have hk := (hat.regular hv).2.kind_eq_structural.trans
      (hkind.trans hd.choose_spec.some.kind_eq_structural.symm)
    have hu := RuntimeValue.ValHasType.reshap hat (hk ▸ (hat.regular hv).2) hd.choose_spec.some
    exact rawApplyAt_result h1.hasType.some.lc hmatch ⟨g,hpi⟩ hi
      (hshape.2.trans hcshape) function' argument' targetDims
      (fun raw he => hsubst hv hpiValid hu rho raw he)

/-- Frame re-anchoring also closes with the ordinary carrier. -/
theorem arm_frame_reanchor
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b0' b1 : Basis} {n0 : Term}
    {leev env1 : ValExpr} {tauv0 tauv0' tauv1 tauv1' : ValTy}
    (htof : Basis.tof b0' = Basis.tof b0)
    (_ht : Nonempty (HasType ∅ Gamma n0 (Basis.tof (.frame b0 b1))))
    (hbv : BasisValid Gamma (.frame b0 b1))
    (hTy : S.TyAt Gamma Psi (.frame b0 b1) (.piTy tauv0 tauv1'))
    (h0 : S.TyAt Gamma Psi b0 tauv0)
    (hfn : S.Term ∅ Gamma Psi n0 (.frame b0' b1) leev
      (.piTy tauv0' tauv1))
    (hdom : S.TyAt Gamma Psi b0' tauv0')
    (L : Finset Name)
    (hx : forall y, y ∉ L ->
      S.Term ∅ (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (.var y) b0' (ValExpr.openVar y tauv0 env1) tauv0')
    (hcod : forall y, y ∉ L ->
      S.TyAt (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1) (ValTy.openVar y tauv0 tauv1'))
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.frame b0 b1)
      (.piTy tauv0 tauv1'))
    (_ih0 : RawMTyAtSubctx orc Gamma Psi b0 tauv0)
    (ihFn : RawMTermTraceSubctx orc ∅ Gamma Psi n0
      (.frame b0' b1) leev (.piTy tauv0' tauv1))
    (_ihDom : RawMTyAtSubctx orc Gamma Psi b0' tauv0')
    (ihX : forall y, y ∉ L ->
      RawMTermTraceSubctx orc ∅
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (.var y) b0' (ValExpr.openVar y tauv0 env1) tauv0')
    (ihCod : forall y, y ∉ L ->
      RawMTyAtSubctx orc
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1) (ValTy.openVar y tauv0 tauv1')) :
    RawMTermTraceSubctx orc ∅ Gamma Psi n0 (.frame b0 b1)
      (.vlam tauv0 tauv1'
        (.reshap
          (.applyValue leev (.reshap env1 tauv0' tauv0'))
          tauv1' tauv1'))
      (.piTy tauv0 tauv1') := by
  intro Psi' hsub _hdisj rho Delta' Gamma' sigma GammaV hle hc
  have hdFun : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1')
      (denotBasis sigma (.frame b0 b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hresult : RawResultAgree orc sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1')
      (denotBasis sigma (.frame b0 b1)) (denotTerm sigma n0)
      (denotValB_semS orc rho [] []
        (.vlam tauv0 tauv1'
          (.reshap
            (.applyValue leev (.reshap env1 tauv0' tauv0'))
            tauv1' tauv1'))) := by
    apply (RawNonBetaValueKernel.holds orc).vlam
      (.reshap
        (.applyValue leev (.reshap env1 tauv0' tauv0'))
        tauv1' tauv1') hdFun
    intro x' arg harg
    let d := (denotTy sigma (Basis.tof b0)).embed x'
    let w := ValValSem.fromEl (denotValTyS orc rho [] [] tauv0) arg
    have hdPi := hdFun
    simp only [Basis.tof, RawAgreeDimsAt] at hdPi
    have hdDom : RawAgreeDimsAt orc sigma rho [] [] []
        (Basis.tof b0) tauv0 (denotBasis sigma b0) := by
      simpa only [denotBasis_frame_domainBasis] using hdPi.1
    have hargDom : RawAgree orc sigma rho [] [] []
        (Basis.tof b0) tauv0 (denotBasis sigma b0) d w := by
      simpa only [denotBasis_frame_domainBasis, d, w] using harg
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
      (L ∪ Delta'.keys ∪ Gamma'.keys ∪ Psi'.names ∪
        Term.fv n0 ∪ Basis.fv b0 ∪ Basis.fv b0' ∪ Basis.fv b1 ∪
        ValExpr.fv leev ∪ ValExpr.fv env1 ∪
        ValTy.fv tauv0 ∪ ValTy.fv tauv0' ∪
        ValTy.fv tauv1 ∪ ValTy.fv tauv1')
    have hyL : y ∉ L := fun hm => hy (by simp [hm])
    have hyDeltaKeys : y ∉ Delta'.keys := fun hm => hy (by simp [hm])
    have hyGammaKeys : y ∉ Gamma'.keys := fun hm => hy (by simp [hm])
    have hyPsiNames : y ∉ Psi'.names := fun hm => hy (by simp [hm])
    have hyn0 : y ∉ Term.fv n0 := fun hm => hy (by simp [hm])
    have hyb0 : y ∉ Basis.fv b0 := fun hm => hy (by simp [hm])
    have _hyb0' : y ∉ Basis.fv b0' := fun hm => hy (by simp [hm])
    have hyb1 : y ∉ Basis.fv b1 := fun hm => hy (by simp [hm])
    have hyleev : y ∉ ValExpr.fv leev := fun hm => hy (by simp [hm])
    have hyenv1 : y ∉ ValExpr.fv env1 := fun hm => hy (by simp [hm])
    have hytauv0 : y ∉ ValTy.fv tauv0 := fun hm => hy (by simp [hm])
    have hytauv0' : y ∉ ValTy.fv tauv0' := fun hm => hy (by simp [hm])
    have _hytauv1 : y ∉ ValTy.fv tauv1 := fun hm => hy (by simp [hm])
    have hytauv1' : y ∉ ValTy.fv tauv1' := fun hm => hy (by simp [hm])
    have hyDelta : y ∉ Delta' :=
      fun hym => hyDeltaKeys (Finmap.mem_keys.mpr hym)
    have hyGamma : y ∉ Gamma' :=
      fun hym => hyGammaKeys (Finmap.mem_keys.mpr hym)
    have hyPsi : forall b, (y, b) ∉ Psi' := by
      intro b hym
      exact hyPsiNames (Finset.mem_image.mpr
        ⟨(y, b), Finmap.mem_keys.mpr hym, rfl⟩)
    have hleOpen : RawCtxIncl ∅
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
    have hleFn : RawCtxIncl ∅ Gamma Delta'
        (Finmap.insert y (Basis.tof b0) Gamma') :=
      ⟨fun _ _ hz => by simp at hz,
        hle.2.insert_right hyGamma (Basis.tof b0)⟩
    have hright : Psi'.Subctx
        (Psi'.extend y b0 (.var y tauv0)) :=
      EvalCtx.Subctx.extend_right_of_name_fresh hyPsiNames b0
        (.var y tauv0)
    have hsubFn : Psi.Subctx
        (Psi'.extend y b0 (.var y tauv0)) := hsub.trans hright
    have hsubOpen : (Psi.extend y b0 (.var y tauv0)).Subctx
        (Psi'.extend y b0 (.var y tauv0)) := hsub.extend y b0 (.var y tauv0)
    obtain ⟨hbv0, _hbv1, _k0, _k1, _htFrame⟩ := hbv.frame_inv
    have hc' : RawTypedConsistent orc Delta'
        (Finmap.insert y (Basis.tof b0) Gamma')
        (Psi'.extend y b0 (.var y tauv0))
        (Finmap.insert y tauv0 GammaV) (sigma.bind y d)
        (rho.update y w) := by
      exact RawTypedConsistent.worldExtendNLAt
        hspec.toOracleSpec.fvIrrel hc hle.2
        ⟨hyDelta, hyGamma, hyPsi⟩ hbv0 h0.isTyBasis (h0.mono hsub)
        x' w hargDom hdDom
    let function := ihFn hsubFn (Graded.CtxDisj.empty Gamma)
      (rho.update y w) Delta'
      (Finmap.insert y (Basis.tof b0) Gamma') (sigma.bind y d)
      (Finmap.insert y tauv0 GammaV) hleFn hc'
    let converted0 := ihX y hyL hsubOpen
      (Graded.CtxDisj.empty (Finmap.insert y (Basis.tof b0) Gamma))
      (rho.update y w) Delta'
      (Finmap.insert y (Basis.tof b0) Gamma') (sigma.bind y d)
      (Finmap.insert y tauv0 GammaV) hleOpen hc'
    let converted : RawTermTraceAt orc (sigma.bind y d) (rho.update y w)
        (.reshap (ValExpr.openVar y tauv0 env1) tauv0' tauv0')
        (Basis.tof b0') tauv0' (denotBasis (sigma.bind y d) b0')
        (denotTerm (sigma.bind y d) (.var y)) :=
      ⟨(RawNonBetaValueKernel.holds orc).reshape converted0.dims converted0.dims converted0.result,
        converted0.dims⟩
    have targetDims0 := ihCod y hyL hsubOpen
      (rho.update y w) Delta'
      (Finmap.insert y (Basis.tof b0) Gamma') (sigma.bind y d)
      (Finmap.insert y tauv0 GammaV) hleOpen.2 hc'
    have targetDims : RawAgreeDimsAt orc (sigma.bind y d)
        (rho.update y w) [] [] []
        (Basis.tof (Basis.instantiate (.var y) b1))
        (ValTy.openVar y tauv0 tauv1')
        (denotBasis (sigma.bind y d) (Basis.instantiate (.var y) b1)) := by
      simpa only [Basis.instantiate] using targetDims0
    have hfnCurrent := hfn.mono hsubFn
    have hxCurrent := (hx y hyL).mono hsubOpen
    obtain ⟨htx⟩ := hasType_mono_nl_raw hxCurrent.hasType hleOpen.2
    have hmatch : (denotTerm (sigma.bind y d) (.var y)).matchesShape
        (denotTy (sigma.bind y d) (Basis.tof b0')) :=
      (soundness htx hc'.ctxWF_nl hc'.envWF_nl).1
    obtain ⟨htfn⟩ := hasType_mono_nl_raw hfnCurrent.hasType hleFn.2
    have hfunShape : (denotTerm (sigma.bind y d) n0).matchesShape
        (denotTy (sigma.bind y d) (Basis.tof (.frame b0' b1))) :=
      (soundness htfn hc'.ctxWF_nl hc'.envWF_nl).1
    obtain ⟨g, hpi, _hg⟩ := DVal.matchesShape_sec_eq hfunShape
    have hcodCurrent := (hcod y hyL).mono hsubOpen
    have hcodomain : ValSoundOfDenot.ValTy.SameShape tauv1
        (ValTy.openVar y tauv0 tauv1') :=
      appN_codomain_sameShape (n1 := .var y) hfnCurrent (by
        simpa only [Basis.instantiate] using hcodCurrent)
    have function' := RawTermTraceAt.inferred hfnCurrent hc'.raw
      hspec.toOracleSpec.fvIrrel function (by intro sv hs; cases hs)
    have opened : RawTermTraceAt orc (sigma.bind y d) (rho.update y w)
        (.reshap (.applyValue leev (.reshap (ValExpr.openVar y tauv0 env1) tauv0' tauv0'))
          (ValTy.openVar y tauv0 tauv1') (ValTy.openVar y tauv0 tauv1'))
        (Basis.tof (Basis.openVar y b1)) (ValTy.openVar y tauv0 tauv1')
        (denotBasis (sigma.bind y d) (Basis.openVar y b1))
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) := by
      have hshape := raw_inferType_sameShape hfnCurrent hc'.raw
      cases hf : ValExpr.inferTypeCtx [] leev with
      | space sv => simp only [hf,ValSoundOfDenot.ValTy.SameShape] at hshape
      | piTy dom cod =>
        rw [hf] at function'
        simp only [hf,ValSoundOfDenot.ValTy.SameShape] at hshape
        simpa only [Basis.instantiate] using
          rawApplyAtSelf_result Term.lc.var hmatch ⟨g,hpi⟩ hf
            (hshape.2.trans hcodomain) function' converted targetDims
    obtain ⟨_kind, htOpen⟩ := hcodCurrent.toTy.tvalid
    have hlcOpen : Ty.lc (Ty.openVar y (Basis.tof b1)) := by
      simpa only [Basis.openVar, Basis.tof_openRec] using
        TValid.lc htOpen.some
    let Bopen := denotBasis (sigma.bind y d) (Basis.openVar y b1)
    obtain ⟨out, hout, hagreeOpen0⟩ := opened.result
    have hagreeOpenStack : RawAgree orc (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1') Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out := by
      apply (RawAgree.lc_irrel_src orc hlcOpen
        (ValTy.openVar y tauv0 tauv1') (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using
        hagreeOpen0
    have hdOpenStack : RawAgreeDimsAt orc (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1') Bopen := by
      apply (RawAgreeDimsAt.lc_irrel_src orc hlcOpen
        (ValTy.openVar y tauv0 tauv1') (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using opened.dims
    have hytof1 : y ∉ Ty.fv (Basis.tof b1) :=
      fun hym => hyb1 (Basis.fv_tof_subset b1 hym)
    have hsourceBridge := RawAgree.openRec_bind_src orc (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1') [d] [] [] 0 Bopen
      (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out hytof1
    simp only [List.getD_cons_zero] at hsourceBridge
    have hagreeSource : RawAgree orc sigma (rho.update y w) [d] [] []
        (Basis.tof b1) (ValTy.openVar y tauv0 tauv1') Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out :=
      hsourceBridge.mp hagreeOpenStack
    have hdSourceBridge := RawAgreeDimsAt.openRec_bind_src orc (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1') [d] [] [] 0 Bopen hytof1
    simp only [List.getD_cons_zero] at hdSourceBridge
    have hdSource : RawAgreeDimsAt orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1') Bopen :=
      hdSourceBridge.mp hdOpenStack
    let Tinner := denotTy (sigma.bind y d) (Basis.tof b0')
    let xInner : Tinner.El :=
      Tinner.extract (denotTerm (sigma.bind y d) (.var y))
    have hembedInner : Tinner.embed xInner =
        denotTerm (sigma.bind y d) (.var y) := by
      exact HType.embed_extract_of_matchesShape hmatch
    have hytof0 : y ∉ Ty.fv (Basis.tof b0) :=
      fun hym => hyb0 (Basis.fv_tof_subset b0 hym)
    have hT : Tinner = denotTy sigma (Basis.tof b0) := by
      dsimp only [Tinner]
      rw [htof]
      exact denotTy_agree _
        (DEnv.AgreeOn.bind_left_of_not_mem hytof0)
    have hxcast : hT ▸ xInner = x' := by
      apply htype_embed_injective_raw (denotTy sigma (Basis.tof b0))
      calc
        (denotTy sigma (Basis.tof b0)).embed (hT ▸ xInner) =
            Tinner.embed xInner := htype_embed_cast_raw hT xInner
        _ = denotTerm (sigma.bind y d) (.var y) := hembedInner
        _ = d := denotTerm_bind_self sigma y d
        _ = (denotTy sigma (Basis.tof b0)).embed x' := rfl
    have hn0 : denotTerm (sigma.bind y d) n0 = denotTerm sigma n0 :=
      denotTerm_agree n0 (DEnv.AgreeOn.bind_left_of_not_mem hyn0)
    have hsourceOut :
        denotTerm (sigma.bind y d) (.appN n0 (.var y)) =
          (denotTerm sigma n0).applyEl x' := by
      rw [denotTerm_appN_applyEl_raw hpi hmatch]
      change (denotTerm (sigma.bind y d) n0).applyEl xInner = _
      calc
        _ = (denotTerm sigma n0).applyEl xInner :=
          congrArg (fun z => z.applyEl xInner) hn0
        _ = (denotTerm sigma n0).applyEl (hT ▸ xInner) :=
          (dval_applyEl_hcast_raw hT (denotTerm sigma n0) xInner).symm
        _ = (denotTerm sigma n0).applyEl x' :=
          congrArg (denotTerm sigma n0).applyEl hxcast
    have hbasisOut : Bopen =
        (denotBasis sigma (.frame b0 b1)).applyEl x' :=
      (denotBasis_frame_applyEl_openVar y hyb1 x').symm
    have hleevLc : ValExpr.lc leev :=
      opStep_lc hfnCurrent.toOpStep hc'.evalCtxLc
    have htauv0'Lc : ValTy.lc tauv0' :=
      evalT_lc (hdom.mono hsubFn).toEvalT hc'.evalCtxLc
    have hopenValue :
        ValExpr.openVar y tauv0
          (.reshap
            (.applyValue leev (.reshap env1 tauv0' tauv0'))
            tauv1' tauv1') =
        .reshap
          (.applyValue leev
            (.reshap (ValExpr.openVar y tauv0 env1) tauv0' tauv0'))
          (ValTy.openVar y tauv0 tauv1')
          (ValTy.openVar y tauv0 tauv1') := by
      simp only [ValExpr.openVar, ValExpr.applyValue, ValExpr.openRec, ValExpr.inferType,
        ValExpr.openRec_lc hleevLc 0 (.var y tauv0),
        ValTy.openRec_lc htauv0'Lc 0 (.var y tauv0),
        ValTy.openRec_lc hleevLc.inferType.domain 0 (.var y tauv0)]
    have hopenResult : RawResultAgree orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1')
        ((denotBasis sigma (.frame b0 b1)).applyEl x')
        ((denotTerm sigma n0).applyEl x')
        (denotValB_semS orc (rho.update y w) [] []
          (ValExpr.openVar y tauv0
            (.reshap
              (.applyValue leev (.reshap env1 tauv0' tauv0'))
              tauv1' tauv1'))) := by
      refine ⟨out, ?_, ?_⟩
      · rw [hopenValue]
        exact hout
      · simpa only [hsourceOut, hbasisOut] using hagreeSource
    have hopenDims : RawAgreeDimsAt orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1')
        ((denotBasis sigma (.frame b0 b1)).applyEl x') := by
      simpa only [hbasisOut] using hdSource
    have hyBody : y ∉ ValExpr.fv
        (.reshap
          (.applyValue leev (.reshap env1 tauv0' tauv0'))
          tauv1' tauv1') := by
      simp only [ValExpr.fv, Finset.mem_union, not_or]
      refine ⟨⟨?_,hytauv1'⟩,hytauv1'⟩
      intro hm
      have hm' := ValExpr.fv_applyValue_subset _ _ hm
      simpa [ValExpr.fv,hyleev,hyenv1,hytauv0'] using hm'
    have htauv0Lc : ValTy.lc tauv0 :=
      evalT_lc (h0.mono hsub).toEvalT hc.evalCtxLc
    have hopenEnv1Lc : ValExpr.lc (ValExpr.openVar y tauv0 env1) :=
      opStep_lc hxCurrent.toOpStep hc'.evalCtxLc
    have hopenTauv1'Lc : ValTy.lc (ValTy.openVar y tauv0 tauv1') :=
      evalT_lc hcodCurrent.toEvalT hc'.evalCtxLc
    have hopenBodyLc : ValExpr.lc
        (ValExpr.openVar y tauv0
          (.reshap
            (.applyValue leev (.reshap env1 tauv0' tauv0'))
            tauv1' tauv1')) := by
      rw [hopenValue]
      exact .reshap
        (.appV hleevLc
          (.reshap (.reshap hopenEnv1Lc htauv0'Lc htauv0'Lc)
            hleevLc.inferType.domain htauv0'Lc))
        hopenTauv1'Lc hopenTauv1'Lc
    exact hspec.rawResultBinderCoherent htauv0Lc hopenBodyLc
      hytauv0 hytauv1' hyBody
      hopenDims hopenResult
  exact ⟨hresult, hdFun⟩

/-- Frame eta is the degenerate re-anchoring case in which the strengthened
rule already supplies the whole opened application as one recursive premise.
Its ordinary trace can therefore be closed by exactly the same fresh
named-to-de-Bruijn path as `nllam`; source soundness only identifies the
named application with the original function applied to the canonical raw
argument. -/
theorem arm_frame_eta
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {n0 : Term}
    {tauv0 tauv1 : ValTy} {env : ValExpr}
    (ht : Nonempty (HasType ∅ Gamma n0 (Basis.tof (.frame b0 b1))))
    (hbv : BasisValid Gamma (.frame b0 b1))
    (_hTy : S.TyAt Gamma Psi (.frame b0 b1) (.piTy tauv0 tauv1))
    (h0 : S.TyAt Gamma Psi b0 tauv0)
    (L : Finset Name)
    (he : forall y, y ∉ L ->
      S.Term ∅ (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (.appN n0 (.var y)) (Basis.openVar y b1)
        (ValExpr.openVar y tauv0 env) (ValTy.openVar y tauv0 tauv1))
    (_h1 : forall y, y ∉ L ->
      S.TyAt (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1) (ValTy.openVar y tauv0 tauv1))
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.frame b0 b1)
      (.piTy tauv0 tauv1))
    (_ih0 : RawMTyAtSubctx orc Gamma Psi b0 tauv0)
    (ihE : forall y, y ∉ L ->
      RawMTermTraceSubctx orc ∅
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (.appN n0 (.var y)) (Basis.openVar y b1)
        (ValExpr.openVar y tauv0 env) (ValTy.openVar y tauv0 tauv1))
    (_ih1 : forall y, y ∉ L ->
      RawMTyAtSubctx orc
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1) (ValTy.openVar y tauv0 tauv1)) :
    RawMTermTraceSubctx orc ∅ Gamma Psi n0 (.frame b0 b1)
      (.vlam tauv0 tauv1 (.reshap env tauv1 tauv1))
      (.piTy tauv0 tauv1) := by
  intro Psi' hsub _hdisj rho Delta' Gamma' sigma GammaV hle hc
  have hdFun : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
      (denotBasis sigma (.frame b0 b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hresult : RawResultAgree orc sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
      (denotBasis sigma (.frame b0 b1)) (denotTerm sigma n0)
      (denotValB_semS orc rho [] []
        (.vlam tauv0 tauv1 (.reshap env tauv1 tauv1))) := by
    apply (RawNonBetaValueKernel.holds orc).vlam (.reshap env tauv1 tauv1) hdFun
    intro x' arg harg
    let d := (denotTy sigma (Basis.tof b0)).embed x'
    let w := ValValSem.fromEl (denotValTyS orc rho [] [] tauv0) arg
    have hdPi := hdFun
    simp only [Basis.tof, RawAgreeDimsAt] at hdPi
    have hdDom : RawAgreeDimsAt orc sigma rho [] [] []
        (Basis.tof b0) tauv0 (denotBasis sigma b0) := by
      simpa only [denotBasis_frame_domainBasis] using hdPi.1
    have hargDom : RawAgree orc sigma rho [] [] []
        (Basis.tof b0) tauv0 (denotBasis sigma b0) d w := by
      simpa only [denotBasis_frame_domainBasis, d, w] using harg
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
      (L ∪ Delta'.keys ∪ Gamma'.keys ∪ Psi'.names ∪
        Term.fv n0 ∪ Basis.fv b0 ∪ Basis.fv b1 ∪
        ValExpr.fv env ∪ ValTy.fv tauv0 ∪ ValTy.fv tauv1)
    have hyL : y ∉ L := fun hm => hy (by simp [hm])
    have hyDeltaKeys : y ∉ Delta'.keys := fun hm => hy (by simp [hm])
    have hyGammaKeys : y ∉ Gamma'.keys := fun hm => hy (by simp [hm])
    have hyPsiNames : y ∉ Psi'.names := fun hm => hy (by simp [hm])
    have hyn0 : y ∉ Term.fv n0 := fun hm => hy (by simp [hm])
    have hyb0 : y ∉ Basis.fv b0 := fun hm => hy (by simp [hm])
    have hyb1 : y ∉ Basis.fv b1 := fun hm => hy (by simp [hm])
    have hyenv : y ∉ ValExpr.fv env := fun hm => hy (by simp [hm])
    have hytauv0 : y ∉ ValTy.fv tauv0 := fun hm => hy (by simp [hm])
    have hytauv1 : y ∉ ValTy.fv tauv1 := fun hm => hy (by simp [hm])
    have hyDelta : y ∉ Delta' :=
      fun hym => hyDeltaKeys (Finmap.mem_keys.mpr hym)
    have hyGamma : y ∉ Gamma' :=
      fun hym => hyGammaKeys (Finmap.mem_keys.mpr hym)
    have hyPsi : forall b, (y, b) ∉ Psi' := by
      intro b hym
      exact hyPsiNames (Finset.mem_image.mpr
        ⟨(y, b), Finmap.mem_keys.mpr hym, rfl⟩)
    have hleOpen : RawCtxIncl ∅
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
    have hleFn : NLCtxIncl Gamma
        (Finmap.insert y (Basis.tof b0) Gamma') :=
      hle.2.insert_right hyGamma (Basis.tof b0)
    have hsubOpen : (Psi.extend y b0 (.var y tauv0)).Subctx
        (Psi'.extend y b0 (.var y tauv0)) := hsub.extend y b0 (.var y tauv0)
    obtain ⟨hbv0, _hbv1, _k0, _k1, _htFrame⟩ := hbv.frame_inv
    have hc' : RawTypedConsistent orc Delta'
        (Finmap.insert y (Basis.tof b0) Gamma')
        (Psi'.extend y b0 (.var y tauv0))
        (Finmap.insert y tauv0 GammaV) (sigma.bind y d)
        (rho.update y w) := by
      exact RawTypedConsistent.worldExtendNLAt
        hspec.toOracleSpec.fvIrrel hc hle.2
        ⟨hyDelta, hyGamma, hyPsi⟩ hbv0 h0.isTyBasis (h0.mono hsub)
        x' w hargDom hdDom
    let opened0 := ihE y hyL hsubOpen
      (Graded.CtxDisj.empty (Finmap.insert y (Basis.tof b0) Gamma))
      (rho.update y w) Delta'
      (Finmap.insert y (Basis.tof b0) Gamma') (sigma.bind y d)
      (Finmap.insert y tauv0 GammaV) hleOpen hc'
    let opened : RawTermTraceAt orc (sigma.bind y d) (rho.update y w)
        (.reshap (ValExpr.openVar y tauv0 env)
          (ValTy.openVar y tauv0 tauv1)
          (ValTy.openVar y tauv0 tauv1))
        (Basis.tof (Basis.openVar y b1))
        (ValTy.openVar y tauv0 tauv1)
        (denotBasis (sigma.bind y d) (Basis.openVar y b1))
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) :=
      ⟨(RawNonBetaValueKernel.holds orc).reshape opened0.dims opened0.dims opened0.result,
        opened0.dims⟩
    obtain ⟨_kind, htOpen⟩ := (he y hyL).ty.tvalid
    have hlcOpen : Ty.lc (Ty.openVar y (Basis.tof b1)) := by
      simpa only [Basis.openVar, Basis.tof_openRec] using
        TValid.lc htOpen.some
    let Bopen := denotBasis (sigma.bind y d) (Basis.openVar y b1)
    obtain ⟨out, hout, hagreeOpen0⟩ := opened.result
    have hagreeOpenStack : RawAgree orc (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1) Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out := by
      apply (RawAgree.lc_irrel_src orc hlcOpen
        (ValTy.openVar y tauv0 tauv1) (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using
        hagreeOpen0
    have hdOpenStack : RawAgreeDimsAt orc (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1) Bopen := by
      apply (RawAgreeDimsAt.lc_irrel_src orc hlcOpen
        (ValTy.openVar y tauv0 tauv1) (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using opened.dims
    have hytof1 : y ∉ Ty.fv (Basis.tof b1) :=
      fun hym => hyb1 (Basis.fv_tof_subset b1 hym)
    have hsourceBridge := RawAgree.openRec_bind_src orc (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1) [d] [] [] 0 Bopen
      (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out hytof1
    simp only [List.getD_cons_zero] at hsourceBridge
    have hagreeSource : RawAgree orc sigma (rho.update y w) [d] [] []
        (Basis.tof b1) (ValTy.openVar y tauv0 tauv1) Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out :=
      hsourceBridge.mp hagreeOpenStack
    have hdSourceBridge := RawAgreeDimsAt.openRec_bind_src orc (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1) [d] [] [] 0 Bopen hytof1
    simp only [List.getD_cons_zero] at hdSourceBridge
    have hdSource : RawAgreeDimsAt orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1) Bopen :=
      hdSourceBridge.mp hdOpenStack
    let Tinner := denotTy (sigma.bind y d) (Basis.tof b0)
    let xInner : Tinner.El :=
      Tinner.extract (denotTerm (sigma.bind y d) (.var y))
    have hytof0 : y ∉ Ty.fv (Basis.tof b0) :=
      fun hym => hyb0 (Basis.fv_tof_subset b0 hym)
    have hT : Tinner = denotTy sigma (Basis.tof b0) := by
      exact denotTy_agree _ (DEnv.AgreeOn.bind_left_of_not_mem hytof0)
    have hmatch : (denotTerm (sigma.bind y d) (.var y)).matchesShape
        Tinner := by
      rw [denotTerm_bind_self sigma y d]
      have hembed : d = Tinner.embed (hT.symm ▸ x') := by
        dsimp only [d]
        exact (htype_embed_cast_raw hT.symm x').symm
      rw [hembed]
      exact HType.embed_matchesShape _ _
    have hembedInner : Tinner.embed xInner =
        denotTerm (sigma.bind y d) (.var y) :=
      HType.embed_extract_of_matchesShape hmatch
    have hxcast : hT ▸ xInner = x' := by
      apply htype_embed_injective_raw (denotTy sigma (Basis.tof b0))
      calc
        (denotTy sigma (Basis.tof b0)).embed (hT ▸ xInner) =
            Tinner.embed xInner := htype_embed_cast_raw hT xInner
        _ = denotTerm (sigma.bind y d) (.var y) := hembedInner
        _ = d := denotTerm_bind_self sigma y d
        _ = (denotTy sigma (Basis.tof b0)).embed x' := rfl
    obtain ⟨htfn⟩ := hasType_mono_nl_raw ht hleFn
    have hfunShape : (denotTerm (sigma.bind y d) n0).matchesShape
        (denotTy (sigma.bind y d) (Basis.tof (.frame b0 b1))) :=
      (soundness htfn hc'.ctxWF_nl hc'.envWF_nl).1
    obtain ⟨g, hpi, _hg⟩ := DVal.matchesShape_sec_eq hfunShape
    have hn0 : denotTerm (sigma.bind y d) n0 = denotTerm sigma n0 :=
      denotTerm_agree n0 (DEnv.AgreeOn.bind_left_of_not_mem hyn0)
    have hsourceOut :
        denotTerm (sigma.bind y d) (.appN n0 (.var y)) =
          (denotTerm sigma n0).applyEl x' := by
      rw [denotTerm_appN_applyEl_raw hpi hmatch]
      change (denotTerm (sigma.bind y d) n0).applyEl xInner = _
      calc
        _ = (denotTerm sigma n0).applyEl xInner :=
          congrArg (fun z => z.applyEl xInner) hn0
        _ = (denotTerm sigma n0).applyEl (hT ▸ xInner) :=
          (dval_applyEl_hcast_raw hT (denotTerm sigma n0) xInner).symm
        _ = (denotTerm sigma n0).applyEl x' :=
          congrArg (denotTerm sigma n0).applyEl hxcast
    have hbasisOut : Bopen =
        (denotBasis sigma (.frame b0 b1)).applyEl x' :=
      (denotBasis_frame_applyEl_openVar y hyb1 x').symm
    have hopenResult : RawResultAgree orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1)
        ((denotBasis sigma (.frame b0 b1)).applyEl x')
        ((denotTerm sigma n0).applyEl x')
        (denotValB_semS orc (rho.update y w) [] []
          (ValExpr.openVar y tauv0 (.reshap env tauv1 tauv1))) := by
      refine ⟨out, ?_, ?_⟩
      · simpa only [ValExpr.openVar, ValExpr.openRec] using hout
      · simpa only [hsourceOut, hbasisOut] using hagreeSource
    have hopenDims : RawAgreeDimsAt orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1)
        ((denotBasis sigma (.frame b0 b1)).applyEl x') := by
      simpa only [hbasisOut] using hdSource
    have hyBody : y ∉ ValExpr.fv (.reshap env tauv1 tauv1) := by
      simp [ValExpr.fv, hyenv, hytauv1]
    have htauv0Lc : ValTy.lc tauv0 :=
      evalT_lc (h0.mono hsub).toEvalT hc.evalCtxLc
    have hopenEnvLc : ValExpr.lc (ValExpr.openVar y tauv0 env) :=
      opStep_lc ((he y hyL).mono hsubOpen).toOpStep hc'.evalCtxLc
    have hopenTauv1Lc : ValTy.lc (ValTy.openVar y tauv0 tauv1) :=
      evalT_lc ((he y hyL).mono hsubOpen).ty.toEvalT hc'.evalCtxLc
    have hopenBodyLc : ValExpr.lc
        (ValExpr.openVar y tauv0 (.reshap env tauv1 tauv1)) := by
      simpa only [ValExpr.openVar, ValExpr.openRec] using
        ValExpr.lc.reshap hopenEnvLc hopenTauv1Lc hopenTauv1Lc
    exact hspec.rawResultBinderCoherent htauv0Lc hopenBodyLc
      hytauv0 hytauv1 hyBody
      hopenDims hopenResult
  exact ⟨hresult, hdFun⟩

end GLang
