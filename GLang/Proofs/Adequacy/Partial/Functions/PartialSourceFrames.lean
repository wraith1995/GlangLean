import GLang.Proofs.Adequacy.Partial.Functions.PartialSourceAbstraction
import GLang.Proofs.Adequacy.Partial.Functions.PartialSourceApplication

namespace GLang.PartialAdequacy
open Basis (BasisValid)

theorem arm_frame_reanchor
    (hirr : PartialDirectFv.OracleFresh PartialDirectOracle.oracle)
    (hpush : PartialDirectOpenPush.OracleOpenPush PartialDirectOracle.oracle)
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
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi (.frame b0 b1)
      (.piTy tauv0 tauv1'))
    (_ih0 : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi b0 tauv0)
    (ihFn : MTermSubctx PartialDirectOracle.oracle ∅ Gamma Psi n0
      (.frame b0' b1) leev (.piTy tauv0' tauv1))
    (_ihDom : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi b0' tauv0')
    (ihX : forall y, y ∉ L ->
      MTermSubctx PartialDirectOracle.oracle ∅
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (.var y) b0' (ValExpr.openVar y tauv0 env1) tauv0')
    (ihCod : forall y, y ∉ L ->
      MTyAtSubctx PartialDirectOracle.oracle
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1) (ValTy.openVar y tauv0 tauv1')) :
    MTermSubctx PartialDirectOracle.oracle ∅ Gamma Psi n0 (.frame b0 b1)
      (.vlam tauv0 tauv1'
        (.reshap
          (.applyValue leev (.reshap env1 tauv0' tauv0'))
          tauv1' tauv1'))
      (.piTy tauv0 tauv1') := by
  intro Psi' hsub _hdisj rho Delta' Gamma' sigma GammaV hle hc
  have hdFun : DimsAt PartialDirectOracle.oracle sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1')
      (denotBasis sigma (.frame b0 b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hresult : ResultAgree PartialDirectOracle.oracle sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1')
      (denotBasis sigma (.frame b0 b1)) (denotTerm sigma n0)
      (denotValB_partial PartialDirectOracle.oracle rho [] []
        (.vlam tauv0 tauv1'
          (.reshap
            (.applyValue leev (.reshap env1 tauv0' tauv0'))
            tauv1' tauv1'))) := by
    apply lambda_result hdFun
    intro x' arg harg
    let d := (denotTy sigma (Basis.tof b0)).embed x'
    let w := tauv0.carrierToVal arg
    have hdPi := hdFun
    simp only [Basis.tof, DimsAt] at hdPi
    have hdDom : DimsAt PartialDirectOracle.oracle sigma rho [] [] []
        (Basis.tof b0) tauv0 (denotBasis sigma b0) := by
      simpa only [denotBasis_frame_domainBasis] using hdPi.1
    have hargDom : Agree PartialDirectOracle.oracle sigma rho [] [] []
        (Basis.tof b0) tauv0 (denotBasis sigma b0) d w := by
      simpa only [denotBasis_frame_domainBasis, d, w] using harg
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
      (L ∪ Delta'.keys ∪ Gamma'.keys ∪ Psi'.keyNames ∪
        Term.fv n0 ∪ Basis.fv b0 ∪ Basis.fv b0' ∪ Basis.fv b1 ∪
        ValExpr.fv leev ∪ ValExpr.fv env1 ∪
        ValTy.fv tauv0 ∪ ValTy.fv tauv0' ∪
        ValTy.fv tauv1 ∪ ValTy.fv tauv1')
    have hyL : y ∉ L := fun hm => hy (by simp [hm])
    have hyDeltaKeys : y ∉ Delta'.keys := fun hm => hy (by simp [hm])
    have hyGammaKeys : y ∉ Gamma'.keys := fun hm => hy (by simp [hm])
    have hyPsiNames : y ∉ Psi'.keyNames := fun hm => hy (by simp [hm])
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
    have hc' : TypedHistory PartialDirectOracle.oracle Delta'
        (Finmap.insert y (Basis.tof b0) Gamma')
        (Psi'.extend y b0 (.var y tauv0))
        (Finmap.insert y tauv0 GammaV) (sigma.bind y d)
        (rho.update y w) := by
      exact TypedHistory.worldExtendNLAt
        hirr hc hle.2
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
    let converted : TermTraceAt PartialDirectOracle.oracle (sigma.bind y d) (rho.update y w)
        (.reshap (ValExpr.openVar y tauv0 env1) tauv0' tauv0')
        (Basis.tof b0') tauv0' (denotBasis (sigma.bind y d) b0')
        (denotTerm (sigma.bind y d) (.var y)) :=
      reshape_compiled ((hx y hyL).mono hsubOpen) hc'.history hirr converted0.dims converted0
    have targetDims0 := ihCod y hyL hsubOpen
      (rho.update y w) Delta'
      (Finmap.insert y (Basis.tof b0) Gamma') (sigma.bind y d)
      (Finmap.insert y tauv0 GammaV) hleOpen.2 hc'
    have targetDims : DimsAt PartialDirectOracle.oracle (sigma.bind y d)
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
    have function' := TermTraceAt.inferred hfnCurrent hc'.history hirr function
      (by intro sv hs; cases hs)
    have applied : TermTraceAt PartialDirectOracle.oracle (sigma.bind y d) (rho.update y w)
        (.applyAt leev (.reshap (ValExpr.openVar y tauv0 env1) tauv0' tauv0')
          (ValTy.openVar y tauv0 tauv1'))
        (Basis.tof (Basis.instantiate (.var y) b1)) (ValTy.openVar y tauv0 tauv1')
        (denotBasis (sigma.bind y d) (Basis.instantiate (.var y) b1))
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) := by
      have hshape := inferType_sameShape hfnCurrent hc'.history
      cases hf : ValExpr.inferTypeCtx [] leev with
      | space sv => simp only [hf, ValSoundOfDenot.ValTy.SameShape] at hshape
      | piTy dom cod =>
        rw [hf] at function'
        refine partialAppNVal_result Term.lc.var hmatch ⟨g, hpi⟩
          hf function' converted ?_ targetDims
        intro raw hu
        have hv := hc'.context.evalContext.valid.some
        have hfun := (RuntimeValue.preservation_mutual.2.2.2 hfnCurrent.toOpStep
          _ hc'.context.evalContext).at
          (show ValExpr.inferType leev = .piTy dom cod by
            simpa only [ValExpr.inferTypeCtx_nil] using hf)
        have harg := (RuntimeValue.preservation_mutual.2.2.2 hxCurrent.toOpStep
          _ hc'.context.evalContext).some
        have ht := (RuntimeValue.preservation_mutual.2.1
          (hdom.mono hsubFn).toEvalT _ hc'.context.evalContext).some
        have hfk := RuntimeValue.operational_kind_of_context hfnCurrent.toOpStep
          hc'.context.evalContext.regular
        have hf' : ValExpr.inferType leev = .piTy dom cod := by
          simpa only [ValExpr.inferTypeCtx_nil] using hf
        simp only [hf',ValTy.structuralKind,Basis.tof,Ty.sourceKind,ValKind.arrow.injEq] at hfk
        have hdk := (hdom.mono hsubFn).toEvalT.structuralKind_eq_sourceKind
        exact application_substitution hv hfun (.reshap harg ht ht)
          (by simpa only [ValExpr.inferType_reshap] using hdk.trans hfk.1.symm) _ raw hu
    let opened : TermTraceAt PartialDirectOracle.oracle (sigma.bind y d) (rho.update y w)
        (.reshap
          (.applyValue leev (.reshap (ValExpr.openVar y tauv0 env1) tauv0' tauv0'))
          (ValTy.openVar y tauv0 tauv1')
          (ValTy.openVar y tauv0 tauv1'))
        (Basis.tof (Basis.openVar y b1))
        (ValTy.openVar y tauv0 tauv1')
        (denotBasis (sigma.bind y d) (Basis.openVar y b1))
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) := by
      obtain ⟨r,hr,ha⟩ := applied.result
      refine ⟨⟨r,reshape_self_of_inferred hr,?_⟩,?_⟩
      · simpa only [Basis.instantiate] using ha
      · simpa only [Basis.instantiate] using applied.dims
    obtain ⟨_kind, htOpen⟩ := hcodCurrent.toTy.tvalid
    have hlcOpen : Ty.lc (Ty.openVar y (Basis.tof b1)) := by
      simpa only [Basis.openVar, Basis.tof_openRec] using
        TValid.lc htOpen.some
    let Bopen := denotBasis (sigma.bind y d) (Basis.openVar y b1)
    obtain ⟨out, hout, hagreeOpen0⟩ := opened.result
    have hagreeOpenStack : Agree PartialDirectOracle.oracle (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1') Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out := by
      apply (Agree.lc_irrel_src PartialDirectOracle.oracle hlcOpen
        (ValTy.openVar y tauv0 tauv1') (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using
        hagreeOpen0
    have hdOpenStack : DimsAt PartialDirectOracle.oracle (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1') Bopen := by
      apply (DimsAt.lc_irrel_src PartialDirectOracle.oracle hlcOpen
        (ValTy.openVar y tauv0 tauv1') (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using opened.dims
    have hytof1 : y ∉ Ty.fv (Basis.tof b1) :=
      fun hym => hyb1 (Basis.fv_tof_subset b1 hym)
    have hsourceBridge := Agree.openRec_bind_src PartialDirectOracle.oracle (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1') [d] [] [] 0 Bopen
      (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out hytof1
    simp only [List.getD_cons_zero] at hsourceBridge
    have hagreeSource : Agree PartialDirectOracle.oracle sigma (rho.update y w) [d] [] []
        (Basis.tof b1) (ValTy.openVar y tauv0 tauv1') Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out :=
      hsourceBridge.mp hagreeOpenStack
    have hdSourceBridge := DimsAt.openRec_bind_src PartialDirectOracle.oracle (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1') [d] [] [] 0 Bopen hytof1
    simp only [List.getD_cons_zero] at hdSourceBridge
    have hdSource : DimsAt PartialDirectOracle.oracle sigma (rho.update y w)
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
    have hxcast : (hT ▸ xInner : (denotTy sigma (Basis.tof b0)).El) = x' := by
      apply htype_embed_injective_raw (denotTy sigma (Basis.tof b0))
      calc
        (denotTy sigma (Basis.tof b0)).embed ((hT ▸ xInner : (denotTy sigma (Basis.tof b0)).El)) =
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
        _ = (denotTerm sigma n0).applyEl ((hT ▸ xInner : (denotTy sigma (Basis.tof b0)).El)) :=
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
          (.applyValue leev (.reshap (ValExpr.openVar y tauv0 env1) tauv0' tauv0'))
          (ValTy.openVar y tauv0 tauv1')
          (ValTy.openVar y tauv0 tauv1') := by
      simp only [ValExpr.openVar, ValExpr.applyValue, ValExpr.openRec, ValExpr.inferType,
        ValExpr.openRec_lc hleevLc 0 (.var y tauv0),
        ValTy.openRec_lc htauv0'Lc 0 (.var y tauv0),
        ValTy.openRec_lc hleevLc.inferType.domain 0 (.var y tauv0)]
    have hopenResult : ResultAgree PartialDirectOracle.oracle sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1')
        ((denotBasis sigma (.frame b0 b1)).applyEl x')
        ((denotTerm sigma n0).applyEl x')
        (denotValB_partial PartialDirectOracle.oracle (rho.update y w) [] []
          (ValExpr.openVar y tauv0
            (.reshap
              (.applyValue leev (.reshap env1 tauv0' tauv0'))
              tauv1' tauv1'))) := by
      refine ⟨out, ?_, ?_⟩
      · rw [hopenValue]
        exact hout
      · simpa only [hsourceOut, hbasisOut] using hagreeSource
    have hopenDims : DimsAt PartialDirectOracle.oracle sigma (rho.update y w)
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
    exact ResultAgree.valueOpenPush (G := []) (D := []) hpush htauv0Lc
      hytauv0 (by intro t ht; cases ht) rfl hytauv1' hyBody
      hopenDims hopenResult
  exact ⟨hresult, hdFun⟩

theorem arm_frame_eta
    {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    (hpush : PartialDirectOpenPush.OracleOpenPush orc)
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
    (ihTy : MTyAtSubctx orc Gamma Psi (.frame b0 b1)
      (.piTy tauv0 tauv1))
    (_ih0 : MTyAtSubctx orc Gamma Psi b0 tauv0)
    (ihE : forall y, y ∉ L ->
      MTermSubctx orc ∅
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (.appN n0 (.var y)) (Basis.openVar y b1)
        (ValExpr.openVar y tauv0 env) (ValTy.openVar y tauv0 tauv1))
    (_ih1 : forall y, y ∉ L ->
      MTyAtSubctx orc
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1) (ValTy.openVar y tauv0 tauv1)) :
    MTermSubctx orc ∅ Gamma Psi n0 (.frame b0 b1)
      (.vlam tauv0 tauv1 (.reshap env tauv1 tauv1))
      (.piTy tauv0 tauv1) := by
  intro Psi' hsub _hdisj rho Delta' Gamma' sigma GammaV hle hc
  have hdFun : DimsAt orc sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
      (denotBasis sigma (.frame b0 b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hresult : ResultAgree orc sigma rho [] [] []
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
      (denotBasis sigma (.frame b0 b1)) (denotTerm sigma n0)
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
        Term.fv n0 ∪ Basis.fv b0 ∪ Basis.fv b1 ∪
        ValExpr.fv env ∪ ValTy.fv tauv0 ∪ ValTy.fv tauv1)
    have hyL : y ∉ L := fun hm => hy (by simp [hm])
    have hyDeltaKeys : y ∉ Delta'.keys := fun hm => hy (by simp [hm])
    have hyGammaKeys : y ∉ Gamma'.keys := fun hm => hy (by simp [hm])
    have hyPsiNames : y ∉ Psi'.keyNames := fun hm => hy (by simp [hm])
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
    have hc' : TypedHistory orc Delta'
        (Finmap.insert y (Basis.tof b0) Gamma')
        (Psi'.extend y b0 (.var y tauv0))
        (Finmap.insert y tauv0 GammaV) (sigma.bind y d)
        (rho.update y w) := by
      exact TypedHistory.worldExtendNLAt
        hirr hc hle.2
        ⟨hyDelta, hyGamma, hyPsi⟩ hbv0 h0.isTyBasis (h0.mono hsub)
        x' w hargDom hdDom
    let opened0 := ihE y hyL hsubOpen
      (Graded.CtxDisj.empty (Finmap.insert y (Basis.tof b0) Gamma))
      (rho.update y w) Delta'
      (Finmap.insert y (Basis.tof b0) Gamma') (sigma.bind y d)
      (Finmap.insert y tauv0 GammaV) hleOpen hc'
    let opened : TermTraceAt orc (sigma.bind y d) (rho.update y w)
        (.reshap (ValExpr.openVar y tauv0 env)
          (ValTy.openVar y tauv0 tauv1)
          (ValTy.openVar y tauv0 tauv1))
        (Basis.tof (Basis.openVar y b1))
        (ValTy.openVar y tauv0 tauv1)
        (denotBasis (sigma.bind y d) (Basis.openVar y b1))
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) :=
      reshape_compiled ((he y hyL).mono (hsub.extend y b0 (.var y tauv0))) hc'.history hirr opened0.dims opened0
    obtain ⟨_kind, htOpen⟩ := (he y hyL).ty.tvalid
    have hlcOpen : Ty.lc (Ty.openVar y (Basis.tof b1)) := by
      simpa only [Basis.openVar, Basis.tof_openRec] using
        TValid.lc htOpen.some
    let Bopen := denotBasis (sigma.bind y d) (Basis.openVar y b1)
    obtain ⟨out, hout, hagreeOpen0⟩ := opened.result
    have hagreeOpenStack : Agree orc (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1) Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out := by
      apply (Agree.lc_irrel_src orc hlcOpen
        (ValTy.openVar y tauv0 tauv1) (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using
        hagreeOpen0
    have hdOpenStack : DimsAt orc (sigma.bind y d)
        (rho.update y w) [d] [] []
        (Ty.openVar y (Basis.tof b1))
        (ValTy.openVar y tauv0 tauv1) Bopen := by
      apply (DimsAt.lc_irrel_src orc hlcOpen
        (ValTy.openVar y tauv0 tauv1) (sigma.bind y d)
        (rho.update y w) [] [d] [] [] Bopen).mp
      simpa only [Basis.openVar, Basis.tof_openRec, Bopen] using opened.dims
    have hytof1 : y ∉ Ty.fv (Basis.tof b1) :=
      fun hym => hyb1 (Basis.fv_tof_subset b1 hym)
    have hsourceBridge := Agree.openRec_bind_src orc (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1) [d] [] [] 0 Bopen
      (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out hytof1
    simp only [List.getD_cons_zero] at hsourceBridge
    have hagreeSource : Agree orc sigma (rho.update y w) [d] [] []
        (Basis.tof b1) (ValTy.openVar y tauv0 tauv1) Bopen
        (denotTerm (sigma.bind y d) (.appN n0 (.var y))) out :=
      hsourceBridge.mp hagreeOpenStack
    have hdSourceBridge := DimsAt.openRec_bind_src orc (z := y)
      sigma (rho.update y w) (Basis.tof b1)
      (ValTy.openVar y tauv0 tauv1) [d] [] [] 0 Bopen hytof1
    simp only [List.getD_cons_zero] at hdSourceBridge
    have hdSource : DimsAt orc sigma (rho.update y w)
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
    have hxcast : (hT ▸ xInner : (denotTy sigma (Basis.tof b0)).El) = x' := by
      apply htype_embed_injective_raw (denotTy sigma (Basis.tof b0))
      calc
        (denotTy sigma (Basis.tof b0)).embed ((hT ▸ xInner : (denotTy sigma (Basis.tof b0)).El)) =
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
        _ = (denotTerm sigma n0).applyEl ((hT ▸ xInner : (denotTy sigma (Basis.tof b0)).El)) :=
          (dval_applyEl_hcast_raw hT (denotTerm sigma n0) xInner).symm
        _ = (denotTerm sigma n0).applyEl x' :=
          congrArg (denotTerm sigma n0).applyEl hxcast
    have hbasisOut : Bopen =
        (denotBasis sigma (.frame b0 b1)).applyEl x' :=
      (denotBasis_frame_applyEl_openVar y hyb1 x').symm
    have hopenResult : ResultAgree orc sigma (rho.update y w)
        [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1)
        ((denotBasis sigma (.frame b0 b1)).applyEl x')
        ((denotTerm sigma n0).applyEl x')
        (denotValB_partial orc (rho.update y w) [] []
          (ValExpr.openVar y tauv0 (.reshap env tauv1 tauv1))) := by
      refine ⟨out, ?_, ?_⟩
      · simpa only [ValExpr.openVar, ValExpr.openRec] using hout
      · simpa only [hsourceOut, hbasisOut] using hagreeSource
    have hopenDims : DimsAt orc sigma (rho.update y w)
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
    exact ResultAgree.valueOpenPush (G := []) (D := []) hpush htauv0Lc
      hytauv0 (by intro t ht; cases ht) rfl hytauv1 hyBody
      hopenDims hopenResult
  exact ⟨hresult, hdFun⟩

end GLang.PartialAdequacy
