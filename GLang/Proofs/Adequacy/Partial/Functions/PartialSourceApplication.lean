import GLang.Proofs.Adequacy.Partial.Source.PartialSourceInferredAgreement
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceInstantiation
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceRepresentation
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialApplicationCompiled

namespace GLang.PartialAdequacy
open Basis (BasisValid)

/-- Application converts the inferred argument and the dependent callback result
between their independently realized types. Adequacy proves both checks succeed. -/
theorem partialAppNVal_result
    {orc : PartialFFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b0 b1 : Basis} {n0 n1 : Term} {env0 env1 : ValExpr}
    {tauv0 tauv1 tauOut : ValTy}
    (hn1Lc : Term.lc n1)
    (hmatch : (denotTerm sigma n1).matchesShape (denotTy sigma (Basis.tof b0)))
    (hpi : exists g : (denotTy sigma (Basis.tof b0)).El -> DVal,
      denotTerm sigma n0 = .pi (denotTy sigma (Basis.tof b0)).El g)
    (hinfer : ValExpr.inferTypeCtx [] env0 = .piTy tauv0 tauv1)
    (function : TermTraceAt orc sigma rho env0
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
      (denotBasis sigma (.frame b0 b1)) (denotTerm sigma n0))
    (argument : TermTraceAt orc sigma rho env1
      (Basis.tof b0) (ValExpr.inferTypeCtx [] env1)
      (denotBasis sigma b0) (denotTerm sigma n1))
    (hsubst : ∀ raw,
      denotValB_partial orc rho [] [] (.reshap env1 tauv0 (ValExpr.inferType env1)) = .ok raw →
      PartialValueSubstitution.RawPresentation orc tauv1
        (ValTy.applyCodomain (.reshap env1 tauv0 (ValExpr.inferType env1)) tauv1)
        ⟨rho,[tauv0],[raw]⟩ ⟨rho,[],[]⟩)
    (hdOut : DimsAt orc sigma rho [] [] []
      (Basis.tof (Basis.instantiate n1 b1)) tauOut
      (denotBasis sigma (Basis.instantiate n1 b1))) :
    TermTraceAt orc sigma rho (.applyAt env0 env1 tauOut)
      (Basis.tof (Basis.instantiate n1 b1)) tauOut
      (denotBasis sigma (Basis.instantiate n1 b1))
      (denotTerm sigma (.appN n0 n1)) := by
  let T0 := denotTy sigma (Basis.tof b0)
  let x' : T0.El := T0.extract (denotTerm sigma n1)
  have hxT : T0.embed x' = denotTerm sigma n1 :=
    HType.embed_extract_of_matchesShape hmatch
  obtain ⟨funValue, hfunEval, hfunAgree⟩ := function.result
  have hdFun := function.dims
  simp only [Basis.tof,DimsAt] at hdFun
  have hd : DimsAt orc sigma rho [] [] [] (Basis.tof b0) tauv0 (denotBasis sigma b0) := by
    simpa only [denotBasis_frame_domainBasis] using hdFun.1
  have hcallback : ∀ raw (arg : tauv0.carrierEl),
      tauv0.carrierFromVal raw = .ok arg →
      Agree orc sigma rho [] [] [] (Basis.tof b0) tauv0 (denotBasis sigma b0)
        (denotTerm sigma n1) raw →
      DimsAt orc sigma rho [] [tauv0] [raw]
        (Basis.tof (Basis.instantiate n1 b1)) tauv1
        (denotBasis sigma (Basis.instantiate n1 b1)) ∧
      ResultAgree orc sigma rho [] [tauv0] [raw]
        (Basis.tof (Basis.instantiate n1 b1)) tauv1
        (denotBasis sigma (Basis.instantiate n1 b1))
        (denotTerm sigma (.appN n0 n1)) (funValue.applyTyped arg) := by
    intro raw arg hto harg
    have harg0 : Agree orc sigma rho [] [] [] (Basis.tof b0) tauv0
        (denotBasis sigma (.frame b0 b1)).domainBasis (T0.embed x') raw := by
      simpa only [hxT, denotBasis_frame_domainBasis] using harg
    simp only [Basis.tof, Agree] at hfunAgree
    obtain ⟨D, hD, f, rfl, hf⟩ := hfunAgree
    obtain ⟨out, hout, houtPush⟩ := hf x' raw arg hto harg0
    have hdCodPush := hdFun.2 x' raw arg hto harg0
    have houtOpen : Agree orc sigma rho [] [tauv0] [raw]
        (Ty.openRec 0 n1 (Basis.tof b1)) tauv1
        ((denotBasis sigma (.frame b0 b1)).applyEl x')
        ((denotTerm sigma n0).applyEl x') out := by
      apply (Agree.instantiate_src hn1Lc (Basis.tof b1) [tauv0] [raw] tauv1
        ((denotBasis sigma (.frame b0 b1)).applyEl x')
        ((denotTerm sigma n0).applyEl x') out).mp
      simpa only [T0, hxT] using houtPush
    have hdOpen : DimsAt orc sigma rho [] [tauv0] [raw]
        (Ty.openRec 0 n1 (Basis.tof b1)) tauv1
        ((denotBasis sigma (.frame b0 b1)).applyEl x') := by
      apply (DimsAt.instantiate_src hn1Lc (Basis.tof b1) [tauv0] [raw] tauv1
        ((denotBasis sigma (.frame b0 b1)).applyEl x')).mp
      simpa only [T0, hxT] using hdCodPush
    obtain ⟨g, hg⟩ := hpi
    have hbasis := denotBasis_frame_applyEl_instantiate
      (sigma := sigma) (n1 := n1) (b0 := b0) (b1 := b1) hn1Lc hmatch
    have hsource := denotTerm_appN_applyEl
      (sigma := sigma) (n0 := n0) (n1 := n1) (T0 := T0) (g := g)
      (by simpa only [T0] using hg) hmatch
    rw [hbasis, ← hsource] at houtOpen
    rw [hbasis] at hdOpen
    refine ⟨?_, out, ?_, ?_⟩
    · simpa only [Basis.instantiate, Basis.tof_openRec] using hdOpen
    · rw [ValValSem.applyTyped_fn, hout]
    · simpa only [Basis.instantiate, Basis.tof_openRec] using houtOpen
  exact ⟨applyAt_agree hinfer hfunEval hd argument hdOut hcallback hsubst,hdOut⟩

theorem arm_appN_val
    (hirr : PartialDirectFv.OracleFresh PartialDirectOracle.oracle)
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
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi
      (Basis.instantiate n1 b1) tauOut)
    (ih0 : MTermSubctx PartialDirectOracle.oracle ∅ Gamma Psi n0
      (.frame b0 b1) env0 (.piTy tauFun0 tauFun1))
    (ih1 : MTermSubctx PartialDirectOracle.oracle ∅ Gamma Psi n1
      b0 env1 tauArg)
    (ih1Dof : MDofSubctx PartialDirectOracle.oracle Gamma Psi env1 tauArg) :
    MTermSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.appN n0 n1)
      (Basis.instantiate n1 b1) (.applyAt env0 env1 tauOut) tauOut := by
  intro Psi' hsub _hdisj rho Delta' Gamma' sigma GammaV hle hc
  let function := ih0 hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  let argument := ih1 hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : DimsAt PartialDirectOracle.oracle sigma rho [] [] []
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
  have function' := TermTraceAt.inferred (h0.mono hsub) hc.history hirr function
    (by intro sv hs; cases hs)
  have argument' := TermTraceAt.inferred (h1.mono hsub) hc.history hirr argument
    (fun sv hs => ih1Dof hs hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have hshape := inferType_sameShape (h0.mono hsub) hc.history
  cases hf : ValExpr.inferTypeCtx [] env0 with
  | space sv => simp only [hf, ValSoundOfDenot.ValTy.SameShape] at hshape
  | piTy d c =>
    rw [hf] at function'
    refine partialAppNVal_result h1.hasType.some.lc hmatch ⟨g, hpi⟩
      hf function' argument' ?_ targetDims
    intro raw hu
    have hv := hc.context.evalContext.valid.some
    have hfun := (RuntimeValue.preservation_mutual.2.2.2
      (h0.mono hsub).toOpStep GammaV hc.context.evalContext).at
        (show ValExpr.inferType env0 = .piTy d c by simpa only [ValExpr.inferTypeCtx_nil] using hf)
    have harg := (RuntimeValue.preservation_mutual.2.2.2
      (h1.mono hsub).toOpStep GammaV hc.context.evalContext).some
    have hfk := RuntimeValue.operational_kind_of_context
      (h0.mono hsub).toOpStep hc.context.evalContext.regular
    have hak := RuntimeValue.operational_kind_of_context
      (h1.mono hsub).toOpStep hc.context.evalContext.regular
    have hf' : ValExpr.inferType env0 = .piTy d c := by
      simpa only [ValExpr.inferTypeCtx_nil] using hf
    simp only [hf',ValTy.structuralKind,Basis.tof,Ty.sourceKind,ValKind.arrow.injEq] at hfk
    exact application_substitution hv hfun harg (hak.trans hfk.1.symm) rho raw hu

end GLang.PartialAdequacy
