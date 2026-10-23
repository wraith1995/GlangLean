import GLang.Proofs.Value.Runtime.RuntimeValueTotalSemanticSubstitution
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyBasic

set_option maxHeartbeats 1800000
namespace GLang

theorem raw_inferType_pi_dims
    {DeltaS : LCtx} {GammaS : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauv0 tauv1 : ValTy}
    (h : S.Term DeltaS GammaS Psi e b v (.piTy tauv0 tauv1))
    {orc : FFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (hc : RawConsistent orc DeltaC GammaC Psi GammaV sigma rho)
    (hirr : OracleFvIrrel orc)
    {t0 t1 : Ty} (ht : Basis.tof b = .piTy t0 t1)
    (hdims : RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b)
      (.piTy tauv0 tauv1) (denotBasis sigma b)) :
    RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b) (ValExpr.inferTypeCtx [] v)
      (denotBasis sigma b) := by
  refine S.Term.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ Psi _ b v tauv _ =>
      forall {dom cod : ValTy}, tauv = .piTy dom cod ->
      forall {orc : FFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
        {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem},
        RawConsistent orc DeltaC GammaC Psi GammaV sigma rho ->
        OracleFvIrrel orc →
        forall {t0 t1 : Ty}, Basis.tof b = .piTy t0 t1 →
        RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b)
          (.piTy dom cod) (denotBasis sigma b) →
        RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b) (ValExpr.inferTypeCtx [] v)
          (denotBasis sigma b))
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
    ?termZero ?termRlit h rfl hc hirr ht hdims
  case termVarLin =>
    intro Gamma Psi x b v s tauv hlookup _htof _hbv htauv _ihtauv
      dom cod htauvPi orc DeltaC GammaC GammaV sigma rho hc hirr t0 t1 ht hdims
    obtain ⟨vStored,tauStored,xs,yV,Gamma0,Psi0,hPsi,_,_,_,_,_,_,_,hdimsStored,hinfer⟩ :=
      hc.stored_raw_current_infer hirr (Finmap.mem_of_lookup_eq_some hlookup)
    have hv : vStored = v := Option.some.inj (hPsi.symm.trans hlookup)
    subst vStored
    rw [hinfer]
    exact hdimsStored
  case termVarNlin =>
    intro Gamma Psi x b v tauv hlookup _hGamma _hbv htauv _ihtauv
      dom cod htauvPi orc DeltaC GammaC GammaV sigma rho hc hirr t0 t1 ht hdims
    obtain ⟨vStored,tauStored,xs,yV,Gamma0,Psi0,hPsi,_,_,_,_,_,_,_,hdimsStored,hinfer⟩ :=
      hc.stored_raw_current_infer hirr (Finmap.mem_of_lookup_eq_some hlookup)
    have hv : vStored = v := Option.some.inj (hPsi.symm.trans hlookup)
    subst vStored
    rw [hinfer]
    exact hdimsStored
  all_goals
    simp only [ValExpr.applyAt, ValExpr.inferTypeCtx,reduceCtorEq,forall_const,false_implies,ValTy.domain_piTy]
  all_goals intros
  all_goals try trivial
  case termPromote => solve_by_elim (maxDepth := 8)
  all_goals
    rename_i dom cod hpi orc DC GC GV sig rh hc hf t0 t1 htof hd
    simpa only [hpi] using hd

/-- Inference retains the realized source kind even when its annotation differs. -/
theorem raw_inferType_sameShape
    {Δ Γ Ψ e b v tv} (h : S.Term Δ Γ Ψ e b v tv)
    {orc : FFSOracleSem} {Δc Γc Γv σ ρ}
    (hc : RawConsistent orc Δc Γc Ψ Γv σ ρ) :
    ValSoundOfDenot.ValTy.SameShape (ValExpr.inferTypeCtx [] v) tv := by
  have hp := V2.preservation_master.2.2.2 h.toOpStep Δ Γ Ψ.keyNames
    hc.evalCtxValidPlus hc.evalCtxValidPlus.rhoValid_keyNames (Finset.Subset.refl _)
    h.hasType.some h.tyAt.basisValid.sof_valid.some
  obtain ⟨⟨tv', heval, k, hi, ht⟩, _, _⟩ := hp
  rw [inferTypeCtx_of_lc [] (opStep_lc h.toOpStep hc.evalCtxLc)]
  have hshape := valTValidC_sameShape_of_sameKind k hi.some ht.some
  have heq := heval.structuralKind_determined h.toEvalT
  exact hshape.trans (valTValidC_sameShape_of_sameKind k ht.some
    (by
      have hk : k = tv.structuralKind := (ValTValidC.kind_eq_structural ht.some).trans heq
      rw [hk]
      exact (evalT_valid h.toEvalT).some))

/-- A base-space producer also has a base-space inferred type. -/
theorem raw_inferType_isSpace
    {Δ Γ Ψ e b v sv} (h : S.Term Δ Γ Ψ e b v (.space sv))
    {orc : FFSOracleSem} {Δc Γc Γv σ ρ}
    (hc : RawConsistent orc Δc Γc Ψ Γv σ ρ) :
    ∃ s, ValExpr.inferTypeCtx [] v = .space s := by
  have hs := raw_inferType_sameShape h hc
  cases hi : ValExpr.inferTypeCtx [] v with
  | space s => exact ⟨s, rfl⟩
  | piTy d c => simp only [hi, ValSoundOfDenot.ValTy.SameShape] at hs

/-- Operational producers agree on their inferred type and array-space view. -/
theorem raw_inferType_spaceOf_eq
    {Δ Γ Ψ e b v tv} (h : S.Term Δ Γ Ψ e b v tv)
    {orc : FFSOracleSem} {Δc Γc Γv σ ρ}
    (hc : RawConsistent orc Δc Γc Ψ Γv σ ρ) :
    ∀ s, ValExpr.inferTypeCtx [] v = .space s → ValExpr.inferSpaceCtx [] v = s := by
  refine S.Term.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ Ψ _ _ v _ _ =>
      ∀ {orc : FFSOracleSem} {Δc Γc Γv σ ρ}, RawConsistent orc Δc Γc Ψ Γv σ ρ →
        ∀ s, ValExpr.inferTypeCtx [] v = .space s → ValExpr.inferSpaceCtx [] v = s)
    ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
    ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
    ?tySpace ?tyPi ?tyAtSpace ?tyAtFrame
    ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
    ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
    ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
    ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
    ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
    ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
    ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
    ?termAppL ?termAppI ?termNllam ?termAppNVal
    ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
    ?termZero ?termRlit h hc
  case termVarLin =>
    intro Γ Ψ x b v sp tv hl _ _ _ _ orc Δc Γc Γv σ ρ hc s hi
    obtain ⟨v',tv',_,_,_,_,_,_,_,_,hs,_,heq,_,_⟩ :=
      hc.lookup (Finmap.mem_of_lookup_eq_some hl)
    have hv : v' = v := Option.some.inj (heq.symm.trans hl)
    subst v'
    have htv : tv' = .space s := by
      rw [inferTypeCtx_of_lc [] hs.hlc, hs.hinfer] at hi
      exact hi
    exact (htv ▸ hs.hinferSpaceBase).spaceEq
  case termVarNlin =>
    intro Γ Ψ x b v tv hl _ _ _ _ orc Δc Γc Γv σ ρ hc s hi
    obtain ⟨v',tv',_,_,_,_,_,_,_,_,hs,_,heq,_,_⟩ :=
      hc.lookup (Finmap.mem_of_lookup_eq_some hl)
    have hv : v' = v := Option.some.inj (heq.symm.trans hl)
    subst v'
    have htv : tv' = .space s := by
      rw [inferTypeCtx_of_lc [] hs.hlc, hs.hinfer] at hi
      exact hi
    exact (htv ▸ hs.hinferSpaceBase).spaceEq
  case termDsum =>
    intro Delta Gamma Psi e0 e1 b0 b1 v0 v1 sv0 sv1 htof0 htof1 ht hbv hTy he0 he1 ihTy ih0 ih1
      orc DC GC GV sig rh hc s hi
    obtain ⟨s0, h0⟩ := raw_inferType_isSpace he0 hc
    obtain ⟨s1, h1⟩ := raw_inferType_isSpace he1 hc
    simpa only [ValExpr.inferSpaceCtx, ih0 hc s0 h0, ih1 hc s1 h1] using
      (by simpa only [ValExpr.inferTypeCtx, h0, h1, ValTy.spaceOf, ValTy.space.injEq] using hi : s0.dsum s1 = s)
  case termTprod =>
    intro Delta0 Delta1 Gamma Psi e0 e1 b0 b1 v0 v1 sv0 sv1 hdisj htof0 htof1 ht hbv hTy he0 he1 ihTy ih0 ih1
      orc DC GC GV sig rh hc s hi
    obtain ⟨s0, h0⟩ := raw_inferType_isSpace he0 hc
    obtain ⟨s1, h1⟩ := raw_inferType_isSpace he1 hc
    simpa only [ValExpr.inferSpaceCtx, ih0 hc s0 h0, ih1 hc s1 h1] using
      (by simpa only [ValExpr.inferTypeCtx, h0, h1, ValTy.spaceOf, ValTy.space.injEq] using hi : s0.tprod s1 = s)
  case termPinvTStd =>
    intro Gamma Psi b0 b1 e v sv0 sv1 hb0 hb1 ht hbv hTy he ihTy ihE
      orc DC GC GV sig rh hc s hi
    obtain ⟨sv, hv⟩ := raw_inferType_isSpace he hc
    have hs := ihE hc sv hv
    cases sv <;> simpa [ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, hv, hs] using hi
  case termPinvTGpinv =>
    intro Gamma Psi b0 b1 e v env0 env1 sv0 sv1 ht hbv hTy he hi0 hi1 ihTy ihE ihI0 ihI1
      orc DC GC GV sig rh hc s hi
    obtain ⟨sv, hv⟩ := raw_inferType_isSpace he hc
    have hs := ihE hc sv hv
    cases sv <;> simpa [ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, hv, hs] using hi
  case termEmbedKer | termEmbedCoker | termEmbedImg | termEmbedCoimg =>
    intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv hTy hi0 hi1 he ihTy ihI0 ihI1 ihE
      orc DC GC GV sig rh hc s hi
    obtain ⟨sv, hv⟩ := raw_inferType_isSpace he hc
    have hs := ihE hc sv hv
    cases sv <;> simpa [ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, hv, hs] using hi
  all_goals intros
  all_goals try dsimp only at *
  all_goals intros
  all_goals simp_all [ValExpr.applyAt, ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, ValExpr.reshapBase,
    ValExpr.sumAt, ValTy.spaceOf]
  all_goals solve_by_elim (maxDepth := 8)
/-- The array-shape companion and inferred Pi realization together recover
agreement at the complete inferred value type. -/
theorem raw_inferType_dims
    {Δ Γ Ψ e b v tv} (h : S.Term Δ Γ Ψ e b v tv)
    {orc : FFSOracleSem} {Δc Γc Γv σ ρ}
    (hc : RawConsistent orc Δc Γc Ψ Γv σ ρ) (hirr : OracleFvIrrel orc)
    (hd : RawAgreeDimsAt orc σ ρ [] [] [] (Basis.tof b) tv (denotBasis σ b))
    (hm : ∀ sv, tv = .space sv →
      ValSpace.shpOf (orc ρ [] []) (ValExpr.inferSpaceCtx [] v) =
        ValSpace.shpOf (orc ρ [] []) sv) :
    RawAgreeDimsAt orc σ ρ [] [] [] (Basis.tof b) (ValExpr.inferTypeCtx [] v) (denotBasis σ b) := by
  have hs := raw_inferType_sameShape h hc
  cases tv with
  | space sv =>
    cases hi : ValExpr.inferTypeCtx [] v with
    | piTy d c => simp only [hi,ValSoundOfDenot.ValTy.SameShape] at hs
    | space s =>
      have he := raw_inferType_spaceOf_eq h hc s hi
      have hm' := hm sv rfl
      rw [he] at hm'
      cases ht : Basis.tof b with
      | piTy d c => simp only [ht,RawAgreeDimsAt] at hd
      | space src => simpa only [ht,RawAgreeDimsAt,hm'] using hd
  | piTy d c =>
    cases ht : Basis.tof b with
    | space src => simp only [ht,RawAgreeDimsAt] at hd
    | piTy sd sc => simpa only [ht] using raw_inferType_pi_dims h hc hirr ht hd

/-- Retagging a successful trace by inference changes no runtime value. -/
theorem RawTermTraceAt.inferred
    {Δ Γ Ψ e b v tv} (h : S.Term Δ Γ Ψ e b v tv)
    {orc : FFSOracleSem} {Δc Γc Γv σ ρ}
    (hc : RawConsistent orc Δc Γc Ψ Γv σ ρ) (hirr : OracleFvIrrel orc)
    (hv : RawTermTraceAt orc σ ρ v (Basis.tof b) tv (denotBasis σ b) (denotTerm σ e))
    (hm : ∀ sv, tv = .space sv →
      ValSpace.shpOf (orc ρ [] []) (ValExpr.inferSpaceCtx [] v) =
        ValSpace.shpOf (orc ρ [] []) sv) :
    RawTermTraceAt orc σ ρ v (Basis.tof b) (ValExpr.inferTypeCtx [] v)
      (denotBasis σ b) (denotTerm σ e) := by
  have hd := raw_inferType_dims h hc hirr hv.dims hm
  obtain ⟨r,hr,ha⟩ := hv.result
  exact ⟨⟨r,hr,RawAgree.realize_transport orc σ ρ (raw_inferType_sameShape h hc).symm hv.dims hd ha⟩,hd⟩

/-- Argument conversion is explicit; the binary application retains its native
result and its inferred dependent codomain. -/
theorem rawApplyValue_result
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b0 b1 : Basis} {n0 n1 : Term} {f a : ValExpr} {d c out : ValTy}
    (hn : Term.lc n1)
    (hm : (denotTerm sigma n1).matchesShape (denotTy sigma (Basis.tof b0)))
    (hp : ∃ g : (denotTy sigma (Basis.tof b0)).El → DVal,
      denotTerm sigma n0 = .pi (denotTy sigma (Basis.tof b0)).El g)
    (hi : ValExpr.inferTypeCtx [] f = .piTy d c)
    (hshape : ValSoundOfDenot.ValTy.SameShape c out)
    (hf : RawTermTraceAt orc sigma rho f (Basis.tof (.frame b0 b1))
      (.piTy d c) (denotBasis sigma (.frame b0 b1)) (denotTerm sigma n0))
    (ha : RawTermTraceAt orc sigma rho a (Basis.tof b0) (ValExpr.inferTypeCtx [] a)
      (denotBasis sigma b0) (denotTerm sigma n1))
    (ho : RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof (Basis.instantiate n1 b1))
      out (denotBasis sigma (Basis.instantiate n1 b1))) :
    RawTermTraceAt orc sigma rho (.applyValue f a) (Basis.tof (Basis.instantiate n1 b1))
      out (denotBasis sigma (Basis.instantiate n1 b1)) (denotTerm sigma (.appN n0 n1)) := by
  have hd : RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b0) d (denotBasis sigma b0) := by
    have h := hf.dims
    simp only [Basis.tof,RawAgreeDimsAt,denotBasis_frame_domainBasis] at h
    exact h.1
  have hc : RawTermTraceAt orc sigma rho (.reshap a d (ValExpr.inferType a))
      (Basis.tof b0) d (denotBasis sigma b0) (denotTerm sigma n1) := by
    refine ⟨?_,hd⟩
    simpa only [ValExpr.inferTypeCtx_nil] using
      (RawNonBetaValueKernel.holds orc).reshape hd ha.dims ha.result
  have hr := rawAppNVal_result hn hm hp
    (by simpa only [hi,ValTy.domain_piTy] using ValSoundOfDenot.ValTy.SameShape.refl d)
    (by
      intro s t hs ht
      have hs' : d = .space s := by simpa only [hi,ValTy.domain_piTy] using hs
      have he : s = t := ValTy.space.inj (hs'.symm.trans ht)
      subst t
      rfl)
    hshape hf hc ho
  simpa only [ValExpr.applyValue,← ValExpr.inferTypeCtx_nil,hi,ValTy.domain_piTy] using hr

/-- The independently realized target remains an ordinary reshape argument. -/
theorem rawApplyAtSelf_result
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b0 b1 : Basis} {n0 n1 : Term} {f a : ValExpr} {d c out : ValTy}
    (hn : Term.lc n1)
    (hm : (denotTerm sigma n1).matchesShape (denotTy sigma (Basis.tof b0)))
    (hp : ∃ g : (denotTy sigma (Basis.tof b0)).El → DVal,
      denotTerm sigma n0 = .pi (denotTy sigma (Basis.tof b0)).El g)
    (hi : ValExpr.inferTypeCtx [] f = .piTy d c)
    (hshape : ValSoundOfDenot.ValTy.SameShape c out)
    (hf : RawTermTraceAt orc sigma rho f (Basis.tof (.frame b0 b1))
      (.piTy d c) (denotBasis sigma (.frame b0 b1)) (denotTerm sigma n0))
    (ha : RawTermTraceAt orc sigma rho a (Basis.tof b0) (ValExpr.inferTypeCtx [] a)
      (denotBasis sigma b0) (denotTerm sigma n1))
    (ho : RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof (Basis.instantiate n1 b1))
      out (denotBasis sigma (Basis.instantiate n1 b1))) :
    RawTermTraceAt orc sigma rho (.reshap (.applyValue f a) out out) (Basis.tof (Basis.instantiate n1 b1))
      out (denotBasis sigma (Basis.instantiate n1 b1)) (denotTerm sigma (.appN n0 n1)) := by
  have hr := rawApplyValue_result hn hm hp hi hshape hf ha ho
  exact ⟨(RawNonBetaValueKernel.holds orc).reshape ho ho hr.result,ho⟩

/-- The independently realized target remains an ordinary reshape argument. -/
theorem rawApplyAt_result
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b0 b1 : Basis} {n0 n1 : Term} {f a : ValExpr} {d c out : ValTy}
    (hn : Term.lc n1)
    (hm : (denotTerm sigma n1).matchesShape (denotTy sigma (Basis.tof b0)))
    (hp : ∃ g : (denotTy sigma (Basis.tof b0)).El → DVal,
      denotTerm sigma n0 = .pi (denotTy sigma (Basis.tof b0)).El g)
    (hi : ValExpr.inferTypeCtx [] f = .piTy d c)
    (hshape : ValSoundOfDenot.ValTy.SameShape c out)
    (hf : RawTermTraceAt orc sigma rho f (Basis.tof (.frame b0 b1))
      (.piTy d c) (denotBasis sigma (.frame b0 b1)) (denotTerm sigma n0))
    (ha : RawTermTraceAt orc sigma rho a (Basis.tof b0) (ValExpr.inferTypeCtx [] a)
      (denotBasis sigma b0) (denotTerm sigma n1))
    (ho : RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof (Basis.instantiate n1 b1))
      out (denotBasis sigma (Basis.instantiate n1 b1)))
    (substitution : ∀ raw, denotValB_semS orc rho [] []
      (.reshap a d (ValExpr.inferType a)) = .ok raw →
      PaperValueDomains.RawTypePresentation orc c
        (ValTy.applyCodomain (.reshap a d (ValExpr.inferType a)) c)
        ⟨rho,[d],[raw]⟩ ⟨rho,[],[]⟩) :
    RawTermTraceAt orc sigma rho (.applyAt f a out) (Basis.tof (Basis.instantiate n1 b1))
      out (denotBasis sigma (Basis.instantiate n1 b1)) (denotTerm sigma (.appN n0 n1)) := by
  have hd : RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b0) d (denotBasis sigma b0) := by
    have h := hf.dims
    simp only [Basis.tof,RawAgreeDimsAt,denotBasis_frame_domainBasis] at h
    exact h.1
  let u := ValExpr.reshap a d (ValExpr.inferType a)
  have argument : RawTermTraceAt orc sigma rho u (Basis.tof b0) d
      (denotBasis sigma b0) (denotTerm sigma n1) := by
    refine ⟨?_,hd⟩
    simpa only [ValExpr.inferTypeCtx_nil] using
      (RawNonBetaValueKernel.holds orc).reshape hd ha.dims ha.result
  let T0 := denotTy sigma (Basis.tof b0)
  let x' : T0.El := T0.extract (denotTerm sigma n1)
  have hxT : T0.embed x' = denotTerm sigma n1 := HType.embed_extract_of_matchesShape hm
  obtain ⟨funValue,hfunEval,hfunAgree⟩ := hf.result
  obtain ⟨argValue,hargEval,hargAgree⟩ := argument.result
  have hargForApp : RawAgree orc sigma rho [] [] [] (Basis.tof b0) d
      (denotBasis sigma (.frame b0 b1)).domainBasis (T0.embed x') argValue := by
    simpa only [denotBasis_frame_domainBasis,hxT] using hargAgree
  obtain ⟨arg,r,hto,happ,hrPush⟩ := RawAgree.appV_result x' f u out
    hfunAgree hargForApp
    (by simpa only [hi,ValTy.domain_piTy] using ValSoundOfDenot.ValTy.SameShape.refl d)
    (by
      intro s t hs ht
      have he : s = t := ValTy.space.inj ((by simpa only [hi,ValTy.domain_piTy] using hs : d = .space s).symm.trans ht)
      subst t; rfl)
    hfunEval hargEval
  have hdFun := hf.dims
  simp only [Basis.tof,RawAgreeDimsAt] at hdFun
  have hdPush := hdFun.2 x' argValue arg hto hargForApp
  have hrOpen : RawAgree orc sigma rho [] [d] [argValue]
      (Ty.openRec 0 n1 (Basis.tof b1)) c ((denotBasis sigma (.frame b0 b1)).applyEl x')
      ((denotTerm sigma n0).applyEl x') r := by
    apply (RawAgree.instantiate_src hn (Basis.tof b1) [d] [argValue] c _ _ r).mp
    simpa only [T0,hxT] using hrPush
  have hdOpen : RawAgreeDimsAt orc sigma rho [] [d] [argValue]
      (Ty.openRec 0 n1 (Basis.tof b1)) c ((denotBasis sigma (.frame b0 b1)).applyEl x') := by
    apply (RawAgreeDimsAt.instantiate_src hn (Basis.tof b1) [d] [argValue] c _).mp
    simpa only [T0,hxT] using hdPush
  obtain ⟨g,hg⟩ := hp
  have hb := denotBasis_frame_applyEl_instantiate (sigma := sigma) (n1 := n1)
    (b0 := b0) (b1 := b1) hn hm
  have he := denotTerm_appN_applyEl (sigma := sigma) (n0 := n0) (n1 := n1)
    (T0 := T0) (g := g) (by simpa only [T0] using hg) hm
  rw [hb,←he] at hrOpen
  rw [hb] at hdOpen
  have hoOpen : RawAgreeDimsAt orc sigma rho [] [] []
      (Ty.openRec 0 n1 (Basis.tof b1)) out (denotBasis sigma (Basis.instantiate n1 b1)) := by
    simpa only [Basis.instantiate,Basis.tof_openRec] using ho
  have hres := reshapDenotSemBetweenS_rawResult orc sigma rho _ out c
    [] [] [] [d] [argValue] _ _ r hoOpen hdOpen hrOpen
  have hs := substitution argValue hargEval
  have heq := PaperValueDomains.rawPresentation_reshape orc out c out
    (ValTy.applyCodomain u c) rho rho [] [] [d] [] [] [] [argValue] []
    (PaperValueDomains.RawTypePresentation.refl orc out ⟨rho,[],[]⟩) hs r
  rw [heq] at hres
  obtain ⟨result,hresult,hagree⟩ := hres
  refine ⟨⟨result,?_,?_⟩,ho⟩
  · have hi' : ValExpr.inferType f = .piTy d c := by simpa only [ValExpr.inferTypeCtx_nil] using hi
    simpa only [ValExpr.applyAt,ValExpr.applyValue,hi',ValTy.domain_piTy,
      ValExpr.inferType,denotValB_semS.eq_17, u, happ,
      reshapDenotSemS_eq_between] using hresult
  · simpa only [Basis.instantiate,Basis.tof_openRec] using hagree

end GLang
