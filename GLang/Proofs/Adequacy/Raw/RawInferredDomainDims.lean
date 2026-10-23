import GLang.Proofs.Adequacy.Raw.Context.RawConsistent
import GLang.Proofs.Adequacy.Foundations.StrengthenedMono
import GLang.Proofs.Value.Soundness.ValueSoundnessSem

/-! Runtime application checks the inferred domain dimension. -/

set_option maxHeartbeats 1200000
namespace GLang
private theorem raw_evalCtx_mem_extend
    {Psi : EvalCtx} {x x' : VName} {b b' : Basis} {v : ValExpr} :
    (x', b') ∈ Psi.extend x b v ↔
      (x' = x ∧ b' = b) ∨ (x', b') ∈ Psi := by
  simp only [EvalCtx.extend, Finmap.mem_insert, Prod.mk.injEq]

private theorem raw_evalCtx_mem_keyNames
    {Psi : EvalCtx} {x : VName} :
    x ∈ Psi.keyNames ↔ ∃ b, (x, b) ∈ Psi := by
  rw [EvalCtx.keyNames, Finset.mem_image]
  constructor
  · rintro ⟨⟨x', b⟩, hp, rfl⟩
    exact ⟨b, Finmap.mem_keys.mp hp⟩
  · rintro ⟨b, hb⟩
    exact ⟨(x, b), Finmap.mem_keys.mpr hb, rfl⟩

private theorem raw_evalCtx_keyNames_subset_extend
    (Psi : EvalCtx) (y : VName) (b : Basis) (v : ValExpr) :
    Psi.keyNames ⊆ (Psi.extend y b v).keyNames := by
  rw [EvalCtx.keyNames_extend_core]
  exact Finset.subset_insert _ _

private theorem raw_evalCtx_not_mem_keyNames_of_forall
    {Psi : EvalCtx} {y : VName}
    (hy : ∀ b', (y, b') ∉ Psi) : y ∉ Psi.keyNames := by
  rw [raw_evalCtx_mem_keyNames]
  rintro ⟨b, hb⟩
  exact hy b hb

private theorem raw_denot_after_self_update {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc) {rho : ValEnvSem} {x : VName}
    {v : ValExpr} {yV : ValValSem}
    (hnr : x ∉ ValExpr.fv v \/ exists tau, v = .var x tau)
    (hden : denotValB_semS orc rho [] [] v = .ok yV) :
    denotValB_semS orc (rho.update x yV) [] [] v = .ok yV := by
  rcases hnr with hnot | ⟨tau, rfl⟩
  · rw [denotValB_semS_update_of_not_mem_fv hirr rho x yV v
      [] [] hnot (by simp)]
    exact hden
  · simp only [denotValB_semS.eq_2, ValEnvSem.update_same]

theorem RawConsistent.stored_raw_current_infer {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    {x : VName} {b : Basis} (hmem : (x, b) ∈ Psi) :
    exists (v : ValExpr) (tauV : ValTy) (xs : DVal) (yV : ValValSem)
      (Gamma0 : NLCtx) (Psi0 : EvalCtx),
      EvalCtx.lookup Psi (x, b) = some v /\
      sigma.vars.lookup x = some xs /\
      ValTy.EvalT Psi0 (Basis.tof b) tauV /\
      ValExpr.InferSpaceMatchesBase v tauV /\
      Basis.fv b ⊆ Psi.keyNames /\
      ValTy.fv tauV ⊆ Psi.keyNames /\
      denotValB_semS orc rho [] [] v = .ok yV /\
      RawAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) xs yV /\
      RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) /\
      ValExpr.inferTypeCtx [] v = tauV := by
  induction h with
  | empty => exact absurd hmem Finmap.notMem_empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x' b' v' tauV' xs' s yV'
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      have hfvb := hc.basisFvPrefix hb
      have hfvTy := hc.typeFvPrefix hTy
      have hxKey : x' ∉ Psi.keyNames :=
        raw_evalCtx_not_mem_keyNames_of_forall (hc.freshEvalName hx)
      have hsub := raw_evalCtx_keyNames_subset_extend Psi x' b' v'
      rcases raw_evalCtx_mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · obtain ⟨hagree', hdims'⟩ := raw_bind_update_of_fresh hirr
          (fun hm => hxKey (hfvb hm)) (fun hm => hxKey (hfvTy hm))
          xs' yV' hagree hdims
        exact ⟨v', tauV', xs', yV', Gamma, Psi,
          by simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert],
          by simp [DEnv.bind, Finmap.lookup_insert], hTy, hinferSpace,
          hfvb.trans hsub, hfvTy.trans hsub,
          raw_denot_after_self_update hirr hnr hden,
          hagree', hdims', by rw [inferTypeCtx_of_lc [] hlc, hinfer]⟩
      · obtain ⟨v, tauV, xs, yV, Gamma0, Psi0, hPsi, hsigma,
          hsty, hinfer0, hfvb0, hfvTy0, hden0, hagree0, hdims0, hexact0⟩ := ih hmem'
        have hxx : x ≠ x' := fun e =>
          hc.freshEvalName hx b (e ▸ hmem')
        obtain ⟨hagree', hdims'⟩ := raw_bind_update_of_fresh hirr
          (fun hm => hxKey (hfvb0 hm)) (fun hm => hxKey (hfvTy0 hm))
          xs' yV' hagree0 hdims0
        have hne : (x, b) ≠ (x', b') := fun e => hxx (Prod.mk.inj e).1
        have hfvv0 : ValExpr.fv v ⊆ Psi.keyNames :=
          (hc.stored_fv x b v hPsi).2
        refine ⟨v, tauV, xs, yV, Gamma0, Psi0,
          by simpa [EvalCtx.extend, EvalCtx.lookup,
            Finmap.lookup_insert_of_ne _ hne] using hPsi,
          by simpa [DEnv.bind, Finmap.lookup_insert_of_ne _ hxx] using hsigma,
          hsty, hinfer0, hfvb0.trans hsub, hfvTy0.trans hsub, ?_,
          hagree', hdims', hexact0⟩
        rw [denotValB_semS_update_of_not_mem_fv hirr rho x' yV' v [] []
          (fun hm => hxKey (hfvv0 hm))
          (by simp)]
        exact hden0
  | @extend_nl Delta Gamma Psi GammaV sigma rho x' b' v' tauV' xs' yV'
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      have hfvb := hc.basisFvPrefix hb
      have hfvTy := hc.typeFvPrefix hTy
      have hxKey : x' ∉ Psi.keyNames :=
        raw_evalCtx_not_mem_keyNames_of_forall (hc.freshEvalName hx)
      have hsub := raw_evalCtx_keyNames_subset_extend Psi x' b' v'
      rcases raw_evalCtx_mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · obtain ⟨hagree', hdims'⟩ := raw_bind_update_of_fresh hirr
          (fun hm => hxKey (hfvb hm)) (fun hm => hxKey (hfvTy hm))
          xs' yV' hagree hdims
        exact ⟨v', tauV', xs', yV', Gamma, Psi,
          by simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert],
          by simp [DEnv.bind, Finmap.lookup_insert], hTy, hinferSpace,
          hfvb.trans hsub, hfvTy.trans hsub,
          raw_denot_after_self_update hirr hnr hden,
          hagree', hdims', by rw [inferTypeCtx_of_lc [] hlc, hinfer]⟩
      · obtain ⟨v, tauV, xs, yV, Gamma0, Psi0, hPsi, hsigma,
          hsty, hinfer0, hfvb0, hfvTy0, hden0, hagree0, hdims0, hexact0⟩ := ih hmem'
        have hxx : x ≠ x' := fun e =>
          hc.freshEvalName hx b (e ▸ hmem')
        obtain ⟨hagree', hdims'⟩ := raw_bind_update_of_fresh hirr
          (fun hm => hxKey (hfvb0 hm)) (fun hm => hxKey (hfvTy0 hm))
          xs' yV' hagree0 hdims0
        have hne : (x, b) ≠ (x', b') := fun e => hxx (Prod.mk.inj e).1
        have hfvv0 : ValExpr.fv v ⊆ Psi.keyNames :=
          (hc.stored_fv x b v hPsi).2
        refine ⟨v, tauV, xs, yV, Gamma0, Psi0,
          by simpa [EvalCtx.extend, EvalCtx.lookup,
            Finmap.lookup_insert_of_ne _ hne] using hPsi,
          by simpa [DEnv.bind, Finmap.lookup_insert_of_ne _ hxx] using hsigma,
          hsty, hinfer0, hfvb0.trans hsub, hfvTy0.trans hsub, ?_,
          hagree', hdims', hexact0⟩
        rw [denotValB_semS_update_of_not_mem_fv hirr rho x' yV' v [] []
          (fun hm => hxKey (hfvv0 hm))
          (by simp)]
        exact hden0
  | @extend_rep Delta Gamma Psi GammaV sigma rho x' b' v' tauV' xs' yV'
      hc hkey hsource hsigma' hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      have hfvb := hc.basisFvPrefix hb
      have hfvTy := hc.typeFvPrefix hTy
      have hsub := raw_evalCtx_keyNames_subset_extend Psi x' b' v'
      rcases raw_evalCtx_mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · exact ⟨v', tauV', xs', yV', Gamma, Psi,
          by simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert],
          hsigma', hTy, hinferSpace, hfvb.trans hsub, hfvTy.trans hsub,
          hden, hagree, hdims, by rw [inferTypeCtx_of_lc [] hlc, hinfer]⟩
      · obtain ⟨v, tauV, xs, yV, Gamma0, Psi0, hPsi, hsigma,
          hsty, hinfer0, hfvb0, hfvTy0, hden0, hagree0, hdims0, hexact0⟩ := ih hmem'
        have hne : (x, b) ≠ (x', b') := fun e => hkey (e ▸ hmem')
        exact ⟨v, tauV, xs, yV, Gamma0, Psi0,
          by simpa [EvalCtx.extend, EvalCtx.lookup,
            Finmap.lookup_insert_of_ne _ hne] using hPsi,
          hsigma, hsty, hinfer0, hfvb0.trans hsub, hfvTy0.trans hsub,
          hden0, hagree0, hdims0, hexact0⟩

theorem RawAgreeDimsAt.domain_dof_eq
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {tau : Ty} {a dom cod : ValTy} {B : BasisDenot}
    (ha : RawAgreeDimsAt orc sigma rho [] [] [] tau a B)
    (hb : RawAgreeDimsAt orc sigma rho [] [] [] tau (.piTy dom cod) B)
    {s t : ValSpace} (hs : a.domain = .space s) (ht : dom = .space t) :
    ValSpace.dof (orc rho [] []) s = ValSpace.dof (orc rho [] []) t := by
  subst dom
  cases tau with
  | space x => simp only [RawAgreeDimsAt] at hb
  | piTy x y =>
    cases a with
    | space z => simp only [RawAgreeDimsAt] at ha
    | piTy d c =>
      simp only [ValTy.domain_piTy] at hs
      subst d
      simp only [RawAgreeDimsAt] at ha hb
      have hx := ha.1
      have hy := hb.1
      cases x with
      | piTy x y => simp only [RawAgreeDimsAt] at hx
      | space x =>
        simp only [RawAgreeDimsAt] at hx hy
        change ValSpace.shpOf _ s = _ at hx
        change ValSpace.shpOf _ t = _ at hy
        simpa only [ValSpace.dof] using
          congrArg (fun sh : List Nat => sh.foldr (· * ·) 1) (hx.trans hy.symm)

theorem S.Term.inferType_domain_dof_eq_raw
    {DeltaS : LCtx} {GammaS : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauv0 tauv1 : ValTy}
    (h : S.Term DeltaS GammaS Psi e b v (.piTy tauv0 tauv1))
    {orc : FFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (hc : RawConsistent orc DeltaC GammaC Psi GammaV sigma rho)
    (hirr : OracleFvIrrel orc)
    (hdims : RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b)
      (.piTy tauv0 tauv1) (denotBasis sigma b)) :
    ∀ s t, (ValExpr.inferTypeCtx [] v).domain = .space s → tauv0 = .space t →
      ValSpace.dof (orc rho [] []) s = ValSpace.dof (orc rho [] []) t := by
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
        RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b)
          (.piTy dom cod) (denotBasis sigma b) →
        ∀ s t, (ValExpr.inferTypeCtx [] v).domain = .space s → dom = .space t →
          ValSpace.dof (orc rho [] []) s = ValSpace.dof (orc rho [] []) t)
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
    ?termZero ?termRlit h rfl hc hirr hdims
  case termVarLin =>
    intro Gamma Psi x b v s tauv hlookup _htof _hbv htauv _ihtauv
      dom cod htauvPi orc DeltaC GammaC GammaV sigma rho hc hirr hdims s t hs ht
    obtain ⟨vStored, tauStored, xs, yV, Gamma0, Psi0,
      hPsi, _, _, _, _, _, _, _, hdimsStored, hinfer⟩ :=
      hc.stored_raw_current_infer hirr (Finmap.mem_of_lookup_eq_some hlookup)
    have hv : vStored = v := Option.some.inj (hPsi.symm.trans hlookup)
    subst vStored
    rw [hinfer] at hs
    exact RawAgreeDimsAt.domain_dof_eq hdimsStored hdims hs ht
  case termVarNlin =>
    intro Gamma Psi x b v tauv hlookup _hGamma _hbv htauv _ihtauv
      dom cod htauvPi orc DeltaC GammaC GammaV sigma rho hc hirr hdims s t hs ht
    obtain ⟨vStored, tauStored, xs, yV, Gamma0, Psi0,
      hPsi, _, _, _, _, _, _, _, hdimsStored, hinfer⟩ :=
      hc.stored_raw_current_infer hirr (Finmap.mem_of_lookup_eq_some hlookup)
    have hv : vStored = v := Option.some.inj (hPsi.symm.trans hlookup)
    subst vStored
    rw [hinfer] at hs
    exact RawAgreeDimsAt.domain_dof_eq hdimsStored hdims hs ht
  all_goals
    simp_all [ValExpr.applyAt, ValExpr.inferTypeCtx]

end GLang
