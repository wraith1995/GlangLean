import GLang.Proofs.Adequacy.Partial.Source.PartialSourceHistory
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMotives

set_option maxHeartbeats 1800000
namespace GLang.PartialAdequacy
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

private theorem raw_denot_after_self_update {orc : PartialFFSOracleSem}
    (hirr : PartialDirectFv.OracleFresh orc) {rho : ValEnvSem} {x : VName}
    {v : ValExpr} {yV : ValValSem}
    (hnr : x ∉ ValExpr.fv v \/ exists tau, v = .var x tau)
    (hden : denotValB_partial orc rho [] [] v = .ok yV) :
    denotValB_partial orc (rho.update x yV) [] [] v = .ok yV := by
  rcases hnr with hnot | ⟨tau, rfl⟩
  · rw [PartialDirectFv.eval_eq hirr rho x yV v
      [] [] hnot (by simp)]
    exact hden
  · simp only [denotValB_partial, ValEnvSem.update_same]

theorem History.stored_raw_current_infer {orc : PartialFFSOracleSem}
    (hirr : PartialDirectFv.OracleFresh orc)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : History orc Delta Gamma Psi GammaV sigma rho)
    {x : VName} {b : Basis} (hmem : (x, b) ∈ Psi) :
    exists (v : ValExpr) (tauV : ValTy) (xs : DVal) (yV : ValValSem)
      (Gamma0 : NLCtx) (Psi0 : EvalCtx),
      EvalCtx.lookup Psi (x, b) = some v /\
      sigma.vars.lookup x = some xs /\
      ValTy.EvalT Psi0 (Basis.tof b) tauV /\
      ValExpr.InferSpaceMatchesBase v tauV /\
      Basis.fv b ⊆ Psi.keyNames /\
      ValTy.fv tauV ⊆ Psi.keyNames /\
      denotValB_partial orc rho [] [] v = .ok yV /\
      Agree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) xs yV /\
      DimsAt orc sigma rho [] [] [] (Basis.tof b) tauV
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
        rw [PartialDirectFv.eval_eq hirr rho x' yV' v [] []
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
        rw [PartialDirectFv.eval_eq hirr rho x' yV' v [] []
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

/-- The domain of a successfully realized source Pi type is itself successful
at every kind, including higher-order function domains. -/
theorem DimsAt.domain {orc : PartialFFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {G : List ValTy} {D : List ValValSem} {t0 t1 : Ty} {tv : ValTy} {B : BasisDenot}
    (h : DimsAt orc sigma rho Ds G D (.piTy t0 t1) tv B) :
    DimsAt orc sigma rho Ds G D t0 tv.domain B.domainBasis := by
  cases tv with
  | space s => simp only [DimsAt] at h
  | piTy d c =>
    simp only [DimsAt] at h
    exact h.1

/-- Pi-valued producers retain a fully successful inferred application domain,
not just the dimension of a base domain. Stored entries use their exact
creation type transported through the semantic history. -/
theorem inferType_domain_dims
    {DeltaS : LCtx} {GammaS : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauv0 tauv1 : ValTy}
    (h : S.Term DeltaS GammaS Psi e b v (.piTy tauv0 tauv1))
    {orc : PartialFFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (hc : History orc DeltaC GammaC Psi GammaV sigma rho)
    (hirr : PartialDirectFv.OracleFresh orc)
    {t0 t1 : Ty} (ht : Basis.tof b = .piTy t0 t1)
    (hdims : DimsAt orc sigma rho [] [] [] (Basis.tof b)
      (.piTy tauv0 tauv1) (denotBasis sigma b)) :
    DimsAt orc sigma rho [] [] [] t0 (ValExpr.inferTypeCtx [] v).domain
      (denotBasis sigma b).domainBasis := by
  refine S.Term.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ Psi _ b v tauv _ =>
      forall {dom cod : ValTy}, tauv = .piTy dom cod ->
      forall {orc : PartialFFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
        {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem},
        History orc DeltaC GammaC Psi GammaV sigma rho ->
        PartialDirectFv.OracleFresh orc →
        forall {t0 t1 : Ty}, Basis.tof b = .piTy t0 t1 →
        DimsAt orc sigma rho [] [] [] (Basis.tof b)
          (.piTy dom cod) (denotBasis sigma b) →
        DimsAt orc sigma rho [] [] [] t0 (ValExpr.inferTypeCtx [] v).domain
          (denotBasis sigma b).domainBasis)
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
    rw [ht] at hdimsStored
    exact hdimsStored.domain
  case termVarNlin =>
    intro Gamma Psi x b v tauv hlookup _hGamma _hbv htauv _ihtauv
      dom cod htauvPi orc DeltaC GammaC GammaV sigma rho hc hirr t0 t1 ht hdims
    obtain ⟨vStored,tauStored,xs,yV,Gamma0,Psi0,hPsi,_,_,_,_,_,_,_,hdimsStored,hinfer⟩ :=
      hc.stored_raw_current_infer hirr (Finmap.mem_of_lookup_eq_some hlookup)
    have hv : vStored = v := Option.some.inj (hPsi.symm.trans hlookup)
    subst vStored
    rw [hinfer]
    rw [ht] at hdimsStored
    exact hdimsStored.domain
  all_goals
    simp only [ValExpr.applyAt, ValExpr.inferTypeCtx,reduceCtorEq,forall_const,false_implies,ValTy.domain_piTy]
  all_goals intros
  all_goals try trivial
  case termPromote => solve_by_elim (maxDepth := 8)
  all_goals
    rename_i dom cod hpi orc DC GC GV sig rh hc hf t0 t1 htof hd
    rw [htof] at hd
    have he := congrArg ValTy.domain hpi
    simp only [ValTy.domain_piTy] at he
    simpa only [he] using hd.domain

/-- The entire inferred function type, including every dependent codomain,
realizes the source type. This strengthens the domain-only companion. -/
theorem inferType_pi_dims
    {DeltaS : LCtx} {GammaS : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauv0 tauv1 : ValTy}
    (h : S.Term DeltaS GammaS Psi e b v (.piTy tauv0 tauv1))
    {orc : PartialFFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (hc : History orc DeltaC GammaC Psi GammaV sigma rho)
    (hirr : PartialDirectFv.OracleFresh orc)
    {t0 t1 : Ty} (ht : Basis.tof b = .piTy t0 t1)
    (hdims : DimsAt orc sigma rho [] [] [] (Basis.tof b)
      (.piTy tauv0 tauv1) (denotBasis sigma b)) :
    DimsAt orc sigma rho [] [] [] (Basis.tof b) (ValExpr.inferTypeCtx [] v)
      (denotBasis sigma b) := by
  refine S.Term.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ Psi _ b v tauv _ =>
      forall {dom cod : ValTy}, tauv = .piTy dom cod ->
      forall {orc : PartialFFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
        {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem},
        History orc DeltaC GammaC Psi GammaV sigma rho ->
        PartialDirectFv.OracleFresh orc →
        forall {t0 t1 : Ty}, Basis.tof b = .piTy t0 t1 →
        DimsAt orc sigma rho [] [] [] (Basis.tof b)
          (.piTy dom cod) (denotBasis sigma b) →
        DimsAt orc sigma rho [] [] [] (Basis.tof b) (ValExpr.inferTypeCtx [] v)
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

theorem inferType_domain_sameShape
    {DeltaS : LCtx} {GammaS : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauv0 tauv1 : ValTy}
    (h : S.Term DeltaS GammaS Psi e b v (.piTy tauv0 tauv1))
    {orc : PartialFFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (hc : History orc DeltaC GammaC Psi GammaV sigma rho) :
    ValSoundOfDenot.ValTy.SameShape
      (ValExpr.inferTypeCtx [] v).domain tauv0 := by
  refine S.Term.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ Psi _ _ v tauv _ =>
      forall {dom cod : ValTy}, tauv = .piTy dom cod ->
      forall {orc : PartialFFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
        {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem},
        History orc DeltaC GammaC Psi GammaV sigma rho ->
        ValSoundOfDenot.ValTy.SameShape
          (ValExpr.inferTypeCtx [] v).domain dom)
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
    ?termZero ?termRlit h rfl hc
  case termVarLin =>
    intro Gamma Psi x b v s tauv hlookup _htof _hbv htauv _ihtauv
      dom cod htauvPi orc DeltaC GammaC GammaV sigma rho hc
    obtain ⟨vStored, tauStored, xs, yV, Delta0, Gamma0, Psi0, GammaV0,
        sigma0, rho0, hstored, _hIncl, hPsi, _hsigma, _hctx⟩ :=
      hc.lookup (Finmap.mem_of_lookup_eq_some hlookup)
    have hv : vStored = v := Option.some.inj (hPsi.symm.trans hlookup)
    subst vStored
    have hinfer : ValExpr.inferTypeCtx [] v = tauStored := by
      rw [inferTypeCtx_of_lc [] hstored.hlc, hstored.hinfer]
    have hshape : ValSoundOfDenot.ValTy.SameShape tauStored tauv :=
      evalT_sameShape hstored.hTy htauv.toEvalT
    rw [hinfer]
    simpa only [htauvPi, ValTy.domain_piTy] using hshape.domain
  case termVarNlin =>
    intro Gamma Psi x b v tauv hlookup _hGamma _hbv htauv _ihtauv
      dom cod htauvPi orc DeltaC GammaC GammaV sigma rho hc
    obtain ⟨vStored, tauStored, xs, yV, Delta0, Gamma0, Psi0, GammaV0,
        sigma0, rho0, hstored, _hIncl, hPsi, _hsigma, _hctx⟩ :=
      hc.lookup (Finmap.mem_of_lookup_eq_some hlookup)
    have hv : vStored = v := Option.some.inj (hPsi.symm.trans hlookup)
    subst vStored
    have hinfer : ValExpr.inferTypeCtx [] v = tauStored := by
      rw [inferTypeCtx_of_lc [] hstored.hlc, hstored.hinfer]
    have hshape : ValSoundOfDenot.ValTy.SameShape tauStored tauv :=
      evalT_sameShape hstored.hTy htauv.toEvalT
    rw [hinfer]
    simpa only [htauvPi, ValTy.domain_piTy] using hshape.domain
  all_goals
    simp_all [ValExpr.applyAt, ValExpr.inferTypeCtx]

end GLang.PartialAdequacy
