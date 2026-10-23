import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCobMotives

namespace GLang.PartialAdequacy

theorem basis_dimension {orc : PartialFFSOracleSem}
    {Gamma Gamma' : NLCtx} {Delta' : LCtx} {Psi Psi' : EvalCtx}
    {epsilon : ValCtx} {sigma : DEnv} {rho : ValEnvSem} {b : Basis} {sv : ValSpace}
    (hb : Basis.BasisValid Gamma b) (ih : MSpaceSubctx orc Gamma Psi (Basis.sof b) sv)
    (hsub : Psi.Subctx Psi') (hle : NLCtxIncl Gamma Gamma')
    (hc : TypedHistory orc Delta' Gamma' Psi' epsilon sigma rho) :
    sv.dofPartial (orc rho [] []) =
      .ok ((denotBasis sigma b).atSpace (denotSpace sigma (Basis.sof b))).length := by
  have hl := denotBasis_atSpace_isListBasis sigma Gamma' b
    (raw_basisValid_mono hb hle) hc.ctxWF_nl hc.envWF_nl
  exact (shape_dof (ih hsub rho Delta' Gamma' sigma epsilon hle hc)).trans
    (congrArg Except.ok hl.finrank_eq)

theorem arm_cob_refl {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {sv : ValSpace} (hb : Basis.BasisValid Gamma b)
    (ih : MSpaceSubctx orc Gamma Psi (Basis.sof b) sv) :
    CobFactsSubctx orc Gamma Psi b
      (.reshap (.idelta sv) (.space (.tprod sv sv)) (.space (.tprod sv sv))) b := by
  constructor
  · intro Psi' hsub rho Delta' Gamma' sigma epsilon hle hc
    have hd := basis_dimension hb ih hsub hle hc
    exact cob_reshape (dof_tprod_ok hd hd) (cob_refl _ hd)
  · intro Psi' hsub rho Delta' Gamma' sigma epsilon hle hc
    have hd := basis_dimension hb ih hsub hle hc
    exact ⟨sv,sv,rfl,hd,hd⟩

theorem arm_cob_inverse {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : ValExpr}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (he : S.Cob Gamma Psi b1 e b0) (ih : CobFactsSubctx orc Gamma Psi b1 e b0) :
    CobFactsSubctx orc Gamma Psi b0 (.inv e) b1 := by
  have hsof := he.sof_eq
  constructor
  · intro Psi' hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sa,sb,hi,ha,hb⟩ := ih.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    have hr := ih.agree hsub rho Delta' Gamma' sigma epsilon hle hc
    dsimp only [CobAgree] at hr ⊢
    rw [hsof] at hr ha hb
    have hs := denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1 hle) hc.ctxWF_nl hc.envWF_nl
    have ht := denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0 hle) hc.ctxWF_nl hc.envWF_nl
    rw [hsof] at hs
    exact cob_inverse hs ht hi ha hb hr
  · intro Psi' hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sa,sb,hi,ha,hb⟩ := ih.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    have hl := raw_denotBasis_length_eq_of_sof_eq hc.ctxWF_nl hc.envWF_nl
      (raw_basisValid_mono hb0 hle) (raw_basisValid_mono hb1 hle) hsof.symm
    refine ⟨sb,sa,?_,hb.trans (congrArg Except.ok hl.symm),ha.trans (congrArg Except.ok hl.symm)⟩
    simp only [ValExpr.inferSpaceCtx,hi]

theorem arm_cob_trans {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b2 : Basis} {e0 e1 : ValExpr} {sv : ValSpace}
    (hb0 : Basis.BasisValid Gamma b0)
    (h0 : S.Cob Gamma Psi b0 e0 b1) (h1 : S.Cob Gamma Psi b1 e1 b2)
    (ih0 : CobFactsSubctx orc Gamma Psi b0 e0 b1)
    (ih1 : CobFactsSubctx orc Gamma Psi b1 e1 b2)
    (ihS : MSpaceSubctx orc Gamma Psi (Basis.sof b0) sv) :
    CobFactsSubctx orc Gamma Psi b0
      (.mtm 0 0 sv sv e1 (ValExpr.reshapBase e0 (.tprod sv sv))) b2 := by
  have hsof := h0.sof_eq
  constructor
  · intro Psi' hsub rho Delta' Gamma' sigma epsilon hle hc
    have hd := basis_dimension hb0 ihS hsub hle hc
    have hr0 := ih0.agree hsub rho Delta' Gamma' sigma epsilon hle hc
    have hr1 := ih1.agree hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sa,sb,hi,ha,hb⟩ := ih1.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    have hl := raw_denotBasis_length_eq_of_sof_eq hc.ctxWF_nl hc.envWF_nl
      (raw_basisValid_mono h1.basisValid_src hle) (raw_basisValid_mono hb0 hle) hsof.symm
    rw [hl] at ha hb
    dsimp only [CobAgree] at hr0 hr1 ⊢
    rw [← hsof] at hr1
    exact cob_trans rfl hi hd hd hd ha hb (cob_reshape (dof_tprod_ok hd hd) hr0) hr1
  · intro Psi' hsub rho Delta' Gamma' sigma epsilon hle hc
    have hd := basis_dimension hb0 ihS hsub hle hc
    obtain ⟨sa,sb,hi,ha,hb⟩ := ih1.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    have hl := raw_denotBasis_length_eq_of_sof_eq hc.ctxWF_nl hc.envWF_nl
      (raw_basisValid_mono h1.basisValid_src hle) (raw_basisValid_mono hb0 hle) hsof.symm
    refine ⟨sv,sb,?_,hd,hb.trans (congrArg Except.ok hl)⟩
    simp only [ValExpr.reshapBase,ValExpr.inferSpaceCtx,ValTy.spaceOf,hi]

theorem arm_cob_tprod {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b0' b1' : Basis} {e0 e1 : ValExpr}
    (h0 : S.Cob Gamma Psi b0 e0 b0') (h1 : S.Cob Gamma Psi b1 e1 b1')
    (ih0 : CobFactsSubctx orc Gamma Psi b0 e0 b0')
    (ih1 : CobFactsSubctx orc Gamma Psi b1 e1 b1') :
    CobFactsSubctx orc Gamma Psi (.tprod b0 b1) (.vkrn e0 e1) (.tprod b0' b1') := by
  constructor
  · intro Psi' hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sa,sb,hi0,ha,hb⟩ := ih0.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sc,sd,hi1,hc',hd⟩ := ih1.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    have hr0 := ih0.agree hsub rho Delta' Gamma' sigma epsilon hle hc
    have hr1 := ih1.agree hsub rho Delta' Gamma' sigma epsilon hle hc
    have hr := cob_tprod hi0 hi1 ha hb hc' hd hr0 hr1
    dsimp only [CobAgree, Basis.sof, denotBasis, denotSpace, denotSpaceAux]
    simp only [denotBasis]
    rw [← h0.sof_eq, ← h1.sof_eq]
    simpa only [BasisDenot.atSpace_vecs_self] using hr
  · intro Psi' hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sa,sb,hi0,ha,hb⟩ := ih0.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sc,sd,hi1,hc',hd⟩ := ih1.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    refine ⟨.tprod sa sc,.tprod sb sd,?_,?_,?_⟩
    · simp only [ValExpr.inferSpaceCtx,hi0,hi1]
    all_goals rw [raw_denotBasis_tprod_atSpace_length]
    all_goals rw [ValSpace.dofPartial,ValSpace.shpOfPartial]
    · simp [ha,hc',bind,Except.bind,pure,Except.pure]
    · simp [hb,hd,bind,Except.bind,pure,Except.pure]

theorem arm_cob_dsum {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b0' b1' : Basis} {e0 e1 : ValExpr}
    (h0 : S.Cob Gamma Psi b0 e0 b0') (h1 : S.Cob Gamma Psi b1 e1 b1')
    (ih0 : CobFactsSubctx orc Gamma Psi b0 e0 b0')
    (ih1 : CobFactsSubctx orc Gamma Psi b1 e1 b1') :
    CobFactsSubctx orc Gamma Psi (.dsum b0 b1) (.vblk e0 e1) (.dsum b0' b1') := by
  constructor
  · intro Psi' hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sa,sb,hi0,ha,hb⟩ := ih0.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sc,sd,hi1,hc',hd⟩ := ih1.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    have hr0 := ih0.agree hsub rho Delta' Gamma' sigma epsilon hle hc
    have hr1 := ih1.agree hsub rho Delta' Gamma' sigma epsilon hle hc
    have hr := cob_dsum hi0 hi1 ha hb hc' hd hr0 hr1
    dsimp only [CobAgree, Basis.sof, denotBasis, denotSpace, denotSpaceAux]
    simp only [denotBasis]
    rw [← h0.sof_eq, ← h1.sof_eq]
    simpa only [BasisDenot.atSpace_vecs_self] using hr
  · intro Psi' hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sa,sb,hi0,ha,hb⟩ := ih0.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    obtain ⟨sc,sd,hi1,hc',hd⟩ := ih1.infer hsub rho Delta' Gamma' sigma epsilon hle hc
    refine ⟨.dsum sa sc,.dsum sb sd,?_,?_,?_⟩
    · simp only [ValExpr.inferSpaceCtx,hi0,hi1]
    all_goals rw [raw_denotBasis_dsum_atSpace_length]
    all_goals rw [ValSpace.dofPartial,ValSpace.shpOfPartial]
    · simp [ha,hc',bind,Except.bind,pure,Except.pure]
    · simp [hb,hd,bind,Except.bind,pure,Except.pure]

end GLang.PartialAdequacy
