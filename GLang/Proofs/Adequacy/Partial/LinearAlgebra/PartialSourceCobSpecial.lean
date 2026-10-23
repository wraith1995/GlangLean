import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCobMotives
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCanonical
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobInverse
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobAdequacyCore

namespace GLang.PartialAdequacy
open scoped BigOperators Matrix

theorem arm_cob_infer_image
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 : Basis} {env : ValExpr}
    (hbSrc : Basis.BasisValid Gamma (.image b0))
    (hcoker : exists s0 s1 e, Basis.sof b0 = .coker s0 s1 e)
    (ih : CobInferSubctx orc Gamma Psi env b0) :
    CobInferSubctx orc Gamma Psi env (.image b0) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa, sb, hinfer, hsa, hsb⟩ :=
    ih hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨s0, s1, e, hsof⟩ := hcoker
  have hbase := denotBasis_atSpace_isListBasis sigma Gamma' b0
    (raw_basisValid_mono hbSrc.image_inv.1 hle)
    hc.ctxWF_nl hc.envWF_nl
  have himage := denotBasis_atSpace_isListBasis sigma Gamma' (.image b0)
    (raw_basisValid_mono hbSrc hle) hc.ctxWF_nl hc.envWF_nl
  have hdim :
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (Basis.sof b0))).length =
      ((denotBasis sigma (.image b0)).atSpace
        (denotSpace sigma (Basis.sof (.image b0)))).length := by
    have hsofImage : Basis.sof (.image b0) = .img s0 s1 e := by
      simp only [Basis.sof, hsof]
    rw [hbase.finrank_eq.symm, himage.finrank_eq.symm, hsof, hsofImage]
    exact raw_finrank_denotSpace_coker_eq_img sigma s0 s1 e
  exact ⟨sa, sb, hinfer, hsa.trans (congrArg Except.ok hdim), hsb.trans (congrArg Except.ok hdim)⟩

theorem arm_cob_image
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b0' : Basis} {env : ValExpr}
    (_hbSrc : Basis.BasisValid Gamma (.image b0))
    (_hbTgt : Basis.BasisValid Gamma (.image b0'))
    (hcoker : exists s0 s1 e, Basis.sof b0 = .coker s0 s1 e)
    (h : S.Cob Gamma Psi b0 env b0')
    (ih : MCobSubctx orc Gamma Psi b0 env b0') :
    MCobSubctx orc Gamma Psi (.image b0) env (.image b0') := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨s0, s1, e, hsof⟩ := hcoker
  have hsof' : Basis.sof b0' = .coker s0 s1 e :=
    (S.Cob.sof_eq h).symm.trans hsof
  have hAgree := ih hsub rho Delta' Gamma' sigma GammaV hle hc
  unfold CobAgree CobResult CobRows at hAgree ⊢
  dsimp only at hAgree ⊢
  rw [hsof] at hAgree
  rw [Basis.raw_sof_image_of_coker hsof]
  obtain ⟨a, ha, htarget, halen, hsum⟩ := hAgree
  have hSource :
      (denotBasis sigma (.image b0)).atSpace
        (denotSpace sigma (.img s0 s1 e)) =
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (.coker s0 s1 e))).map
        (rawImageMap
          ((denotTerm sigma e).asLinMap
            (denotSpace sigma s0) (denotSpace sigma s1))
          (Submodule.orthRel (denotSpace sigma s0).innerProduct
            (LinearMap.ker ((denotTerm sigma e).asLinMap
              (denotSpace sigma s0) (denotSpace sigma s1))))) := by
    simp only [denotBasis]
    split
    · rename_i heq
      rw [hsof] at heq
      cases heq
      exact BasisDenot.atSpace_vecs_self _ _
    · rename_i heq
      exact (heq _ _ _ hsof).elim
  have hTarget :
      (denotBasis sigma (.image b0')).atSpace
        (denotSpace sigma (.img s0 s1 e)) =
      ((denotBasis sigma b0').atSpace
        (denotSpace sigma (.coker s0 s1 e))).map
        (rawImageMap
          ((denotTerm sigma e).asLinMap
            (denotSpace sigma s0) (denotSpace sigma s1))
          (Submodule.orthRel (denotSpace sigma s0).innerProduct
            (LinearMap.ker ((denotTerm sigma e).asLinMap
              (denotSpace sigma s0) (denotSpace sigma s1))))) := by
    simp only [denotBasis]
    split
    · rename_i heq
      rw [hsof'] at heq
      cases heq
      exact BasisDenot.atSpace_vecs_self _ _
    · rename_i heq
      exact (heq _ _ _ hsof').elim
  rw [hSource, hTarget]
  obtain ⟨h1, h2, h3⟩ := raw_cobAgree_map_list _ _ _ _ a
    htarget halen hsum
  exact ⟨a, ha, h1, h2, h3⟩

theorem arm_cob_image_facts
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b0' : Basis} {env : ValExpr}
    (hbSrc : Basis.BasisValid Gamma (.image b0))
    (hbTgt : Basis.BasisValid Gamma (.image b0'))
    (hcoker : exists s0 s1 e, Basis.sof b0 = .coker s0 s1 e)
    (h : S.Cob Gamma Psi b0 env b0')
    (ih : CobFactsSubctx orc Gamma Psi b0 env b0') :
    CobFactsSubctx orc Gamma Psi (.image b0) env (.image b0') :=
  ⟨arm_cob_image hbSrc hbTgt hcoker h ih.agree,
    arm_cob_infer_image hbSrc hcoker ih.infer⟩

theorem arm_cob_infer_dual_std
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 : Basis} {env : ValExpr}
    (ih : CobInferSubctx orc Gamma Psi env b0) :
    CobInferSubctx orc Gamma Psi (.vtrans (.inv env)) (.dual b0) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa, sb, hinfer, hsa, hsb⟩ :=
    ih hsub rho Delta' Gamma' sigma GammaV hle hc
  refine ⟨sa, sb, ?_, ?_, ?_⟩
  · simp only [ValExpr.inferSpaceCtx, hinfer]
  · simpa only [raw_denotBasis_dual_atSpace_length] using hsa
  · simpa only [raw_denotBasis_dual_atSpace_length] using hsb

theorem arm_cob_dual_std (orc : PartialFFSOracleSem)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 : Basis} {env : ValExpr}
    (hinfer : CobInferSubctx orc Gamma Psi env b0)
    (htof : Basis.tof b0 = .space (Basis.sof b0))
    (hbS : Basis.BasisValid Gamma (.dual b0))
    (hbT : Basis.BasisValid Gamma
      (Basis.std (Basis.tof (.dual b0))))
    (_h : S.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih : MCobSubctx orc Gamma Psi b0 env
      (Basis.std (Basis.tof b0))) :
    MCobSubctx orc Gamma Psi (.dual b0) (.vtrans (.inv env))
      (Basis.std (Basis.tof (.dual b0))) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa, sb, hsab, hNa, hNb⟩ :=
    hinfer hsub rho Delta' Gamma' sigma GammaV hle hc
  have hA := ih hsub rho Delta' Gamma' sigma GammaV hle hc
  unfold CobAgree CobResult CobRows at hA ⊢
  dsimp only at hA ⊢
  obtain ⟨a, ha, hTlen, halen, hrows⟩ := hA
  set V := denotSpace sigma (Basis.sof b0)
  set S0 := (denotBasis sigma b0).atSpace V
  set T0 := (denotBasis sigma (Basis.std (Basis.tof b0))).atSpace V
  have hstddual := Basis.raw_std_tof_dual_eq_dual_std_tof
    (b := b0) htof
  have hsofstd :
      Basis.sof (Basis.std (Basis.tof b0)) = Basis.sof b0 := by
    rw [htof]
    exact Basis.sof_stdSpace _
  have hbT0 : Basis.BasisValid Gamma
      (Basis.std (Basis.tof b0)) := by
    exact (hstddual ▸ hbT).dual_inv
  have hSb : IsListBasis V S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hbS.dual_inv hle)
      hc.ctxWF_nl hc.envWF_nl
  have hTb : IsListBasis V T0 := by
    have hb := denotBasis_atSpace_isListBasis sigma Gamma'
      (Basis.std (Basis.tof b0)) (raw_basisValid_mono hbT0 hle)
      hc.ctxWF_nl hc.envWF_nl
    rw [hsofstd] at hb
    exact hb
  let M : Matrix (Fin S0.length) (Fin S0.length) ℝ :=
    denotAsMatrix S0.length S0.length a.get
  let bT : Module.Basis (Fin S0.length) ℝ V.carrier :=
    hTb.toBasis.reindex (finCongr hTlen)
  have hbT_apply (i : Fin S0.length) : bT i = T0.getD i.val 0 := by
    rw [List.getD_eq_getElem T0 0 (hTlen.symm ▸ i.isLt)]
    simp [bT, Module.Basis.reindex_apply, IsListBasis.toBasis_apply]
  have hbS_apply (i : Fin S0.length) :
      hSb.toBasis i = S0.getD i.val 0 := by
    simp [IsListBasis.toBasis_apply]
  have hmrows : ∀ j, hSb.toBasis j = ∑ i, M j i • bT i := by
    intro j
    rw [hbS_apply, hrows j]
    apply Finset.sum_congr rfl
    intro i _
    rw [hbT_apply]
    simp [M, denotAsMatrix, Nat.mul_comm S0.length j.val]
  have hmrowsD : ∀ j : Fin S0.length,
      S0.getD j.val 0 = ∑ i, M j i • T0.getD i.val 0 := by
    intro j
    rw [hrows j]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp [M, denotAsMatrix, Nat.mul_comm S0.length j.val]
  have hright : M * matrixSVDPinv M = 1 :=
    Basis.raw_mul_svdPinv_eq_one_of_rows hSb.toBasis bT M hmrows
  have hdual := IsListBasis.raw_dualVec_transpose_expansion
    hSb hTb hTlen M (matrixSVDPinv M) hmrowsD hright
  have hsrc :
      (denotBasis sigma (.dual b0)).atSpace (HSpace.dual V) =
        V.dualOfList S0 := by
    simp only [denotBasis]
    exact BasisDenot.atSpace_vecs_self _ _
  have htgt :
      (denotBasis sigma
        (Basis.std (Basis.tof (.dual b0)))).atSpace (HSpace.dual V) =
        V.dualOfList T0 := by
    rw [hstddual]
    simp only [denotBasis]
    rw [hsofstd]
    exact BasisDenot.atSpace_vecs_self _ _
  let r : ValueCanonicalFSV.ResultMatrix := ⟨S0.length,S0.length,matrixSVDPinv M⟩
  have hinv : denotValB_partial orc rho [] [] (.inv env) = .ok (.array r.flatten) :=
    eval_inv ha hsab hNa hNb halen
  obtain ⟨w,hval,hwlen,hwget⟩ := eval_transpose (r := r) hinv
    (by simp only [ValExpr.inferSpaceCtx,hsab]) hNb hNa
  change ∃ w, denotValB_partial orc rho [] [] (.vtrans (.inv env)) = .ok (.array w) ∧
    ((denotBasis sigma (Basis.std (Basis.tof (.dual b0)))).atSpace (HSpace.dual V)).length =
      ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).length ∧
    w.length = ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).length *
      ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).length ∧
    ∀ j : Fin ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).length,
      ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).getD j.val 0 =
        ∑ i : Fin ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).length,
          w.get (j.val*((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).length+i.val) •
          ((denotBasis sigma (Basis.std (Basis.tof (.dual b0)))).atSpace (HSpace.dual V)).getD i.val 0
  rw [hsrc,htgt,HSpace.dualOfList_length,HSpace.dualOfList_length]
  refine ⟨w,hval,hTlen,hwlen,?_⟩
  intro j
  rw [HSpace.raw_dualOfList_getD_eq_dualVec V S0 j.isLt,hdual j]
  apply Finset.sum_congr rfl
  intro i _
  rw [HSpace.raw_dualOfList_getD_eq_dualVec V T0 (hTlen.symm ▸ i.isLt)]
  congr 1
  exact (hwget j i).symm

theorem arm_cob_dual_std_facts (orc : PartialFFSOracleSem)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 : Basis} {env : ValExpr}
    (htof : Basis.tof b0 = .space (Basis.sof b0))
    (hbS : Basis.BasisValid Gamma (.dual b0))
    (hbT : Basis.BasisValid Gamma
      (Basis.std (Basis.tof (.dual b0))))
    (h : S.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih : CobFactsSubctx orc Gamma Psi b0 env
      (Basis.std (Basis.tof b0))) :
    CobFactsSubctx orc Gamma Psi (.dual b0) (.vtrans (.inv env))
      (Basis.std (Basis.tof (.dual b0))) :=
  ⟨arm_cob_dual_std orc ih.infer htof hbS hbT h ih.agree,
    arm_cob_infer_dual_std ih.infer⟩

end GLang.PartialAdequacy
