import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceGPinv
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceGPinvDual
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourcePinvConstructors
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMatrixReadback

namespace GLang.PartialAdequacy
open scoped BigOperators Matrix TensorProduct
open Basis (BasisValid)

theorem arm_pinvT_gpinv
    {orc : PartialFFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {sv0 sv1 : ValSpace}
    (_ht : Nonempty (HasType ∅ Gamma (.pinvT (Basis.sof b1)
      (Basis.sof b0) e) (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (_hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (_he : S.Term ∅ Gamma Psi e (.tprod (.dual b1) b0) v
      (.space (.tprod sv1 sv0)))
    (_hi0 : S.Term ∅ Gamma Psi (.inner (Basis.sof b0))
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (_hi1 : S.Term ∅ Gamma Psi (.inner (Basis.sof b1))
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihTy : MTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (ihE : TermFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b1) b0) v (.space (.tprod sv1 sv0)))
    (ihI0 : TermFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b0)) (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : TermFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b1)) (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1))) :
    MTermSubctx orc ∅ Gamma Psi
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (.tprod (.dual b0) b1) (.gpinv v env1 env0)
      (.space (.tprod sv0 sv1)) := by
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma b0).atSpace V0
  let S1 := (denotBasis sigma b1).atSpace V1
  let f := (denotTerm sigma e).asLinMap V1 V0
  obtain ⟨hb0dualv, hb1v⟩ := hbv.tprod_inv
  have hb0v := hb0dualv.dual_inv
  have hb1tof : Basis.tof b1 = .space (Basis.sof b1) := by
    cases hbv with
    | tprod _ _ _ htof1 => exact htof1
  have hlb0 : IsListBasis V0 S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb1 : IsListBasis V1 S1 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb0d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b0)
    (raw_basisValid_mono hb0dualv hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb1d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b1)
    (raw_basisValid_mono (.dual hb1v hb1tof) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have trE := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI0 := ihI0.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI1 := ihI1.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hshape : ValSpace.shpOfPartial (orc rho [] []) (.tprod sv0 sv1) =
      .ok [Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual] using targetDims
  obtain ⟨hd0,hd1⟩ := tprod_shape_factors hshape
  simp only [denotSpace] at hd0 hd1
  rw [hlb0.finrank_eq] at hd0
  rw [hlb1.finrank_eq] at hd1
  have hinshape := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hinputshape : (.tprod sv1 sv0 : ValSpace).shpOfPartial (orc rho [] []) =
      .ok [((denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b1))).length,
        ((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))).length] := by
    simp [ValSpace.shpOfPartial,hd0,hd1,bind,Except.bind,pure,Except.pure,S0,S1,V0,V1]
  rw [hinputshape] at hinshape
  obtain ⟨sa,sb,hinfer,ha,hb⟩ := infer_tprod_of_partial_shape hinshape
  obtain ⟨ae,heval,halen,hM⟩ := trace_witness_matrix hlb1 hlb0 trE
  obtain ⟨ag,hg,hgl,hG⟩ := trace_inner_matrix hlb1 hlb1d trI1
  obtain ⟨ah,hh,hhl,hH⟩ := trace_inner_matrix hlb0 hlb0d trI0
  have hgd : ∃ d, (ValExpr.inferSpaceCtx [] env1).dofPartial (orc rho [] []) = .ok d := by
    have hi := ihI1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd1,bind,Except.bind,pure,Except.pure]
  have hhd : ∃ d, (ValExpr.inferSpaceCtx [] env0).dofPartial (orc rho [] []) = .ok d := by
    have hi := ihI0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd0,bind,Except.bind,pure,Except.pure]
  have hm := RawTermGPinvT.mooreTensor_eq_flat_gpinv_sum hlb1 hlb0 f
  rw [← hM,← hG,← hH] at hm
  refine ⟨⟨_,eval_gpinv heval hg hh hinfer ha hb hgd hhd
    ⟨halen,by simpa only [pow_two] using hgl,by simpa only [pow_two] using hhl⟩,?_⟩,targetDims⟩
  simp only [Basis.tof,Basis.sof,Agree,denotSpaceAux]
  rw [RawSpaceFFS.denotBasis_tprod_dual_atSpace]
  refine ⟨_,dof_tprod_ok hd0 hd1,?_,FlatArray.length_ofFn _ _,?_⟩
  · rw [HSpace.tprodOfLists_length,HSpace.dualOfList_length]
  · change (denotTerm sigma (.pinvT (Basis.sof b1) (Basis.sof b0) e)).atSpace
      (HSpace.tprod (HSpace.dual V0) V1) = _
    simp only [V0,V1,denotSpace,denotTerm,denotTermAux,pinvTensorDVal,DVal.atSpace_hil_self]
    change (dualTensorHomEquiv ℝ V0.carrier V1.carrier).symm
      (LinearMap.mooreInv V1.innerIsIP V0.innerIsIP f) = _
    rw [hm]
    apply Finset.sum_congr rfl
    intro k _
    rw [FlatArray.get_ofFn_lt _ _ _ k.isLt]
    rfl

theorem arm_pinvT_gpinv_facts
    {orc : PartialFFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {sv0 sv1 : ValSpace}
    (ht : Nonempty (HasType ∅ Gamma (.pinvT (Basis.sof b1)
      (Basis.sof b0) e) (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b1) b0) v
      (.space (.tprod sv1 sv0)))
    (hi0 : S.Term ∅ Gamma Psi (.inner (Basis.sof b0))
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (hi1 : S.Term ∅ Gamma Psi (.inner (Basis.sof b1))
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihTy : MTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (ihE : TermFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b1) b0) v (.space (.tprod sv1 sv0)))
    (ihI0 : TermFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b0)) (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : TermFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b1)) (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1))) :
    TermFactsSubctx orc ∅ Gamma Psi
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (.tprod (.dual b0) b1) (.gpinv v env1 env0)
      (.space (.tprod sv0 sv1)) := by
  refine ⟨arm_pinvT_gpinv ht hbv hTy he hi0 hi1 ihTy ihE ihI0 ihI1,?_⟩
  intro sv hsv Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hsv
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle hc
  have hshape : ValSpace.shpOfPartial (orc rho [] []) (.tprod sv0 sv1) =
      .ok [Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual] using targetDims
  obtain ⟨hd0,hd1⟩ := tprod_shape_factors hshape
  have hinshape := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  have hinputshape : (.tprod sv1 sv0 : ValSpace).shpOfPartial (orc rho [] []) =
      .ok [Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier] := by
    simp [ValSpace.shpOfPartial,hd0,hd1,bind,Except.bind,pure,Except.pure]
  rw [hinputshape] at hinshape
  obtain ⟨sa,sb,hinfer,ha,hb⟩ := infer_tprod_of_partial_shape hinshape
  simp only [ValExpr.inferSpaceCtx,hinfer]
  rw [hshape]
  simp [ValSpace.shpOfPartial,ha,hb,bind,Except.bind,pure,Except.pure]

private theorem std_real_basis_eq_one_gpinv
    {Gamma : NLCtx} {b : Basis} (hb : BasisValid Gamma b)
    (hstd : Basis.isStd b) (hsof : Basis.sof b = .real) : b = .one := by
  cases hb <;> simp_all [Basis.sof,Basis.isStd]

theorem arm_pinvD_gpinv
    {orc : PartialFFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {sv1 : ValSpace}
    (hsofb0 : Basis.sof b0 = .real)
    (hb0std : Basis.isStd b0)
    (_ht : Nonempty (HasType ∅ Gamma (.pinvD (Basis.sof b1) e)
      (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (_hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (_he : S.Term ∅ Gamma Psi e (.dual b1) v (.space sv1))
    (_hi0 : S.Term ∅ Gamma Psi (.inner (Basis.sof b0))
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod .real .real)))
    (_hi1 : S.Term ∅ Gamma Psi (.inner (Basis.sof b1))
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihTy : MTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (ihE : TermFactsSubctx orc ∅ Gamma Psi e (.dual b1) v
      (.space sv1))
    (ihI0 : TermFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b0)) (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod .real .real)))
    (ihI1 : TermFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b1)) (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1))) :
    MTermSubctx orc ∅ Gamma Psi
      (.pinvD (Basis.sof b1) e) (.tprod (.dual b0) b1)
      (.gpinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1))
        env1 env0) (.space (.tprod .real sv1)) := by
  obtain ⟨hb0dualv, hb1v⟩ := hbv.tprod_inv
  have hb0v := hb0dualv.dual_inv
  have hb1tof : Basis.tof b1 = .space (Basis.sof b1) := by
    cases hbv with
    | tprod _ _ _ htof1 => exact htof1
  have hb0eq : b0 = .one :=
    std_real_basis_eq_one_gpinv hb0v hb0std hsofb0
  subst b0
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V := denotSpace sigma (Basis.sof b1)
  let S := (denotBasis sigma b1).atSpace V
  have targetDims : DimsAt orc sigma rho [] [] []
      (Basis.tof (.tprod (.dual (.one : Basis)) b1))
      (.space (.tprod .real sv1))
      (denotBasis sigma (.tprod (.dual (.one : Basis)) b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have trE := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI0 := ihI0.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI1 := ihI1.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have hlb : IsListBasis V S :=
    denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlbd := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b1)
    (raw_basisValid_mono (.dual hb1v hb1tof) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb0 := denotBasis_atSpace_isListBasis sigma Gamma' (.one : Basis)
    (raw_basisValid_mono
      (Basis.BasisValid.one : BasisValid Gamma (.one : Basis)) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb0d := denotBasis_atSpace_isListBasis sigma Gamma'
    (.dual (.one : Basis))
    (raw_basisValid_mono
      (.dual (Basis.BasisValid.one : BasisValid Gamma (.one : Basis)) (by rfl)) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hshape : ValSpace.shpOfPartial (orc rho [] []) (.tprod .real sv1) =
      .ok [Module.finrank ℝ HSpace.real.carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual,denotSpace,denotSpaceAux] using targetDims
  have hd1 := (tprod_shape_factors hshape).2
  simp only [denotSpace] at hd1
  rw [hlb.finrank_eq] at hd1
  have harg : ResultAgree orc sigma rho [] [] []
      (.space (.dual (Basis.sof b1))) (.space sv1)
      (.vecs (HSpace.dual (denotSpace sigma (Basis.sof b1)))
        ((denotSpace sigma (Basis.sof b1)).dualOfList
          ((denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b1)))))
      (denotTerm sigma e) (denotValB_partial orc rho [] [] v) := by
    obtain ⟨v',hv,hagree⟩ := trE.result
    refine ⟨v',hv,?_⟩
    cases v' with
    | fn _ _ => simp only [Basis.tof,Agree] at hagree
    | array a =>
      simpa only [Basis.tof,Basis.sof,Agree,denotSpaceAux,
        RawSpaceFFS.denotBasis_dual_atSpace,BasisDenot.atSpace_vecs_self] using hagree
  obtain ⟨ag,hg,hgl,hG⟩ := trace_inner_matrix hlb hlbd trI1
  obtain ⟨ah,hh,hhl,hH⟩ := trace_inner_matrix hlb0 hlb0d trI0
  have hgd : ∃ d, (ValExpr.inferSpaceCtx [] env1).dofPartial (orc rho [] []) = .ok d := by
    have hi := ihI1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd1,bind,Except.bind,pure,Except.pure]
  have hhd : ∃ d, (ValExpr.inferSpaceCtx [] env0).dofPartial (orc rho [] []) = .ok d := by
    have hi := ihI0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,ValSpace.dofPartial,bind,Except.bind,pure,Except.pure]
  have hout := gpinv_dual hlb hg hh hgd hhd
    (by simpa only [pow_two] using hgl)
    (by simpa only [Basis.sof,denotSpace,denotSpaceAux,denotBasis,
      BasisDenot.atSpace_vecs_self,List.length_cons,List.length_nil,pow_two] using hhl)
    hG (by
      simp only [Basis.sof,denotSpace,denotSpaceAux] at hH
      have hone : (denotBasis sigma (.one : Basis)).atSpace HSpace.real = [(1 : ℝ)] := by
        simp only [denotBasis,BasisDenot.atSpace_vecs_self]
      rw [hone] at hH
      exact hH) hd1 harg
  refine ⟨?_,targetDims⟩
  obtain ⟨v',hv,hagree⟩ := hout
  refine ⟨v',hv,?_⟩
  cases v' with
  | fn _ _ => simp only [Agree] at hagree
  | array a =>
    simp only [Basis.tof,Basis.sof,Agree,denotSpaceAux]
    simp only [denotBasis,Basis.sof,denotSpace,denotSpaceAux,BasisDenot.atSpace_vecs_self]
    simpa only [Agree,denotSpaceAux,BasisDenot.atSpace_vecs_self,
      denotTerm,denotTermAux] using hagree

theorem arm_pinvD_gpinv_facts
    {orc : PartialFFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {sv1 : ValSpace}
    (hsofb0 : Basis.sof b0 = .real)
    (hb0std : Basis.isStd b0)
    (ht : Nonempty (HasType ∅ Gamma (.pinvD (Basis.sof b1) e)
      (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (he : S.Term ∅ Gamma Psi e (.dual b1) v (.space sv1))
    (hi0 : S.Term ∅ Gamma Psi (.inner (Basis.sof b0))
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod .real .real)))
    (hi1 : S.Term ∅ Gamma Psi (.inner (Basis.sof b1))
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihTy : MTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (ihE : TermFactsSubctx orc ∅ Gamma Psi e (.dual b1) v
      (.space sv1))
    (ihI0 : TermFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b0)) (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod .real .real)))
    (ihI1 : TermFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b1)) (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1))) :
    TermFactsSubctx orc ∅ Gamma Psi
      (.pinvD (Basis.sof b1) e) (.tprod (.dual b0) b1)
      (.gpinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1))
        env1 env0) (.space (.tprod .real sv1)) := by
  refine ⟨arm_pinvD_gpinv hsofb0 hb0std ht hbv hTy he hi0 hi1 ihTy ihE ihI0 ihI1,?_⟩
  intro sv hsv Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hsv
  rfl

end GLang.PartialAdequacy
