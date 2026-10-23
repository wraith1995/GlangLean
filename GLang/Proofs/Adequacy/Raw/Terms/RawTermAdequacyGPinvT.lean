import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyPinv

/-!
# Raw adequacy for the generalized tensor pseudo-inverse

The matrix operand is read in the exact denoted domain/codomain bases, while
the two inner-product operands are read as the corresponding Gram matrices.
The corrected Gram-weighted GSVD bridge then identifies the value-level
matrix with the intrinsic Moore inverse used by the source denotation.
-/

namespace GLang

open scoped BigOperators Matrix TensorProduct
open Basis (BasisValid)

namespace RawTermGPinvT

/-- Flatten the generalized Moore inverse in the row-major tensor basis used
by the value semantics. -/
theorem mooreTensor_eq_flat_gpinv_sum
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) :
    (dualTensorHomEquiv ℝ V1.carrier V0.carrier).symm
        (LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f) =
      ∑ k : Fin (vs1.length * vs0.length),
        matrixAsDenot
          (matrixGSVDPinv (hb0.coordMatrix hb1 f)
            (IsListBasis.gram V0 vs0) (IsListBasis.gram V1 vs1)).transpose
          k.val •
          (HSpace.tprodOfLists (HSpace.dual V1) V0
            (V1.dualOfList vs1) vs0).getD k.val 0 := by
  rw [hb0.pinvTensor_eq_matrixGSVDPinv_sum hb1 f]
  simpa only [Matrix.transpose_apply] using
    (RawTermPinv.matrixAsDenot_tprod_sum vs1 vs0
      (matrixGSVDPinv (hb0.coordMatrix hb1 f)
        (IsListBasis.gram V0 vs0)
        (IsListBasis.gram V1 vs1)).transpose).symm

end RawTermGPinvT

/-! ## Constructor arm -/

/-- Ordinary exact-basis trace for the generalized tensor pseudo-inverse. -/
theorem arm_pinvT_gpinv
    {orc : FFSOracleSem}
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
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b1) b0) v (.space (.tprod sv1 sv0)))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b0)) (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b1)) (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1))) :
    RawMTermTraceSubctx orc ∅ Gamma Psi
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
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof (.tprod (.dual b0) b1))
      (.space (.tprod sv0 sv1))
      (denotBasis sigma (.tprod (.dual b0) b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have targetShape : ValSpace.shpOf (orc rho [] []) (.tprod sv0 sv1) =
      srcShp sigma []
        (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)) := by
    simpa only [Basis.tof, Basis.sof, RawAgreeDimsAt] using targetDims
  rw [ValSpace.shpOf_tprod,
    RawSpaceFFS.srcShp_tprod_dual] at targetShape
  have hdsv0 : ValSpace.dof (orc rho [] []) sv0 =
      Module.finrank ℝ V0.carrier := by
    injection targetShape
  have hdsv1 : ValSpace.dof (orc rho [] []) sv1 =
      Module.finrank ℝ V1.carrier := by
    injection targetShape with _ htail
    injection htail
  have hlen0 : S0.length = ValSpace.dof (orc rho [] []) sv0 :=
    hlb0.finrank_eq.symm.trans hdsv0.symm
  have hlen1 : S1.length = ValSpace.dof (orc rho [] []) sv1 :=
    hlb1.finrank_eq.symm.trans hdsv1.symm
  have hdshape := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨sa, sb, hinfer⟩ := eq_tprod_of_shpOf_eq hdshape
  rw [hinfer] at hdshape
  have hfac := tprod_factor_dof_eq_of_shpOf_eq hdshape
  obtain ⟨ae, heval, haelen, hM⟩ :=
    RawTermEmbed.trace_witness_matrix hlb1 hlb0 trE
  have trI0' : RawTermTraceAt orc sigma rho env0
      (Basis.tof (.tprod (.dual b0) (.dual b0)))
      (.space (.tprod sv0 sv0))
      (denotBasis sigma (.tprod (.dual b0) (.dual b0)))
      (denotTerm sigma (.inner (Basis.sof b0))) := trI0
  have trI1' : RawTermTraceAt orc sigma rho env1
      (Basis.tof (.tprod (.dual b1) (.dual b1)))
      (.space (.tprod sv1 sv1))
      (denotBasis sigma (.tprod (.dual b1) (.dual b1)))
      (denotTerm sigma (.inner (Basis.sof b1))) := trI1
  obtain ⟨a0, h0eval, ha0len, hG0⟩ :=
    RawTermEmbed.trace_inner_matrix hlb0 hlb0d trI0'
  obtain ⟨a1, h1eval, ha1len, hG1⟩ :=
    RawTermEmbed.trace_inner_matrix hlb1 hlb1d trI1'
  have hd0 : ValSpace.dof (orc rho [] []) sa = S1.length :=
    hfac.1.trans hlen1.symm
  have hd1 : ValSpace.dof (orc rho [] []) sb = S0.length :=
    hfac.2.trans hlen0.symm
  have haeshape : ae.length =
      ValSpace.dof (orc rho [] []) sa *
        ValSpace.dof (orc rho [] []) sb := by
    rw [hd0, hd1]
    exact haelen
  have ha0shape : a0.length = S0.length * S0.length := by
    simpa only [pow_two] using ha0len
  have ha1shape : a1.length = S1.length * S1.length := by
    simpa only [pow_two] using ha1len
  have hgpinvShape : GSVDInputsShape
      (ValSpace.dof (orc rho [] []) sa)
      (ValSpace.dof (orc rho [] []) sb) ae a1 a0 := by
    refine ⟨haeshape, ?_, ?_⟩
    · rw [hd0]
      exact ha1shape
    · rw [hd1]
      exact ha0shape
  have hTensor := RawTermGPinvT.mooreTensor_eq_flat_gpinv_sum hlb1 hlb0 f
  rw [← hM, ← hG1, ← hG0] at hTensor
  have hEval : denotValB_semS orc rho [] [] (.gpinv v env1 env0) =
      .ok (.array (FlatArray.ofFn
        (ValSpace.dof (orc rho [] []) (.tprod sv0 sv1))
        (matrixAsDenot
          (matrixGSVDPinv
            (denotAsMatrix
              (ValSpace.dof (orc rho [] []) sv1)
              (ValSpace.dof (orc rho [] []) sv0) ae.get).transpose
            (denotAsMatrix
              (ValSpace.dof (orc rho [] []) sv1)
              (ValSpace.dof (orc rho [] []) sv1) a1.get)
            (denotAsMatrix
              (ValSpace.dof (orc rho [] []) sv0)
              (ValSpace.dof (orc rho [] []) sv0) a0.get)).transpose))) := by
    rw [denotValB_semS.eq_24, heval, h1eval, h0eval]
    simp only [ValValSem.bindArrays3, ValValSem.bindArray,
      ValExpr.inferSpaceCtx, hinfer,
      ValSpace.dof_tprod, ValValSem.arrayOf]
    rw [if_pos hgpinvShape]
    rw [hfac.1, hfac.2]
  refine ⟨⟨_, hEval, ?_⟩, targetDims⟩
  simp only [Basis.tof, Basis.sof, RawAgree]
  rw [LegacyAgree.space_iff]
  simp only [denotSpaceAux]
  rw [RawSpaceFFS.denotBasis_tprod_dual_atSpace]
  refine ⟨?_, FlatArray.length_ofFn _ _, ?_⟩
  · rw [HSpace.tprodOfLists_length, HSpace.dualOfList_length,
      hlen0, hlen1, ValSpace.dof_tprod]
  · simp only [denotTerm, denotTermAux, pinvTensorDVal,
      DVal.atSpace_hil_self]
    rw [hTensor]
    simp only [denotSpace]
    rw [ValSpace.dof_tprod, ← hlen0, ← hlen1]
    apply Finset.sum_congr rfl
    intro k _
    rw [FlatArray.get_ofFn_lt _ _ _ k.isLt]
    rfl

/-- Paired direct-mutual conclusion for the generalized tensor arm. -/
theorem arm_pinvT_gpinv_facts
    {orc : FFSOracleSem}
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
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b1) b0) v (.space (.tprod sv1 sv0)))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b0)) (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b1)) (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1))) :
    RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (.tprod (.dual b0) b1) (.gpinv v env1 env0)
      (.space (.tprod sv0 sv1)) :=
  ⟨arm_pinvT_gpinv ht hbv hTy he hi0 hi1 ihTy ihE ihI0 ihI1,
    arm_pinvT_gpinv_dof ihE.dof⟩

end GLang
