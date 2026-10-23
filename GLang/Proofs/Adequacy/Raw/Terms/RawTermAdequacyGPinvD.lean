import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyPinv

/-!
# Raw generalized pseudo-inverse for a dual operand

The generalized dual rule is constructive once its one-dimensional
codomain basis is canonical.  This module records that exact theorem so the
remaining rule boundary is explicit: an arbitrary basis of `real` must first
be reached by the ordinary change-of-basis rule.
-/

namespace GLang

open scoped BigOperators Matrix TensorProduct
open Basis (BasisValid)

namespace RawTermGPinvD

private theorem eq_one_of_valid_sof_real
    {Gamma : NLCtx} {b : Basis} (hb : BasisValid Gamma b)
    (hstd : Basis.isStd b) (hsof : Basis.sof b = .real) : b = .one := by
  cases hb <;> simp_all [Basis.sof, Basis.isStd]

private theorem asLinFunctional_eq_atSpace (V : HSpace) (d : DVal) :
    d.asLinFunctional V = d.atSpace (HSpace.dual V) := by
  unfold DVal.asLinFunctional DVal.atSpace
  obtain ⟨Vt, t⟩ := d.asHil
  by_cases h : Vt.carrier = (V.carrier →ₗ[ℝ] ℝ)
  · simp only [h, dif_pos]
  · simp only [h, dif_neg]

private theorem coordMatrix_functional_eq
    {V : HSpace} {vs : List V.carrier}
    (hb : IsListBasis V vs) (a : Nat → ℝ)
    (phi : V.carrier →ₗ[ℝ] ℝ)
    (hphi : phi = ∑ i : Fin vs.length,
      a i.val • (V.dualOfList vs).getD i.val 0) :
    hb.coordMatrix isListBasis_one phi =
      (denotAsMatrix vs.length 1 a).transpose := by
  classical
  have hphiAt (j : Fin vs.length) : phi (vs.get j) = a j.val := by
    rw [hphi, LinearMap.sum_apply]
    calc
      (∑ i : Fin vs.length,
          (a i.val • (V.dualOfList vs).getD i.val 0) (vs.get j)) =
          ∑ i : Fin vs.length, a i.val * (if i = j then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [LinearMap.smul_apply,
          RawSpaceFFS.dualOfList_getD_eq_dualVec V vs i.isLt,
          hb.dual_delta i j]
        rfl
      _ = a j.val := by simp
  apply Matrix.ext
  intro i j
  change Fin 1 at i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  have hreal0 : isListBasis_one.coords (phi (vs.get j)) (0 : Fin 1) =
      phi (vs.get j) := by
    have hreal := isListBasis_one.sum_coords_smul (phi (vs.get j))
    simpa using hreal
  rw [IsListBasis.coordMatrix, LinearMap.toMatrix_apply,
    IsListBasis.toBasis_apply]
  change isListBasis_one.coords (phi (vs.get j)) (0 : Fin 1) =
    a (1 * j.val + 0)
  rw [hreal0, hphiAt]
  simp

private theorem matrixAsDenot_tprod_sum
    {V0 V1 : HSpace} (vs0 : List V0.carrier) (vs1 : List V1.carrier)
    (M : Matrix (Fin vs0.length) (Fin vs1.length) ℝ) :
    (∑ k : Fin (vs0.length * vs1.length),
      matrixAsDenot M k.val •
        (HSpace.tprodOfLists (HSpace.dual V0) V1
          (V0.dualOfList vs0) vs1).getD k.val 0) =
      ∑ i : Fin vs0.length, ∑ j : Fin vs1.length,
        M i j • (V0.dualVec vs0 i ⊗ₜ[ℝ] vs1.get j) := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  have hk :
      ((finProdFinEquiv (i, j) : Fin (vs0.length * vs1.length)) : Nat) =
        j.val + vs1.length * i.val := rfl
  have hpos : 0 < vs1.length := Nat.zero_lt_of_lt j.isLt
  have hlt : j.val + vs1.length * i.val <
      (V0.dualOfList vs0).length * vs1.length := by
    rw [HSpace.dualOfList_length]
    exact (finProdFinEquiv (i, j)).isLt
  obtain ⟨hdiv, hmod⟩ := RawSpaceFFS.rowMajor_div_mod
    (i := i.val) j.isLt
  rw [hk, RawSpaceFFS.tprodOfLists_getD _ _ _ _ _ hlt hpos,
    hdiv, hmod,
    RawSpaceFFS.dualOfList_getD_eq_dualVec V0 vs0 i.isLt,
    List.getD_eq_getElem vs1 0 j.isLt]
  simp [matrixAsDenot, Nat.ne_of_gt hpos, hdiv, hmod]

private theorem mooreDual_eq_flat_gpinv_sum
    {V : HSpace} {vs : List V.carrier}
    (hb : IsListBasis V vs) (a : Nat → ℝ) (d : DVal)
    (hd : d.atSpace (HSpace.dual V) =
      ∑ i : Fin vs.length,
        a i.val • (V.dualOfList vs).getD i.val 0) :
    (dualTensorHomEquiv ℝ ℝ V.carrier).symm
        (LinearMap.mooreInv V.innerIsIP HSpace.real.innerIsIP
          (d.asLinFunctional V)) =
      ∑ k : Fin (1 * vs.length),
        matrixAsDenot
          (matrixGSVDPinv
            (denotAsMatrix vs.length 1 a).transpose
            (IsListBasis.gram V vs)
            (IsListBasis.gram HSpace.real [(1 : ℝ)] )).transpose k.val •
          (HSpace.tprodOfLists (HSpace.dual HSpace.real) V
            (HSpace.real.dualOfList [(1 : ℝ)]) vs).getD k.val 0 := by
  have hphi : d.asLinFunctional V =
      ∑ i : Fin vs.length,
        a i.val • (V.dualOfList vs).getD i.val 0 :=
    (asLinFunctional_eq_atSpace V d).trans hd
  have hcoord := coordMatrix_functional_eq hb a
    (d.asLinFunctional V) hphi
  rw [hb.pinvTensor_eq_matrixGSVDPinv_sum isListBasis_one, hcoord]
  simpa only [Matrix.transpose_apply] using
    (matrixAsDenot_tprod_sum (V0 := HSpace.real) (V1 := V)
      [(1 : ℝ)] vs
      (matrixGSVDPinv
        (denotAsMatrix vs.length 1 a).transpose
        (IsListBasis.gram V vs)
        (IsListBasis.gram HSpace.real [(1 : ℝ)])).transpose).symm

end RawTermGPinvD

/-! ## The corrected direct arm boundary -/

/-- The current generalized dual rule is adequate when its scalar output
basis is canonical.  For an arbitrary scalar basis, evaluate here first and
then transport the result with the ordinary COB rule. -/
theorem arm_pinvD_gpinv_of_std_codomain
    {orc : FFSOracleSem}
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
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e (.dual b1) v
      (.space sv1))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b0)) (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod .real .real)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b1)) (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1))) :
    RawMTermTraceSubctx orc ∅ Gamma Psi
      (.pinvD (Basis.sof b1) e) (.tprod (.dual b0) b1)
      (.gpinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1))
        env1 env0) (.space (.tprod .real sv1)) := by
  obtain ⟨hb0dualv, hb1v⟩ := hbv.tprod_inv
  have hb0v := hb0dualv.dual_inv
  have hb1tof : Basis.tof b1 = .space (Basis.sof b1) := by
    cases hbv with
    | tprod _ _ _ htof1 => exact htof1
  have hb0eq : b0 = .one :=
    RawTermGPinvD.eq_one_of_valid_sof_real hb0v hb0std hsofb0
  subst b0
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V := denotSpace sigma (Basis.sof b1)
  let S := (denotBasis sigma b1).atSpace V
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
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
  obtain ⟨a, haEval, _haBasisLen, haLen, haCoords⟩ :=
    RawSpaceFFS.trace_array_coords (b := .dual b1) (by rfl) trE
  have hshape : ValSpace.shpOf (orc rho [] []) (.tprod .real sv1) =
      srcShp sigma [] (.tprod (.dual (.real : Space)) (Basis.sof b1)) := by
    simpa only [Basis.tof, Basis.sof, RawAgreeDimsAt] using targetDims
  rw [ValSpace.shpOf_tprod, RawSpaceFFS.srcShp_tprod_dual] at hshape
  have hd1 : ValSpace.dof (orc rho [] []) sv1 =
      Module.finrank ℝ V.carrier :=
    (List.cons.inj (List.cons.inj hshape).2).1
  have hlen : S.length = ValSpace.dof (orc rho [] []) sv1 :=
    hlb.finrank_eq.symm.trans hd1.symm
  change (denotTerm sigma e).atSpace (HSpace.dual V) =
    ∑ i : Fin (ValSpace.dof (orc rho [] []) sv1),
      a.get i.val •
        ((denotBasis sigma (.dual b1)).atSpace (HSpace.dual V)).getD
          i.val 0 at haCoords
  rw [← hlen, RawSpaceFFS.denotBasis_dual_atSpace] at haCoords
  have hDual := RawTermGPinvD.mooreDual_eq_flat_gpinv_sum
    hlb a.get (denotTerm sigma e) haCoords
  have trI0' : RawTermTraceAt orc sigma rho env0
      (Basis.tof (.tprod (.dual (.one : Basis)) (.dual (.one : Basis))))
      (.space (.tprod .real .real))
      (denotBasis sigma (.tprod (.dual (.one : Basis)) (.dual (.one : Basis))))
      (denotTerm sigma (.inner (.real : Space))) := trI0
  have trI1' : RawTermTraceAt orc sigma rho env1
      (Basis.tof (.tprod (.dual b1) (.dual b1)))
      (.space (.tprod sv1 sv1))
      (denotBasis sigma (.tprod (.dual b1) (.dual b1)))
      (denotTerm sigma (.inner (Basis.sof b1))) := trI1
  obtain ⟨a0, h0Eval, h0Len, hMV⟩ :=
    RawTermEmbed.trace_inner_matrix hlb0 hlb0d trI0'
  obtain ⟨a1, h1Eval, h1Len, hMW⟩ :=
    RawTermEmbed.trace_inner_matrix hlb hlbd trI1'
  have h0BasisLen :
      ((denotBasis sigma (.one : Basis)).atSpace
        (denotSpace sigma (Basis.sof (.one : Basis)))).length = 1 := by
    rw [show denotSpace sigma (Basis.sof (.one : Basis)) =
      HSpace.real from rfl]
    have hbOne : denotBasis sigma (.one : Basis) =
        .vecs HSpace.real [(1 : ℝ)] := by
      simp [denotBasis]
    rw [hbOne, BasisDenot.atSpace_vecs_self]
    rfl
  have haShape : a.length =
      ValSpace.dof (orc rho [] []) sv1 * 1 := by
    simpa only [Nat.mul_one] using haLen
  have h1Shape : a1.length =
      ValSpace.dof (orc rho [] []) sv1 *
        ValSpace.dof (orc rho [] []) sv1 := by
    rw [← hlen]
    simpa only [pow_two] using h1Len
  have h0Shape : a0.length = 1 * 1 := by
    rw [h0BasisLen] at h0Len
    simpa only [pow_two] using h0Len
  have hgpinvShape : GSVDInputsShape
      (ValSpace.dof (orc rho [] []) sv1) 1 a a1 a0 :=
    ⟨haShape, h1Shape, h0Shape⟩
  have hMV' : denotAsMatrix 1 1 a0.get =
      IsListBasis.gram HSpace.real [(1 : ℝ)] := by
    rw [show denotSpace sigma (Basis.sof (.one : Basis)) =
      HSpace.real from rfl] at hMV
    have hbOne : denotBasis sigma (.one : Basis) =
        .vecs HSpace.real [(1 : ℝ)] := by
      simp [denotBasis]
    rw [hbOne, BasisDenot.atSpace_vecs_self] at hMV
    exact hMV
  have hMW' : denotAsMatrix S.length S.length a1.get =
      IsListBasis.gram V S := by
    simpa only [V, S, denotSpace] using hMW
  have hreshape : denotValB_semS orc rho [] []
      (.reshap v (.space (.tprod sv1 .real)) (.space sv1)) =
      .ok (.array a) := by
    apply denotValB_semS_reshap_spaces_ok
    · exact haEval
    · exact haLen
    · simp only [ValSpace.dof_tprod, ValSpace.dof_real, Nat.mul_one]
  have hEval : denotValB_semS orc rho [] []
      (.gpinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1))
        env1 env0) =
      .ok (.array (FlatArray.ofFn
        (ValSpace.dof (orc rho [] []) (.tprod .real sv1))
        (matrixAsDenot
          (matrixGSVDPinv
            (denotAsMatrix (ValSpace.dof (orc rho [] []) sv1) 1 a.get).transpose
            (denotAsMatrix (ValSpace.dof (orc rho [] []) sv1)
              (ValSpace.dof (orc rho [] []) sv1) a1.get)
            (denotAsMatrix 1 1 a0.get)).transpose))) := by
    rw [denotValB_semS.eq_24, hreshape, h1Eval, h0Eval]
    simp only [ValValSem.bindArrays3, ValValSem.bindArray,
      ValExpr.inferSpaceCtx,
      ValTy.spaceOf, ValSpace.dof_tprod, ValSpace.dof_real,
      ValValSem.arrayOf]
    rw [ValSpace.dof_real (orc rho [] [])]
    rw [if_pos hgpinvShape]
  refine ⟨⟨_, hEval, ?_⟩, targetDims⟩
  simp only [Basis.tof, Basis.sof, RawAgree]
  rw [LegacyAgree.space_iff]
  change
    ((denotBasis sigma (.tprod (.dual (.one : Basis)) b1)).atSpace
      (HSpace.tprod (HSpace.dual HSpace.real) V)).length = _ ∧ _
  have hBasisOut := RawSpaceFFS.denotBasis_tprod_dual_atSpace
    sigma (.one : Basis) b1
  change
    (denotBasis sigma (.tprod (.dual (.one : Basis)) b1)).atSpace
        (HSpace.tprod (HSpace.dual (denotSpace sigma (.real : Space)))
          (denotSpace sigma (Basis.sof b1))) =
      HSpace.tprodOfLists
        (HSpace.dual (denotSpace sigma (.real : Space)))
        (denotSpace sigma (Basis.sof b1))
        ((denotSpace sigma (.real : Space)).dualOfList
          ((denotBasis sigma (.one : Basis)).atSpace
            (denotSpace sigma (.real : Space))))
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1))) at hBasisOut
  have hBasisOut' :
      (denotBasis sigma (.tprod (.dual (.one : Basis)) b1)).atSpace
          (HSpace.tprod (HSpace.dual HSpace.real) V) =
        HSpace.tprodOfLists (HSpace.dual HSpace.real) V
          (HSpace.real.dualOfList [(1 : ℝ)]) S := by
    simpa only [V, S, denotSpace, denotSpaceAux, denotBasis,
      BasisDenot.atSpace_vecs_self] using hBasisOut
  refine ⟨?_, ?_, ?_⟩
  · rw [hBasisOut', HSpace.tprodOfLists_length,
      HSpace.dualOfList_length, hlen, ValSpace.dof_tprod,
      ValSpace.dof_real]
    rfl
  · rw [FlatArray.length_ofFn]
  · have hTargetSpace :
        denotSpaceAux sigma []
            (.tprod (.dual (.real : Space)) (Basis.sof b1)) =
          HSpace.tprod (HSpace.dual HSpace.real) V := rfl
    rw [hTargetSpace]
    simp only [V, denotTerm, denotTermAux, pinvDualDVal,
      DVal.atSpace_hil_self]
    change
      (dualTensorHomEquiv ℝ ℝ V.carrier).symm
          (LinearMap.mooreInv V.innerIsIP HSpace.real.innerIsIP
            ((denotTerm sigma e).asLinFunctional V)) = _
    rw [hDual, hBasisOut']
    rw [ValSpace.dof_tprod, ValSpace.dof_real, ← hlen]
    rw [hMW', hMV']
    simp only [V, S, denotSpace]
    apply Finset.sum_congr rfl
    intro k _
    rw [FlatArray.get_ofFn_lt _ _ _ k.isLt]

/-- Paired dof facts for the corrected generalized dual boundary. -/
theorem arm_pinvD_gpinv_of_std_codomain_facts
    {orc : FFSOracleSem}
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
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e (.dual b1) v
      (.space sv1))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b0)) (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod .real .real)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.inner (Basis.sof b1)) (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1))) :
    RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.pinvD (Basis.sof b1) e) (.tprod (.dual b0) b1)
      (.gpinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1))
        env1 env0) (.space (.tprod .real sv1)) :=
  ⟨arm_pinvD_gpinv_of_std_codomain hsofb0 hb0std ht hbv hTy he hi0 hi1
      ihTy ihE ihI0 ihI1,
    arm_pinvD_gpinv_dof⟩

end GLang
