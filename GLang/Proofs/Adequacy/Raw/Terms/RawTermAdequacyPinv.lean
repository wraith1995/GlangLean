import GLang.Proofs.Adequacy.Raw.RawSpaceFFSAdequacy
import GLang.Proofs.Adequacy.Raw.RawDofAdequacyCore
import GLang.Proofs.Adequacy.Raw.RawPinvCoordinateBridge
import GLang.Proofs.Adequacy.Raw.RawGPinvCoordinateBridge
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyEmbed

/-!
# Raw adequacy for pseudo-inverse terms

The standard-coordinate arms are constructive consequences of the existing
matrix SVD Moore--Penrose laws.  The helpers below make the row-major
transpose explicit, then lift the resulting coordinate identity back through
the tensor basis used by `RawAgree`.
-/

namespace GLang

open scoped BigOperators Matrix TensorProduct
open Basis (BasisValid)

namespace RawTermPinv

/-- A valid basis whose source space is literally `real` is the canonical
one-element basis.  In particular, the syntactically standard `pinvD` rule
does not hide an arbitrary sign choice for the scalar coordinate. -/
private theorem eq_one_of_valid_sof_real
    {Gamma : NLCtx} {b : Basis} (hb : BasisValid Gamma b)
    (hstd : Basis.isStd b) (hsof : Basis.sof b = .real) : b = .one := by
  cases hb <;> simp_all [Basis.sof, Basis.isStd]

/-- Reading a dual-shaped `DVal` as a functional agrees with projecting it
to the dual carrier, including in the mismatch branch (both sides are zero). -/
private theorem asLinFunctional_eq_atSpace (V : HSpace) (d : DVal) :
    d.asLinFunctional V = d.atSpace (HSpace.dual V) := by
  unfold DVal.asLinFunctional DVal.atSpace
  obtain ⟨Vt, t⟩ := d.asHil
  by_cases h : Vt.carrier = (V.carrier →ₗ[ℝ] ℝ)
  · simp only [h, dif_pos]
  · simp only [h, dif_neg]

/-- A flat expansion in the dual list basis is the column matrix consumed
by the value semantics after the `pinvD` reshape to `V ⊗ real`. -/
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
          ∑ i : Fin vs.length,
            a i.val * (if i = j then 1 else 0) := by
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

/-- Coordinate matrix of a tensor from its flat row-major expansion in a
dual/product list basis. -/
private theorem coordMatrix_eq_of_tensor_coords
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (a : Nat → ℝ) (t : (HSpace.tprod (HSpace.dual V0) V1).carrier)
    (ht : t = ∑ k : Fin (vs0.length * vs1.length),
      a k.val • (HSpace.tprodOfLists (HSpace.dual V0) V1
        (V0.dualOfList vs0) vs1).getD k.val 0) :
    hb0.coordMatrix hb1 (dualTensorHom ℝ V0.carrier V1.carrier t) =
      (denotAsMatrix vs0.length vs1.length a).transpose := by
  apply RawSpaceFFS.coordMatrix_eq_denotAsMatrix_transpose_of_dualBasis
    hb0 hb1 _ a (V0.dualVec vs0)
  · intro i j
    exact hb0.dual_delta i j
  · intro u
    rw [ht, map_sum, LinearMap.sum_apply,
      ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
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
    rw [hk, map_smul, LinearMap.smul_apply,
      RawSpaceFFS.tprodOfLists_getD _ _ _ _ _ hlt hpos,
      hdiv, hmod, dualTensorHom_apply,
      RawSpaceFFS.dualOfList_getD_eq_dualVec V0 vs0 i.isLt,
      List.getD_eq_getElem vs1 0 j.isLt, smul_smul, Nat.add_comm]
    rfl

/-- Flattening a rectangular matrix and expanding in the row-major product
basis is the same as its two-index tensor expansion. -/
theorem matrixAsDenot_tprod_sum
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

/-- Exact tensor statement consumed by both standard pseudo-inverse arms. -/
private theorem mooreTensor_eq_flat_pinv_sum
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (horth0 : ∀ i j : Fin vs0.length,
      V0.innerProduct (vs0.get i) (vs0.get j) = if i = j then 1 else 0)
    (horth1 : ∀ i j : Fin vs1.length,
      V1.innerProduct (vs1.get i) (vs1.get j) = if i = j then 1 else 0)
    (a : Nat → ℝ) (t : (HSpace.tprod (HSpace.dual V0) V1).carrier)
    (ht : t = ∑ k : Fin (vs0.length * vs1.length),
      a k.val • (HSpace.tprodOfLists (HSpace.dual V0) V1
        (V0.dualOfList vs0) vs1).getD k.val 0) :
    (dualTensorHomEquiv ℝ V1.carrier V0.carrier).symm
        (LinearMap.mooreInv V0.innerIsIP V1.innerIsIP
          (dualTensorHom ℝ V0.carrier V1.carrier t)) =
      ∑ k : Fin (vs1.length * vs0.length),
        matrixAsDenot
          (matrixSVDPinv (denotAsMatrix vs0.length vs1.length a)) k.val •
          (HSpace.tprodOfLists (HSpace.dual V1) V0
            (V1.dualOfList vs1) vs0).getD k.val 0 := by
  have hcoord := coordMatrix_eq_of_tensor_coords hb0 hb1 a t ht
  rw [hb0.pinvTensor_eq_matrixSVDPinv_sum hb1 horth0 horth1]
  rw [hcoord, Matrix.transpose_transpose]
  exact (matrixAsDenot_tprod_sum vs1 vs0
    (matrixSVDPinv (denotAsMatrix vs0.length vs1.length a))).symm

/-- Degenerate (`pinvD`) specialization: a covector's flat coefficients are
read as a `dim V × 1` matrix, and its inverse lands in `real* ⊗ V`. -/
private theorem mooreDual_eq_flat_pinv_sum
    {V : HSpace} {vs : List V.carrier}
    (hb : IsListBasis V vs)
    (horth : ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0)
    (a : Nat → ℝ) (d : DVal)
    (hd : d.atSpace (HSpace.dual V) =
      ∑ i : Fin vs.length,
        a i.val • (V.dualOfList vs).getD i.val 0) :
    (dualTensorHomEquiv ℝ ℝ V.carrier).symm
        (LinearMap.mooreInv V.innerIsIP HSpace.real.innerIsIP
          (d.asLinFunctional V)) =
      ∑ k : Fin (1 * vs.length),
        matrixAsDenot (matrixSVDPinv
          (denotAsMatrix vs.length 1 a)) k.val •
          (HSpace.tprodOfLists (HSpace.dual HSpace.real) V
            (HSpace.real.dualOfList [(1 : ℝ)]) vs).getD k.val 0 := by
  have hphi : d.asLinFunctional V =
      ∑ i : Fin vs.length,
        a i.val • (V.dualOfList vs).getD i.val 0 :=
    (asLinFunctional_eq_atSpace V d).trans hd
  have hcoord := coordMatrix_functional_eq hb a (d.asLinFunctional V) hphi
  have hcoordT :
      (hb.coordMatrix isListBasis_one (d.asLinFunctional V)).transpose =
        denotAsMatrix vs.length 1 a := by
    rw [hcoord]
    ext i j
    rfl
  rw [hb.pinvTensor_eq_matrixSVDPinv_sum isListBasis_one
    horth denotBasis_orthonormal_one, hcoordT]
  exact (matrixAsDenot_tprod_sum (V0 := HSpace.real) (V1 := V)
    [(1 : ℝ)] vs
    (matrixSVDPinv (denotAsMatrix vs.length 1 a))).symm

end RawTermPinv

/-! ## Standard tensor pseudo-inverse -/

theorem arm_pinvT_std
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v : ValExpr}
    {sv0 sv1 : ValSpace}
    (hb0std : Basis.isStd b0) (hb1std : Basis.isStd b1)
    (_ht : Nonempty (HasType ∅ Gamma
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (_hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (_he : S.Term ∅ Gamma Psi e (.tprod (.dual b1) b0) v
      (.space (.tprod sv1 sv0)))
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b1) b0) v (.space (.tprod sv1 sv0))) :
    RawMTermTraceSubctx orc ∅ Gamma Psi
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (.tprod (.dual b0) b1) (.pinv v)
      (.space (.tprod sv0 sv1)) := by
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof (.tprod (.dual b0) b1))
      (.space (.tprod sv0 sv1))
      (denotBasis sigma (.tprod (.dual b0) b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have trace := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨a, haEval, _haBasisLen, haLen, haCoords⟩ :=
    RawSpaceFFS.trace_array_coords (b := .tprod (.dual b1) b0)
      (by rfl) trace
  have hd := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨sa, sb, hinfer⟩ := eq_tprod_of_shpOf_eq hd
  rw [hinfer] at hd
  have hfac := tprod_factor_dof_eq_of_shpOf_eq hd
  obtain ⟨hb0dualv, hb1v⟩ := hbv.tprod_inv
  have hb0v := hb0dualv.dual_inv
  obtain ⟨hlb0, horth0⟩ := denotBasis_std_orthonormal_core
    (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl hb0std
  obtain ⟨hlb1, horth1⟩ := denotBasis_std_orthonormal_core
    (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl hb1std
  have hshape : ValSpace.shpOf (orc rho [] []) (.tprod sv0 sv1) =
      srcShp sigma []
        (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)) := by
    simpa only [Basis.tof, Basis.sof, RawAgreeDimsAt] using targetDims
  rw [ValSpace.shpOf_tprod,
    RawSpaceFFS.srcShp_tprod_dual] at hshape
  have hd0 : ValSpace.dof (orc rho [] []) sv0 =
      Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier :=
    (List.cons.inj hshape).1
  have hd1 : ValSpace.dof (orc rho [] []) sv1 =
      Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier :=
    (List.cons.inj (List.cons.inj hshape).2).1
  have hlen0 : ((denotBasis sigma b0).atSpace
      (denotSpace sigma (Basis.sof b0))).length =
      ValSpace.dof (orc rho [] []) sv0 :=
    hlb0.finrank_eq.symm.trans hd0.symm
  have hlen1 : ((denotBasis sigma b1).atSpace
      (denotSpace sigma (Basis.sof b1))).length =
      ValSpace.dof (orc rho [] []) sv1 :=
    hlb1.finrank_eq.symm.trans hd1.symm
  change (denotTerm sigma e).atSpace
      (HSpace.tprod
        (HSpace.dual (denotSpace sigma (Basis.sof b1)))
        (denotSpace sigma (Basis.sof b0))) =
    ∑ i : Fin (ValSpace.dof (orc rho [] []) (.tprod sv1 sv0)),
      a.get i.val •
        ((denotBasis sigma (.tprod (.dual b1) b0)).atSpace
          (HSpace.tprod
            (HSpace.dual (denotSpace sigma (Basis.sof b1)))
            (denotSpace sigma (Basis.sof b0)))).getD i.val 0 at haCoords
  rw [ValSpace.dof_tprod, ← hlen1, ← hlen0,
    RawSpaceFFS.denotBasis_tprod_dual_atSpace] at haCoords
  have hTensor := RawTermPinv.mooreTensor_eq_flat_pinv_sum
    hlb1 hlb0 horth1 horth0 a.get
    ((denotTerm sigma e).atSpace
      (HSpace.tprod
        (HSpace.dual (denotSpace sigma (Basis.sof b1)))
        (denotSpace sigma (Basis.sof b0)))) haCoords
  rw [← RawSpaceFFS.asLinMap_eq_dualTensorHom_atSpace] at hTensor
  have hEval : denotValB_semS orc rho [] [] (.pinv v) =
      .ok (.array (FlatArray.ofFn
        (ValSpace.dof (orc rho [] []) (.tprod sv0 sv1))
        (matrixAsDenot (matrixSVDPinv
          (denotAsMatrix
            (ValSpace.dof (orc rho [] []) sv1)
            (ValSpace.dof (orc rho [] []) sv0) a.get))))) := by
    rw [denotValB_semS.eq_18, haEval]
    simp only [ValValSem.bindArray, ValExpr.inferSpaceCtx, hinfer,
      ValSpace.dof_tprod, ValValSem.arrayOf]
    have hguard : a.length =
        ValSpace.dof (orc rho [] []) sa * ValSpace.dof (orc rho [] []) sb := by
      simpa only [ValSpace.dof_tprod, hfac.1, hfac.2] using haLen
    rw [if_pos hguard]
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
    simp only [denotSpace]
    apply Finset.sum_congr rfl
    intro k _
    rw [FlatArray.get_ofFn_lt _ _ _ k.isLt]
    rfl

/-- Paired direct-mutual conclusion for the standard tensor arm. -/
theorem arm_pinvT_std_facts
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v : ValExpr}
    {sv0 sv1 : ValSpace}
    (hb0std : Basis.isStd b0) (hb1std : Basis.isStd b1)
    (ht : Nonempty (HasType ∅ Gamma
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b1) b0) v
      (.space (.tprod sv1 sv0)))
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b1) b0) v (.space (.tprod sv1 sv0))) :
    RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (.tprod (.dual b0) b1) (.pinv v)
      (.space (.tprod sv0 sv1)) :=
  ⟨arm_pinvT_std hb0std hb1std ht hbv hTy he ihTy ihE,
    arm_pinvT_std_dof ihE.dof⟩

/-! ## Standard dual pseudo-inverse -/

theorem arm_pinvD_std
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v : ValExpr}
    {sv1 : ValSpace}
    (hsofb0 : Basis.sof b0 = .real)
    (hb0std : Basis.isStd b0) (hb1std : Basis.isStd b1)
    (_ht : Nonempty (HasType ∅ Gamma (.pinvD (Basis.sof b1) e)
      (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (_hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (_he : S.Term ∅ Gamma Psi e (.dual b1) v (.space sv1))
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e (.dual b1) v
      (.space sv1)) :
    RawMTermTraceSubctx orc ∅ Gamma Psi
      (.pinvD (Basis.sof b1) e) (.tprod (.dual b0) b1)
      (.pinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1)))
      (.space (.tprod .real sv1)) := by
  obtain ⟨hb0dualv, hb1v⟩ := hbv.tprod_inv
  have hb0v := hb0dualv.dual_inv
  have hb0eq : b0 = .one :=
    RawTermPinv.eq_one_of_valid_sof_real hb0v hb0std hsofb0
  subst b0
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof (.tprod (.dual (.one : Basis)) b1))
      (.space (.tprod .real sv1))
      (denotBasis sigma (.tprod (.dual (.one : Basis)) b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have trace := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨a, haEval, _haBasisLen, haLen, haCoords⟩ :=
    RawSpaceFFS.trace_array_coords (b := .dual b1) (by rfl) trace
  obtain ⟨hlb1, horth1⟩ := denotBasis_std_orthonormal_core
    (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl hb1std
  have hshape : ValSpace.shpOf (orc rho [] []) (.tprod .real sv1) =
      srcShp sigma [] (.tprod (.dual (.real : Space)) (Basis.sof b1)) := by
    simpa only [Basis.tof, Basis.sof, RawAgreeDimsAt] using targetDims
  rw [ValSpace.shpOf_tprod,
    RawSpaceFFS.srcShp_tprod_dual] at hshape
  have hd1 : ValSpace.dof (orc rho [] []) sv1 =
      Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier :=
    (List.cons.inj (List.cons.inj hshape).2).1
  have hlen1 : ((denotBasis sigma b1).atSpace
      (denotSpace sigma (Basis.sof b1))).length =
      ValSpace.dof (orc rho [] []) sv1 :=
    hlb1.finrank_eq.symm.trans hd1.symm
  change (denotTerm sigma e).atSpace
      (HSpace.dual (denotSpace sigma (Basis.sof b1))) =
    ∑ i : Fin (ValSpace.dof (orc rho [] []) sv1),
      a.get i.val •
        ((denotBasis sigma (.dual b1)).atSpace
          (HSpace.dual (denotSpace sigma (Basis.sof b1)))).getD i.val 0
      at haCoords
  rw [← hlen1, RawSpaceFFS.denotBasis_dual_atSpace] at haCoords
  have hDual := RawTermPinv.mooreDual_eq_flat_pinv_sum
    hlb1 horth1 a.get (denotTerm sigma e) haCoords
  have hreshape : denotValB_semS orc rho [] []
      (.reshap v (.space (.tprod sv1 .real)) (.space sv1)) =
      .ok (.array a) := by
    apply denotValB_semS_reshap_spaces_ok
    · exact haEval
    · exact haLen
    · simp only [ValSpace.dof_tprod, ValSpace.dof_real, Nat.mul_one]
  have hEval : denotValB_semS orc rho [] []
      (.pinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1))) =
      .ok (.array (FlatArray.ofFn
        (ValSpace.dof (orc rho [] []) (.tprod .real sv1))
        (matrixAsDenot (matrixSVDPinv
          (denotAsMatrix (ValSpace.dof (orc rho [] []) sv1) 1 a.get))))) := by
    rw [denotValB_semS.eq_18, hreshape]
    simp only [ValValSem.bindArray, ValExpr.inferSpaceCtx,
      ValTy.spaceOf, ValSpace.dof_tprod, ValSpace.dof_real,
      ValValSem.arrayOf]
    have hguard : a.length = ValSpace.dof (orc rho [] []) sv1 * 1 := by
      simpa only [Nat.mul_one] using haLen
    rw [if_pos hguard]
    rw [ValSpace.dof_real (orc rho [] [])]
  refine ⟨⟨_, hEval, ?_⟩, targetDims⟩
  simp only [Basis.tof, Basis.sof, RawAgree]
  rw [LegacyAgree.space_iff]
  change
    ((denotBasis sigma (.tprod (.dual (.one : Basis)) b1)).atSpace
      (HSpace.tprod (HSpace.dual (denotSpace sigma (.real : Space)))
        (denotSpace sigma (Basis.sof b1)))).length = _ ∧ _
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
          (HSpace.tprod (HSpace.dual HSpace.real)
            (denotSpace sigma (Basis.sof b1))) =
        HSpace.tprodOfLists (HSpace.dual HSpace.real)
          (denotSpace sigma (Basis.sof b1))
          (HSpace.real.dualOfList [(1 : ℝ)])
          ((denotBasis sigma b1).atSpace
            (denotSpace sigma (Basis.sof b1))) := by
    simpa only [denotSpace, denotSpaceAux, denotBasis,
      BasisDenot.atSpace_vecs_self] using hBasisOut
  refine ⟨?_, ?_, ?_⟩
  · rw [show denotSpace sigma (.real : Space) = HSpace.real from rfl,
      hBasisOut', HSpace.tprodOfLists_length,
      HSpace.dualOfList_length, hlen1, ValSpace.dof_tprod,
      ValSpace.dof_real]
    rfl
  · rw [FlatArray.length_ofFn, ValSpace.dof_tprod, ValSpace.dof_real,
      one_mul]
  · have hTargetSpace :
        denotSpaceAux sigma []
            (.tprod (.dual (.real : Space)) (Basis.sof b1)) =
          HSpace.tprod (HSpace.dual HSpace.real)
            (denotSpace sigma (Basis.sof b1)) := rfl
    rw [hTargetSpace]
    simp only [denotTerm, denotTermAux, pinvDualDVal,
      DVal.atSpace_hil_self]
    rw [hDual]
    rw [hBasisOut']
    rw [ValSpace.dof_tprod, ValSpace.dof_real, ← hlen1]
    simp only [denotSpace]
    apply Finset.sum_congr rfl
    intro k _
    rw [FlatArray.get_ofFn_lt _ _ _ k.isLt]

/-- Paired direct-mutual conclusion for the standard dual arm. -/
theorem arm_pinvD_std_facts
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v : ValExpr}
    {sv1 : ValSpace}
    (hsofb0 : Basis.sof b0 = .real)
    (hb0std : Basis.isStd b0) (hb1std : Basis.isStd b1)
    (ht : Nonempty (HasType ∅ Gamma (.pinvD (Basis.sof b1) e)
      (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (he : S.Term ∅ Gamma Psi e (.dual b1) v (.space sv1))
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e (.dual b1) v
      (.space sv1)) :
    RawTermDofFactsSubctx orc ∅ Gamma Psi
      (.pinvD (Basis.sof b1) e) (.tprod (.dual b0) b1)
      (.pinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1)))
      (.space (.tprod .real sv1)) :=
  ⟨arm_pinvD_std hsofb0 hb0std hb1std ht hbv hTy he ihTy ihE,
    arm_pinvD_std_dof⟩

end GLang
