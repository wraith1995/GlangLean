import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCob
import GLang.Proofs.Adequacy.Raw.RawPinvCoordinateBridge

namespace GLang.PartialAdequacy
open scoped Matrix TensorProduct

theorem coordMatrix_eq_of_tensor_coords
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

theorem asLinFunctional_eq_atSpace (V : HSpace) (d : DVal) :
    d.asLinFunctional V = d.atSpace (HSpace.dual V) := by
  unfold DVal.asLinFunctional DVal.atSpace
  obtain ⟨Vt, t⟩ := d.asHil
  by_cases h : Vt.carrier = (V.carrier →ₗ[ℝ] ℝ)
  · simp only [h, dif_pos]
  · simp only [h, dif_neg]

/-- A flat expansion in the dual list basis is the column matrix consumed
by the value semantics after the `pinvD` reshape to `V ⊗ real`. -/
theorem coordMatrix_functional_eq
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

variable {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
  {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}

theorem eval_pinv {e : ValExpr} {a : FlatArray} {sa sb : ValSpace} {m n : Nat}
    (he : denotValB_partial orc ρ Γ Δ e = .ok (.array a))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod sa sb)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok m)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok n)
    (hlen : a.length = m*n) :
    denotValB_partial orc ρ Γ Δ (.pinv e) =
      .ok (.array (FlatArray.ofFn (n*m)
        (matrixAsDenot (matrixSVDPinv (denotAsMatrix m n a.get))))) := by
  have heq : denotValB_partial orc ρ Γ Δ (.pinv e) =
      denotValB_partial orc ρ Γ Δ (.inv e) := by
    rw [denotValB_partial,denotValB_partial]
    simp only [ValExpr.inferSpaceCtx]
  exact heq.trans (eval_inv he hinfer ha hb hlen)

/-- Standard-basis tensor pseudoinversion agrees with the intrinsic
Moore-Penrose inverse; successful dimensions discharge every runtime guard. -/
theorem pinv_tensor {s₀ s₁ : Space} {sa sb : ValSpace} {x : DVal} {e : ValExpr}
    {vs₀ : List (denotSpaceAux σ Ds s₀).carrier}
    {vs₁ : List (denotSpaceAux σ Ds s₁).carrier}
    (hb₀ : IsListBasis (denotSpaceAux σ Ds s₀) vs₀)
    (hb₁ : IsListBasis (denotSpaceAux σ Ds s₁) vs₁)
    (horth₀ : ∀ i j : Fin vs₀.length,
      (denotSpaceAux σ Ds s₀).innerProduct (vs₀.get i) (vs₀.get j) = if i = j then 1 else 0)
    (horth₁ : ∀ i j : Fin vs₁.length,
      (denotSpaceAux σ Ds s₁).innerProduct (vs₁.get i) (vs₁.get j) = if i = j then 1 else 0)
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod sa sb)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok vs₀.length)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok vs₁.length)
    (h : ResultAgree orc σ ρ Ds Γ Δ (.space (.tprod (.dual s₀) s₁))
      (.space (.tprod sa sb))
      (.vecs (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s₀)) (denotSpaceAux σ Ds s₁))
        (HSpace.tprodOfLists _ _ ((denotSpaceAux σ Ds s₀).dualOfList vs₀) vs₁))
      x (denotValB_partial orc ρ Γ Δ e)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space (.tprod (.dual s₁) s₀))
      (.space (.tprod sb sa))
      (.vecs (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s₁)) (denotSpaceAux σ Ds s₀))
        (HSpace.tprodOfLists _ _ ((denotSpaceAux σ Ds s₁).dualOfList vs₁) vs₀))
      (pinvTensorDVal (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁) x)
      (denotValB_partial orc ρ Γ Δ (.pinv e)) := by
  obtain ⟨v,he,hagree⟩ := h
  obtain ⟨a,n,rfl,hd,_,hlen,hcoords⟩ := hagree.array
  have hdim := dof_tprod_ok ha hb
  have hdim' := dof_tprod_ok hb ha
  have hn : n = vs₀.length * vs₁.length := Except.ok.inj (hd.symm.trans hdim)
  rw [hn] at hlen hcoords
  have hc : x.atSpace (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s₀))
      (denotSpaceAux σ Ds s₁)) = ∑ k : Fin (vs₀.length*vs₁.length), a.get k.val •
        (HSpace.tprodOfLists _ _ ((denotSpaceAux σ Ds s₀).dualOfList vs₀) vs₁).getD k.val 0 := by
    simpa only [denotSpaceAux,BasisDenot.atSpace_vecs_self] using hcoords
  have hm := mooreTensor_eq_flat_pinv_sum hb₀ hb₁ horth₀ horth₁ a.get _ hc
  rw [← RawSpaceFFS.asLinMap_eq_dualTensorHom_atSpace] at hm
  refine ⟨_,eval_pinv he hinfer ha hb hlen,?_⟩
  simp only [Agree,denotSpaceAux,BasisDenot.atSpace_vecs_self]
  refine ⟨_,hdim',?_,FlatArray.length_ofFn _ _,?_⟩
  · rw [HSpace.tprodOfLists_length,HSpace.dualOfList_length]
  · change (pinvTensorDVal (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁) x).atSpace
      (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s₁)) (denotSpaceAux σ Ds s₀)) = _
    simp only [pinvTensorDVal,DVal.atSpace_hil_self]
    rw [hm]
    apply Finset.sum_congr rfl
    intro k _
    rw [FlatArray.get_ofFn_lt _ _ _ k.isLt]
    rfl

/-- Covector pseudoinversion uses the explicit column-matrix reshape. -/
theorem pinv_dual {s : Space} {sv : ValSpace} {x : DVal} {e : ValExpr}
    {vs : List (denotSpaceAux σ Ds s).carrier}
    (hb : IsListBasis (denotSpaceAux σ Ds s) vs)
    (horth : ∀ i j : Fin vs.length,
      (denotSpaceAux σ Ds s).innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0)
    (hd : sv.dofPartial (orc ρ Γ Δ) = .ok vs.length)
    (h : ResultAgree orc σ ρ Ds Γ Δ (.space (.dual s)) (.space sv)
      (.vecs (HSpace.dual (denotSpaceAux σ Ds s)) ((denotSpaceAux σ Ds s).dualOfList vs))
      x (denotValB_partial orc ρ Γ Δ e)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space (.tprod (.dual .real) s))
      (.space (.tprod .real sv))
      (.vecs (HSpace.tprod (HSpace.dual HSpace.real) (denotSpaceAux σ Ds s))
        (HSpace.tprodOfLists _ _ (HSpace.real.dualOfList [1]) vs))
      (pinvDualDVal (denotSpaceAux σ Ds s) x)
      (denotValB_partial orc ρ Γ Δ
        (.pinv (.reshap e (.space (.tprod sv .real)) (.space sv)))) := by
  obtain ⟨v,he,hagree⟩ := h
  obtain ⟨a,n,rfl,hd',_,hlen,hcoords⟩ := hagree.array
  have hn : n = vs.length := Except.ok.inj (hd'.symm.trans hd)
  rw [hn] at hlen hcoords
  have hc : x.atSpace (HSpace.dual (denotSpaceAux σ Ds s)) =
      ∑ i : Fin vs.length, a.get i.val • ((denotSpaceAux σ Ds s).dualOfList vs).getD i.val 0 := by
    simpa only [denotSpaceAux,BasisDenot.atSpace_vecs_self] using hcoords
  have hm := mooreDual_eq_flat_pinv_sum hb horth a.get x hc
  have hr : ValSpace.dofPartial (orc ρ Γ Δ) .real = .ok 1 := by
    simp [ValSpace.dofPartial,ValSpace.shpOfPartial,bind,Except.bind,pure,Except.pure]
  have hsr := dof_tprod_ok hd hr
  have hrs := dof_tprod_ok hr hd
  have he' : denotValB_partial orc ρ Γ Δ
      (.reshap e (.space (.tprod sv .real)) (.space sv)) = .ok (.array a) := by
    rw [denotValB_partial,he]
    simp [PartialValueEval.reshapeInferred,PartialValueEval.reshapeBetween,PartialValueEval.reshapeArray,hd,hsr,hlen]
  refine ⟨_,eval_pinv he' rfl hd hr (by simpa using hlen),?_⟩
  simp only [Agree,denotSpaceAux,BasisDenot.atSpace_vecs_self]
  refine ⟨_,hrs,?_,FlatArray.length_ofFn _ _,?_⟩
  · rw [HSpace.tprodOfLists_length,HSpace.dualOfList_length]
    rfl
  · change (pinvDualDVal (denotSpaceAux σ Ds s) x).atSpace
      (HSpace.tprod (HSpace.dual HSpace.real) (denotSpaceAux σ Ds s)) = _
    simp only [pinvDualDVal,DVal.atSpace_hil_self]
    rw [hm]
    apply Finset.sum_congr rfl
    intro k _
    rw [FlatArray.get_ofFn_lt _ _ _ k.isLt]
    rfl

end GLang.PartialAdequacy
