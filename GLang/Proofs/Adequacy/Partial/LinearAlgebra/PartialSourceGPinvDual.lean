import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceGPinv

namespace GLang.PartialAdequacy
open scoped BigOperators Matrix TensorProduct

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

variable {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
  {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}

theorem gpinv_dual {s : Space} {sv : ValSpace} {x : DVal} {e : ValExpr}
    {vs : List (denotSpaceAux σ Ds s).carrier}
    (hb : IsListBasis (denotSpaceAux σ Ds s) vs)
    {g h : ValExpr} {ag ah : FlatArray}
    (hg : denotValB_partial orc ρ Γ Δ g = .ok (.array ag))
    (hh : denotValB_partial orc ρ Γ Δ h = .ok (.array ah))
    (hgd : ∃ d, (ValExpr.inferSpaceCtx Γ g).dofPartial (orc ρ Γ Δ) = .ok d)
    (hhd : ∃ d, (ValExpr.inferSpaceCtx Γ h).dofPartial (orc ρ Γ Δ) = .ok d)
    (hgl : ag.length = vs.length*vs.length) (hhl : ah.length = 1*1)
    (hG : denotAsMatrix vs.length vs.length ag.get =
      IsListBasis.gram (denotSpaceAux σ Ds s) vs)
    (hH : denotAsMatrix 1 1 ah.get = IsListBasis.gram HSpace.real [1])
    (hd : sv.dofPartial (orc ρ Γ Δ) = .ok vs.length)
    (harg : ResultAgree orc σ ρ Ds Γ Δ (.space (.dual s)) (.space sv)
      (.vecs (HSpace.dual (denotSpaceAux σ Ds s)) ((denotSpaceAux σ Ds s).dualOfList vs))
      x (denotValB_partial orc ρ Γ Δ e)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space (.tprod (.dual .real) s))
      (.space (.tprod .real sv))
      (.vecs (HSpace.tprod (HSpace.dual HSpace.real) (denotSpaceAux σ Ds s))
        (HSpace.tprodOfLists _ _ (HSpace.real.dualOfList [1]) vs))
      (pinvDualDVal (denotSpaceAux σ Ds s) x)
      (denotValB_partial orc ρ Γ Δ
        (.gpinv (.reshap e (.space (.tprod sv .real)) (.space sv)) g h)) := by
  obtain ⟨v,he,hagree⟩ := harg
  obtain ⟨a,n,rfl,hd',_,hlen,hcoords⟩ := hagree.array
  have hn : n = vs.length := Except.ok.inj (hd'.symm.trans hd)
  rw [hn] at hlen hcoords
  have hc : x.atSpace (HSpace.dual (denotSpaceAux σ Ds s)) =
      ∑ i : Fin vs.length, a.get i.val • ((denotSpaceAux σ Ds s).dualOfList vs).getD i.val 0 := by
    simpa only [denotSpaceAux,BasisDenot.atSpace_vecs_self] using hcoords
  have hm := mooreDual_eq_flat_gpinv_sum hb a.get x hc
  rw [← hG,← hH] at hm
  have hr : ValSpace.dofPartial (orc ρ Γ Δ) .real = .ok 1 := by
    simp [ValSpace.dofPartial,ValSpace.shpOfPartial,bind,Except.bind,pure,Except.pure]
  have hsr := dof_tprod_ok hd hr
  have hrs := dof_tprod_ok hr hd
  have he' : denotValB_partial orc ρ Γ Δ
      (.reshap e (.space (.tprod sv .real)) (.space sv)) = .ok (.array a) := by
    rw [denotValB_partial,he]
    simp [PartialValueEval.reshapeInferred,PartialValueEval.reshapeBetween,PartialValueEval.reshapeArray,hd,hsr,hlen]
  refine ⟨_,eval_gpinv he' hg hh rfl hd hr hgd hhd ⟨by simpa using hlen,hgl,hhl⟩,?_⟩
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
