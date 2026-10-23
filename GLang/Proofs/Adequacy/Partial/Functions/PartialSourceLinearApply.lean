import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMatrixReadback
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCob
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceWellFormed
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourcePinvConstructors

namespace GLang.PartialAdequacy
open scoped BigOperators Matrix
open PartialValueEval
variable {orc : PartialFFSOracleSem} {ρ : ValEnvSem} {Γ : List ValTy} {Δ : List ValValSem}

theorem eval_ttv {matrix vector : ValExpr} {a b : FlatArray}
    {sv sa sb : ValSpace} {m n : Nat}
    (hm : denotValB_partial orc ρ Γ Δ matrix = .ok (.array a))
    (he : denotValB_partial orc ρ Γ Δ vector = .ok (.array b))
    (him : ValExpr.inferSpaceCtx Γ matrix = .tprod sa sb)
    (hv : sv.dofPartial (orc ρ Γ Δ) = .ok m)
    (hi : (ValExpr.inferSpaceCtx Γ vector).dofPartial (orc ρ Γ Δ) = .ok m)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok m)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok n)
    (hlenA : a.length = m*n) (hlenB : b.length = m) :
    denotValB_partial orc ρ Γ Δ (.ttv sv matrix vector) =
      .ok (.array (FlatArray.ofFn n (fun i => if i ≥ n then 0 else
        ∑ j ∈ Finset.range m, a.get (n*j+i) * b.get j))) := by
  have hab := dof_tprod_ok ha hb
  rw [denotValB_partial]
  simp only [ValExpr.inferSpaceCtx, him]
  rw [guard_ok (by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨_,hv⟩
    · exact ⟨_,hab⟩
    · exact ⟨_,hi⟩
    · exact ⟨_,hb⟩)]
  have hshape : ValueShape.ttv (numbers (orc ρ Γ Δ)) sv (.tprod sa sb) (ValExpr.inferSpaceCtx Γ vector) a b := by
    simp only [ValueShape.ttv, ValueShape.pair,
      dof_numbers _ _ _ ha, dof_numbers _ _ _ hb, dof_numbers _ _ _ hab,
      dof_numbers _ _ _ hv, dof_numbers _ _ _ hi, hlenA, hlenB, and_self]
  simp only [hm,he,ValValSem.bindArrays,ValValSem.bindArray,if_pos hshape,
    dof_numbers _ _ _ hb,dof_numbers _ _ _ hv,ValValSem.arrayOf]

theorem apply_coordinates {V W : HSpace} {S : List V.carrier} {T : List W.carrier}
    (hS : IsListBasis V S) (hT : IsListBasis W T)
    (f : V.carrier →ₗ[ℝ] W.carrier) (x : V.carrier) (a b : FlatArray)
    (hM : (denotAsMatrix S.length T.length a.get).transpose = hS.coordMatrix hT f)
    (hx : x = ∑ i : Fin S.length, b.get i.val • S.getD i.val 0) :
    f x = ∑ i : Fin T.length,
      (∑ j ∈ Finset.range S.length, a.get (T.length*j+i.val)*b.get j) • T.getD i.val 0 := by
  have hx' : x = ∑ i : Fin S.length, b.get i.val • S.get i := by
    rw [hx]
    apply Finset.sum_congr rfl
    intro i _
    rw [List.getD_eq_getElem S 0 i.isLt]
    rfl
  rw [hx',hS.apply_sum_smul hT,← hM]
  apply Finset.sum_congr rfl
  intro i _
  rw [List.getD_eq_getElem T 0 i.isLt]
  congr 1
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,denotAsMatrix]
  exact Fin.sum_univ_eq_sum_range (fun j => a.get (T.length*j+i.val)*b.get j) S.length

open Basis (BasisValid)

theorem arm_appL_lin
    {orc : PartialFFSOracleSem}
    {Delta0 Delta1 : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {n0 n1 : Term} {env0 env1 : ValExpr}
    {sv svOut svMat0 svMat1 svArg : ValSpace}
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (htof1 : Basis.tof b1 = .space (Basis.sof b1))
    (_ht : Nonempty
      (HasType (Delta0 ∪ Delta1) Gamma
        (.appL (Basis.sof b0) (Basis.sof b1) n0 n1)
        (Basis.tof b1)))
    (hbv : BasisValid Gamma b1)
    (_hsv : S.Space Gamma Psi (Basis.sof b0) sv)
    (hTy : S.TyAt Gamma Psi b1 (.space svOut))
    (h0 : S.Term Delta0 Gamma Psi n0 (.tprod (.dual b0) b1)
      env0 (.space (.tprod svMat0 svMat1)))
    (h1 : S.Term Delta1 Gamma Psi n1 b0 env1 (.space svArg))
    (ihSpace : MSpaceSubctx orc Gamma Psi (Basis.sof b0) sv)
    (ihTy : MTyAtSubctx orc Gamma Psi b1 (.space svOut))
    (ih0 : TermFactsSubctx orc Delta0 Gamma Psi n0
      (.tprod (.dual b0) b1) env0 (.space (.tprod svMat0 svMat1)))
    (ih1 : TermFactsSubctx orc Delta1 Gamma Psi n1 b0 env1
      (.space svArg)) :
    MTermSubctx orc (Delta0 ∪ Delta1) Gamma Psi
      (.appL (Basis.sof b0) (Basis.sof b1) n0 n1) b1
      (ValExpr.reshapBase (.ttv sv env0 env1) svOut) (.space svOut) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have tr0 := ih0.trace hsub (Graded.CtxDisj.of_union_left hctx)
    rho Delta' Gamma' sigma GammaV (RawCtxIncl.union_left hle) hc
  have tr1 := ih1.trace hsub (Graded.CtxDisj.of_union_right hctx)
    rho Delta' Gamma' sigma GammaV (RawCtxIncl.union_right hdisj hle) hc
  obtain ⟨_,htof0',_⟩ := h1.ty.space_inv
  have htof0 := Basis.tof_eq_space_sof_of_tof_space htof0'
  have hb0v := h1.basisValid
  have hB := denotBasis_atSpace_isListBasis sigma Gamma' b0
    (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hC := denotBasis_atSpace_isListBasis sigma Gamma' b1
    (raw_basisValid_mono hbv hle.2) hc.ctxWF_nl hc.envWF_nl
  have hs := ihSpace hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hv := shape_dof hs
  rw [hB.finrank_eq] at hv
  have hsout : svOut.shpOfPartial (orc rho [] []) = .ok (srcShp sigma [] (Basis.sof b1)) := by
    simpa only [htof1,DimsAt] using targetDims
  have houtdim := shape_dof hsout
  rw [hC.finrank_eq] at houtdim
  have hmatshape : (.tprod svMat0 svMat1 : ValSpace).shpOfPartial (orc rho [] []) =
      .ok [Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual] using tr0.dims
  obtain ⟨hmat0,hmat1⟩ := tprod_shape_factors hmatshape
  rw [hB.finrank_eq] at hmat0
  rw [hC.finrank_eq] at hmat1
  have hmati := ih0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  rw [hmatshape] at hmati
  obtain ⟨sa,sb,hinfer,ha,hb⟩ := infer_tprod_of_partial_shape hmati
  rw [hB.finrank_eq] at ha
  rw [hC.finrank_eq] at hb
  obtain ⟨a,he0,halen,hM⟩ := trace_witness_matrix hB hC tr0
  obtain ⟨v',he1,hagree⟩ := tr1.result
  rw [htof0] at hagree
  obtain ⟨a1,n,rfl,hd,hbl,hlen,hcoords⟩ := hagree.array
  rw [← hbl] at hd hlen hcoords
  have hi : (ValExpr.inferSpaceCtx [] env1).dofPartial (orc rho [] []) =
      svArg.dofPartial (orc rho [] []) := by
    simp only [ValSpace.dofPartial,ih1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc]
  have hic := hi.trans hd
  have hinner : ResultAgree orc sigma rho [] [] []
      (.space (Basis.sof b1)) (.space svOut) (denotBasis sigma b1)
      (denotTerm sigma (.appL (Basis.sof b0) (Basis.sof b1) n0 n1))
      (denotValB_partial orc rho [] [] (.ttv sv env0 env1)) := by
    refine ⟨_,eval_ttv he0 he1 hinfer hv hic ha hb halen hlen,?_⟩
    simp only [Agree]
    refine ⟨_,houtdim,rfl,FlatArray.length_ofFn _ _,?_⟩
    rw [denotTerm_appL,DVal.atSpace_hil_self]
    have happ := apply_coordinates hB hC
      ((denotTerm sigma n0).asLinMap (denotSpace sigma (Basis.sof b0))
        (denotSpace sigma (Basis.sof b1)))
      ((denotTerm sigma n1).atSpace (denotSpace sigma (Basis.sof b0))) a a1 hM hcoords
    rw [happ]
    apply Finset.sum_congr rfl
    intro i _
    rw [FlatArray.get_ofFn_lt _ _ _ i.isLt,if_neg (Nat.not_le.mpr i.isLt)]
  refine ⟨?_,targetDims⟩
  rw [htof1]
  exact reshape_space hinner

theorem arm_appI_lin
    {orc : PartialFFSOracleSem}
    {Delta0 Delta1 : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 : Basis} {n0 n1 : Term} {env0 env1 : ValExpr}
    {sv svFun svArg : ValSpace}
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (_ht : Nonempty (HasType (Delta0 ∪ Delta1) Gamma
      (.appI (Basis.sof b0) n0 n1) (Basis.tof .one)))
    (_hsv : S.Space Gamma Psi (Basis.sof b0) sv)
    (_hTy : S.TyAt Gamma Psi .one (.space .real))
    (h0 : S.Term Delta0 Gamma Psi n0 (.dual b0) env0 (.space svFun))
    (h1 : S.Term Delta1 Gamma Psi n1 b0 env1 (.space svArg))
    (ihSpace : MSpaceSubctx orc Gamma Psi (Basis.sof b0) sv)
    (ihTy : MTyAtSubctx orc Gamma Psi .one (.space .real))
    (ih0 : MTermSubctx orc Delta0 Gamma Psi
      n0 (.dual b0) env0 (.space svFun))
    (ih1 : TermFactsSubctx orc Delta1 Gamma Psi
      n1 b0 env1 (.space svArg)) :
    MTermSubctx orc (Delta0 ∪ Delta1) Gamma Psi
      (.appI (Basis.sof b0) n0 n1) .one
      (.ttv sv
        (.reshap env0 (.space (.tprod sv .real)) (.space sv)) env1)
      (.space .real) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have tr0 := ih0 hsub (Graded.CtxDisj.of_union_left hctx)
    rho Delta' Gamma' sigma GammaV (RawCtxIncl.union_left hle) hc
  have tr1 := ih1.trace hsub (Graded.CtxDisj.of_union_right hctx)
    rho Delta' Gamma' sigma GammaV (RawCtxIncl.union_right hdisj hle) hc
  obtain ⟨_,htof0',_⟩ := h1.ty.space_inv
  have htof0 := Basis.tof_eq_space_sof_of_tof_space htof0'
  have hB := denotBasis_atSpace_isListBasis sigma Gamma' b0
    (raw_basisValid_mono h1.basisValid hle.2) hc.ctxWF_nl hc.envWF_nl
  have hv := shape_dof (ihSpace hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  rw [hB.finrank_eq] at hv
  obtain ⟨v0,he0,ha0⟩ := tr0.result
  obtain ⟨a0,dim0,rfl,hd0,hbl0,hlen0,hc0⟩ := ha0.array
  have hbl0' : ((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))).length = dim0 := by
    simp only [Basis.sof,denotSpaceAux,RawSpaceFFS.denotBasis_dual_atSpace] at hbl0
    rw [HSpace.dualOfList_length] at hbl0
    exact hbl0
  rw [← hbl0'] at hlen0 hc0
  obtain ⟨v1,he1,ha1⟩ := tr1.result
  rw [htof0] at ha1
  obtain ⟨a1,dim1,rfl,hd1,hbl1,hlen1,hc1⟩ := ha1.array
  rw [← hbl1] at hd1 hlen1 hc1
  have hphi : (denotTerm sigma n0).asLinFunctional (denotSpace sigma (Basis.sof b0)) =
      ∑ i : Fin ((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))).length,
        a0.get i.val • ((denotSpace sigma (Basis.sof b0)).dualOfList
          ((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0)))).getD i.val 0 := by
    rw [asLinFunctional_eq_atSpace]
    simpa only [Basis.sof,denotSpaceAux,RawSpaceFFS.denotBasis_dual_atSpace] using hc0
  have hM := (coordMatrix_functional_eq hB a0.get _ hphi).symm
  have hr : ValSpace.dofPartial (orc rho [] []) .real = .ok 1 := by
    simp [ValSpace.dofPartial,ValSpace.shpOfPartial,bind,Except.bind,pure,Except.pure]
  have he0' : denotValB_partial orc rho [] []
      (.reshap env0 (.space (.tprod sv .real)) (.space sv)) = .ok (.array a0) := by
    rw [denotValB_partial,he0]
    simp [PartialValueEval.reshapeInferred,PartialValueEval.reshapeBetween,PartialValueEval.reshapeArray,hv,dof_tprod_ok hv hr,hlen0]
  have hi : (ValExpr.inferSpaceCtx [] env1).dofPartial (orc rho [] []) =
      svArg.dofPartial (orc rho [] []) := by
    simp only [ValSpace.dofPartial,ih1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc]
  refine ⟨⟨_,eval_ttv he0' he1 rfl hv (hi.trans hd1) hv hr
    (by simpa only [Nat.mul_one] using hlen0) hlen1,?_⟩,targetDims⟩
  simp only [Basis.tof,Basis.sof,Agree,denotSpaceAux,denotBasis,BasisDenot.atSpace_vecs_self]
  refine ⟨1,hr,rfl,FlatArray.length_ofFn _ _,?_⟩
  rw [denotTerm_appI,DVal.atSpace_hil_self]
  have happ := apply_coordinates hB isListBasis_one
    ((denotTerm sigma n0).asLinFunctional (denotSpace sigma (Basis.sof b0)))
    ((denotTerm sigma n1).atSpace (denotSpace sigma (Basis.sof b0))) a0 a1 hM hc1
  rw [happ]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val < 1 := i.isLt
  rw [FlatArray.get_ofFn_lt 1 _ _ hi,if_neg (Nat.not_le.mpr hi)]
  rfl

end GLang.PartialAdequacy
