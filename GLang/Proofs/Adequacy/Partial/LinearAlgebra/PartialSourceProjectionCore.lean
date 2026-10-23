import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMatrixReadback
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCobConstructors
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobProjections

namespace GLang.PartialAdequacy
open scoped BigOperators Matrix
open PartialValueEval

theorem trace_linear_map_rows
    {orc : PartialFFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b0 b1 : Basis} {e : Term} {env : ValExpr}
    {sv0 sv1 : ValSpace}
    (hdom : IsListBasis (denotSpace sigma (Basis.sof b0))
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (Basis.sof b0))))
    (hcod : IsListBasis (denotSpace sigma (Basis.sof b1))
      ((denotBasis sigma b1).atSpace
        (denotSpace sigma (Basis.sof b1))))
    (htrace : TermTraceAt orc sigma rho env
      (Basis.tof (.tprod (.dual b0) b1))
      (.space (.tprod sv0 sv1))
      (denotBasis sigma (.tprod (.dual b0) b1))
      (denotTerm sigma e)) :
    exists a : FlatArray,
      denotValB_partial orc rho [] [] env = .ok (.array a) /\
      a.length =
        ((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0))).length *
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1))).length /\
      forall j : Fin
          ((denotBasis sigma b0).atSpace
            (denotSpace sigma (Basis.sof b0))).length,
        (denotTerm sigma e).asLinMap
            (denotSpace sigma (Basis.sof b0))
            (denotSpace sigma (Basis.sof b1))
            (((denotBasis sigma b0).atSpace
              (denotSpace sigma (Basis.sof b0))).get j) =
          ∑ i : Fin
              ((denotBasis sigma b1).atSpace
                (denotSpace sigma (Basis.sof b1))).length,
            a.get (j.val *
                ((denotBasis sigma b1).atSpace
                  (denotSpace sigma (Basis.sof b1))).length + i.val) •
              ((denotBasis sigma b1).atSpace
                (denotSpace sigma (Basis.sof b1))).get i := by
  obtain ⟨a,he,hlen,hM⟩ := trace_witness_matrix hdom hcod htrace
  refine ⟨a,he,hlen,?_⟩
  intro j
  rw [← hcod.sum_coords_smul ((denotTerm sigma e).asLinMap
    (denotSpace sigma (Basis.sof b0)) (denotSpace sigma (Basis.sof b1))
    (((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))).get j))]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hij := congrFun (congrFun hM i) j
  simp only [Matrix.transpose_apply,denotAsMatrix,IsListBasis.coordMatrix,
    LinearMap.toMatrix_apply,IsListBasis.toBasis_apply] at hij
  simpa only [Nat.mul_comm] using hij.symm

theorem mtm_rectangular
    (orc : PartialFFSOracleSem) (rho : ValEnvSem)
    {left right : ValExpr} {aLeft aRight : FlatArray}
    {sSource sMiddle sTarget sAux : ValSpace}
    {nSource nMiddle nTarget : Nat}
    (hLeftInfer : ValExpr.inferSpaceCtx [] left =
      .tprod sMiddle sTarget)
    (hRightInfer : ValExpr.inferSpaceCtx [] right =
      .tprod sSource sMiddle)
    (hLeft : denotValB_partial orc rho [] [] left = .ok (.array aLeft))
    (hRight : denotValB_partial orc rho [] [] right = .ok (.array aRight))
    (hSource : ValSpace.dofPartial (orc rho [] []) sSource = .ok nSource)
    (hMiddle : ValSpace.dofPartial (orc rho [] []) sMiddle = .ok nMiddle)
    (hTarget : ValSpace.dofPartial (orc rho [] []) sTarget = .ok nTarget)
    (hLeftLen : aLeft.length = nMiddle * nTarget)
    (hRightLen : aRight.length = nSource * nMiddle) :
    exists a : FlatArray,
      denotValB_partial orc rho [] []
        (.mtm 0 0 sMiddle sAux left right) =
        .ok (.array a) /\
      a.length = nSource * nTarget /\
      forall j i, j < nSource -> i < nTarget ->
        a.get (j * nTarget + i) =
          ∑ k ∈ Finset.range nMiddle,
            aLeft.get (k * nTarget + i) *
              aRight.get (j * nMiddle + k) := by
  let out := FlatArray.ofFn (nSource * nTarget) fun q =>
    if q >= nSource * nTarget then 0
    else ∑ k ∈ Finset.range nMiddle,
      aLeft.get (nTarget * k + q % nTarget) *
        aRight.get (nMiddle * (q / nTarget) + k)
  have hval : denotValB_partial orc rho [] []
      (.mtm 0 0 sMiddle sAux left right) =
      .ok (.array out) := by
    have hMT := dof_tprod_ok hMiddle hTarget
    have hSM := dof_tprod_ok hSource hMiddle
    have hST := dof_tprod_ok hSource hTarget
    rw [denotValB_partial]
    simp only [ValExpr.inferSpaceCtx,hLeftInfer,hRightInfer]
    rw [guard_ok (by
      intro s hs
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact ⟨_,hMiddle⟩
      · exact ⟨_,hMT⟩
      · exact ⟨_,hSM⟩
      · exact ⟨_,hST⟩)]
    have hs : ValueShape.mtm (numbers (orc rho [] [])) sMiddle
        (.tprod sMiddle sTarget) (.tprod sSource sMiddle) aLeft aRight := by
      simp only [ValueShape.mtm,ValueShape.matrices,ValueShape.tensor,
        dof_numbers _ _ _ hMiddle,dof_numbers _ _ _ hSource,dof_numbers _ _ _ hTarget,
        hLeftLen,hRightLen,and_self]
    simp only [hLeft,hRight,ValValSem.bindArrays,ValValSem.bindArray,if_pos hs,
      dof_numbers _ _ _ hMiddle,dof_numbers _ _ _ hSource,dof_numbers _ _ _ hTarget,
      dof_numbers _ _ _ hST,ValValSem.arrayOf]
    rfl
  refine ⟨out, hval, ?_, ?_⟩
  · simp [out]
  · intro j i hj hi
    have hlt : j * nTarget + i < nSource * nTarget := by
      calc
        j * nTarget + i < j * nTarget + nTarget :=
          Nat.add_lt_add_left hi _
        _ = (j + 1) * nTarget := by
          rw [Nat.add_mul, one_mul]
        _ ≤ nSource * nTarget :=
          Nat.mul_le_mul_right nTarget (Nat.succ_le_iff.mpr hj)
    have hnle : ¬ (nSource * nTarget ≤ j * nTarget + i) :=
      Nat.not_le.mpr hlt
    have hdm := RawSpaceFFS.rowMajor_div_mod (i := j) hi
    have hdiv : (j * nTarget + i) / nTarget = j := by
      calc
        (j * nTarget + i) / nTarget =
            (i + nTarget * j) / nTarget := by
          rw [Nat.mul_comm, Nat.add_comm]
        _ = j := hdm.1
    have hmod : (j * nTarget + i) % nTarget = i := by
      calc
        (j * nTarget + i) % nTarget =
            (i + nTarget * j) % nTarget := by
          rw [Nat.mul_comm, Nat.add_comm]
        _ = i := hdm.2
    simp only [out, FlatArray.get_ofFn, hlt, if_true, ge_iff_le,
      hnle, if_false, hdiv, hmod]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.mul_comm nTarget k, Nat.mul_comm nMiddle j]

theorem reshape_array {orc : PartialFFSOracleSem} {rho : ValEnvSem}
    {e : ValExpr} {s : ValSpace} {a : FlatArray} {n : Nat}
    (he : denotValB_partial orc rho [] [] e = .ok (.array a))
    (hd : s.dofPartial (orc rho [] []) = .ok n) (hlen : a.length = n) :
    denotValB_partial orc rho [] [] (ValExpr.reshapBase e s) = .ok (.array a) := by
  rw [ValExpr.reshapBase,denotValB_partial,he]
  simp [PartialValueEval.reshapeInferred,PartialValueEval.reshapeBetween,PartialValueEval.reshapeArray,hd,hlen]

end GLang.PartialAdequacy
