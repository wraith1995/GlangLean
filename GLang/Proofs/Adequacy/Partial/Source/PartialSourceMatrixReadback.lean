import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourcePinv
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMotives
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyEmbed

namespace GLang.PartialAdequacy
open scoped BigOperators

theorem trace_witness_matrix
    {orc : PartialFFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b0 b1 : Basis} {e : Term} {env : ValExpr} {sv0 sv1 : ValSpace}
    (hdom : IsListBasis (denotSpace sigma (Basis.sof b0))
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (Basis.sof b0))))
    (hcod : IsListBasis (denotSpace sigma (Basis.sof b1))
      ((denotBasis sigma b1).atSpace
        (denotSpace sigma (Basis.sof b1))))
    (htrace : TermTraceAt orc sigma rho env
      (Basis.tof (.tprod (.dual b0) b1)) (.space (.tprod sv0 sv1))
      (denotBasis sigma (.tprod (.dual b0) b1)) (denotTerm sigma e)) :
    exists a : FlatArray,
      denotValB_partial orc rho [] [] env = .ok (.array a) ∧
      a.length =
        ((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0))).length *
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1))).length ∧
      (denotAsMatrix
        ((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0))).length
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1))).length a.get).transpose =
        hdom.coordMatrix hcod
          ((denotTerm sigma e).asLinMap
            (denotSpace sigma (Basis.sof b0))
            (denotSpace sigma (Basis.sof b1))) := by
  obtain ⟨v,hv,hagree⟩ := htrace.result
  obtain ⟨a,n,rfl,hd,hbl,hal,hc⟩ := hagree.array
  have hbl' : ((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))).length *
      ((denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b1))).length = n := by
    simp only [Basis.tof,Basis.sof,denotSpaceAux,
      RawSpaceFFS.denotBasis_tprod_dual_atSpace] at hbl
    rw [HSpace.tprodOfLists_length,HSpace.dualOfList_length] at hbl
    exact hbl
  rw [← hbl'] at hal hc
  have hcoords : (denotTerm sigma e).atSpace
      (HSpace.tprod (HSpace.dual (denotSpace sigma (Basis.sof b0)))
        (denotSpace sigma (Basis.sof b1))) =
      ∑ i : Fin (((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))).length *
        ((denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b1))).length),
        a.get i.val • (HSpace.tprodOfLists _ _
          ((denotSpace sigma (Basis.sof b0)).dualOfList
            ((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))))
          ((denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b1)))).getD i.val 0 := by
    simpa only [Basis.tof,Basis.sof,denotSpaceAux,
      RawSpaceFFS.denotBasis_tprod_dual_atSpace] using hc
  refine ⟨a,hv,hal,?_⟩
  have hm := coordMatrix_eq_of_tensor_coords hdom hcod a.get _ hcoords
  rw [← RawSpaceFFS.asLinMap_eq_dualTensorHom_atSpace] at hm
  exact hm.symm

theorem trace_inner_matrix
    {orc : PartialFFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b : Basis} {env : ValExpr} {sv : ValSpace}
    (hb : IsListBasis (denotSpace sigma (Basis.sof b))
      ((denotBasis sigma b).atSpace
        (denotSpace sigma (Basis.sof b))))
    (hdual : IsListBasis (denotSpace sigma (Basis.sof (.dual b)))
      ((denotBasis sigma (.dual b)).atSpace
        (denotSpace sigma (Basis.sof (.dual b)))))
    (htrace : TermTraceAt orc sigma rho env
      (Basis.tof (.tprod (.dual b) (.dual b)))
      (.space (.tprod sv sv))
      (denotBasis sigma (.tprod (.dual b) (.dual b)))
      (denotTerm sigma (.inner (Basis.sof b)))) :
    exists a : FlatArray,
      denotValB_partial orc rho [] [] env = .ok (.array a) ∧
      a.length =
        ((denotBasis sigma b).atSpace
          (denotSpace sigma (Basis.sof b))).length ^ 2 ∧
      denotAsMatrix
        ((denotBasis sigma b).atSpace
          (denotSpace sigma (Basis.sof b))).length
        ((denotBasis sigma b).atSpace
          (denotSpace sigma (Basis.sof b))).length a.get =
        IsListBasis.gram (denotSpace sigma (Basis.sof b))
          ((denotBasis sigma b).atSpace
            (denotSpace sigma (Basis.sof b))) := by
  let V := denotSpace sigma (Basis.sof b)
  let S := (denotBasis sigma b).atSpace V
  let D := (denotBasis sigma (.dual b)).atSpace (HSpace.dual V)
  have hD : D = V.dualOfList S := by
    exact RawSpaceFFS.denotBasis_dual_atSpace sigma b
  have hDlen : D.length = S.length := by
    rw [hD, HSpace.dualOfList_length]
  have hdualD : IsListBasis (HSpace.dual V) D := hdual
  obtain ⟨a, ha, halen, hmatrix⟩ :=
    trace_witness_matrix (b0 := b) (b1 := .dual b) hb hdualD htrace
  have hinner :
      (denotTerm sigma (.inner (Basis.sof b))).asLinMap V
          (HSpace.dual V) = V.innerProduct := by
    exact asLinMap_innerTensor V V.innerProduct
  refine ⟨a, ha, ?_, ?_⟩
  · change a.length = S.length ^ 2
    rw [pow_two]
    change a.length = S.length * D.length at halen
    exact halen.trans (congrArg (S.length * ·) hDlen)
  · change denotAsMatrix S.length S.length a.get =
      IsListBasis.gram V S
    ext i j
    change (denotAsMatrix S.length D.length a.get).transpose =
        hb.coordMatrix hdualD
          ((denotTerm sigma (.inner (Basis.sof b))).asLinMap V
            (HSpace.dual V)) at hmatrix
    let jD : Fin D.length := Fin.cast hDlen.symm j
    have hm := congrFun (congrFun hmatrix jD) i
    simp only [Matrix.transpose_apply] at hm
    rw [hinner] at hm
    have hc := RawTermEmbed.coordMatrix_inner_of_dual_eq hb hdualD hD jD i
    have hcast :
        Fin.cast ((congrArg (fun xs => xs.length) hD).trans
          (HSpace.dualOfList_length V S)) jD = j := by
      apply Fin.ext
      rfl
    rw [hcast] at hc
    have hm' : denotAsMatrix S.length S.length a.get i j =
        hb.coordMatrix hdualD V.innerProduct jD i := by
      simpa [denotAsMatrix, jD, hDlen] using hm
    exact hm'.trans hc

end GLang.PartialAdequacy
