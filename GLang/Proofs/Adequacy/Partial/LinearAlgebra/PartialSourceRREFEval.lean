import GLang.Proofs.Adequacy.Partial.Source.PartialSourceLinearSums
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCob
namespace GLang.PartialAdequacy
open PartialValueEval
theorem denotValB_partial_termsRREFRep_ok
    (orc : PartialFFSOracleSem) (rho : ValEnvSem)
    {env0 env1 : ValExpr} {sv : ValSpace}
    {a0 a1 : FlatArray} {N K : Nat}
    (h0 : denotValB_partial orc rho [] [] env0 = .ok (.array a0))
    (h1 : denotValB_partial orc rho [] [] env1 = .ok (.array a1))
    (hsv : sv.dofPartial (orc rho [] []) = .ok N)
    (ha0 : a0.length = K * N)
    (ha1 : a1.length = N * N)
    (hN : 0 < N) :
    denotValB_partial orc rho [] []
        (ValExpr.reshapBase
          (.rrefRep env0
            (ValExpr.reshapBase env1 (.tprod sv sv)))
          (.tprod sv sv)) =
      .ok (.array (FlatArray.ofFn (N * N)
        (termsRREFRepDenot N K a0.get a1.get))) := by
  have hdim : (.tprod sv sv : ValSpace).dofPartial (orc rho [] []) = .ok (N * N) := by
    simpa using dof_tprod_ok hsv hsv
  have hinner := reshapeBase_ok h1 (by rw [ha1]; exact hdim)
  have hK' : a0.length / N = K := by
    rw [ha0]
    exact Nat.mul_div_cancel K hN
  have hrref : denotValB_partial orc rho [] []
      (.rrefRep env0 (ValExpr.reshapBase env1 (.tprod sv sv))) =
      .ok (.array (FlatArray.ofFn (N * N)
        (termsRREFRepDenot N K a0.get a1.get))) := by
    rw [denotValB_partial]
    simp only [ValExpr.reshapBase, ValExpr.inferSpaceCtx, ValTy.spaceOf_space]
    have hg : dimensions (orc rho [] []) [.tprod sv sv, .tprod sv sv] = .ok () := by
      simp [dimensions, hdim, bind, Except.bind]
    rw [withDimensions, hg]
    dsimp only
    simp only [ValExpr.reshapBase] at hinner
    rw [h0, hinner]
    simp only [dof_numbers _ _ _ hsv, dof_numbers _ _ _ hdim]
    simp only [ValValSem.bindArrays, ValValSem.bindArray,
      ValExpr.reshapBase, ValExpr.inferSpaceCtx, ValTy.spaceOf_space,
      ValSpace.dof_tprod, dof_numbers _ _ _ hsv, ValValSem.arrayOf]
    rw [hK']
    simp only [ha0, ha1, and_self, if_true]
  exact reshapeBase_ok hrref (by simpa only [FlatArray.length_ofFn] using hdim)

theorem denotValB_partial_termsRREFRep_zero_ok
    (orc : PartialFFSOracleSem) (rho : ValEnvSem)
    {env0 env1 : ValExpr} {sv : ValSpace}
    {a0 a1 : FlatArray}
    (h0 : denotValB_partial orc rho [] [] env0 = .ok (.array a0))
    (h1 : denotValB_partial orc rho [] [] env1 = .ok (.array a1))
    (hsv : sv.dofPartial (orc rho [] []) = .ok 0)
    (ha0 : a0.length = 0)
    (ha1 : a1.length = 0) :
    denotValB_partial orc rho [] []
        (ValExpr.reshapBase
          (.rrefRep env0
            (ValExpr.reshapBase env1 (.tprod sv sv)))
          (.tprod sv sv)) =
      .ok (.array (FlatArray.ofFn 0
        (termsRREFRepDenot 0 0 a0.get a1.get))) := by
  have hdim : (.tprod sv sv : ValSpace).dofPartial (orc rho [] []) = .ok (0) := by
    simpa using dof_tprod_ok hsv hsv
  have hinner := reshapeBase_ok h1 (by rw [ha1]; exact hdim)
  have hrref : denotValB_partial orc rho [] []
      (.rrefRep env0 (ValExpr.reshapBase env1 (.tprod sv sv))) =
      .ok (.array (FlatArray.ofFn 0
        (termsRREFRepDenot 0 0 a0.get a1.get))) := by
    rw [denotValB_partial]
    simp only [ValExpr.reshapBase, ValExpr.inferSpaceCtx, ValTy.spaceOf_space]
    have hg : dimensions (orc rho [] []) [.tprod sv sv, .tprod sv sv] = .ok () := by
      simp [dimensions, hdim, bind, Except.bind]
    rw [withDimensions, hg]
    dsimp only
    simp only [ValExpr.reshapBase] at hinner
    rw [h0, hinner]
    simp only [dof_numbers _ _ _ hsv, dof_numbers _ _ _ hdim]
    simp only [ValValSem.bindArrays, ValValSem.bindArray,
      ValExpr.reshapBase, ValExpr.inferSpaceCtx, ValTy.spaceOf_space,
      ValSpace.dof_tprod, dof_numbers _ _ _ hsv, ValValSem.arrayOf]
    simp only [ha0, ha1, Nat.zero_div, Nat.zero_mul, and_self,
      if_true]
  exact reshapeBase_ok hrref (by simpa only [FlatArray.length_ofFn] using hdim)

end GLang.PartialAdequacy
