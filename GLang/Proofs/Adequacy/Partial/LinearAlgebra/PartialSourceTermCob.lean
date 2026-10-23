import GLang.Proofs.Adequacy.Partial.Functions.PartialSourceLinearApply
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceLinearSums
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCobMotives

namespace GLang.PartialAdequacy
open scoped BigOperators
open Basis (BasisValid)

theorem arm_cob_trace
    {orc : PartialFFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b0 b1 : Basis} {v env0 : ValExpr}
    {sv : ValSpace} {tauV : ValTy}
    (htof0 : Basis.tof b0 = .space (Basis.sof b0))
    (htof1 : Basis.tof b1 = .space (Basis.sof b1))
    (_ht : Nonempty (HasType Delta Gamma e (Basis.tof b0)))
    (hbv : BasisValid Gamma b0)
    (_hTy : S.TyAt Gamma Psi b0 (.space sv))
    (_he : S.Term Delta Gamma Psi e b1 v tauV)
    (hbb : S.Cob Gamma Psi b1 env0 b0)
    (_hes : S.Space Gamma Psi (Basis.sof b0) sv)
    (ihTy : MTyAtSubctx orc Gamma Psi b0 (.space sv))
    (ihE : TermFactsSubctx orc Delta Gamma Psi e b1 v tauV)
    (ihCob : CobFactsSubctx orc Gamma Psi b1 env0 b0)
    (ihSpace : MSpaceSubctx orc Gamma Psi (Basis.sof b0) sv) :
    MTermSubctx orc Delta Gamma Psi e b0
      (.ttv sv (ValExpr.reshapBase env0 (.tprod sv sv))
        (ValExpr.reshapBase v sv)) (.space sv) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have child := ihE.trace hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨y, hy, ha⟩ := child.result
  have hC := ihCob.agree hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hB := denotBasis_atSpace_isListBasis sigma Gamma' b0
    (raw_basisValid_mono hbv hle.2) hc.ctxWF_nl hc.envWF_nl
  have hsof := hbb.sof_eq
  rw [htof1] at ha
  cases tauV with
  | piTy d c => simp only [Agree] at ha
  | space sv' =>
    cases y with
    | fn A f => simp only [Agree] at ha
    | array a =>
      simp only [Agree] at ha
      rw [hsof] at ha
      obtain ⟨n, hn, hslen, halen, hcoords⟩ := ha
      dsimp only [CobAgree] at hC
      rw [hsof] at hC
      obtain ⟨E,hE,hT,hElen,hrow⟩ := hC
      let S := (denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b0))
      let T := (denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))
      have hd : sv.dofPartial (orc rho [] []) = .ok n := by
        have hdim := shape_dof (ihSpace hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
        rw [hB.finrank_eq, hT, hslen] at hdim
        exact hdim
      have hmat := reshapeBase_ok hE (by simpa only [hElen, hslen] using dof_tprod_ok hd hd)
      have hvec := reshapeBase_ok hy (by simpa only [halen] using hd)
      have hout := eval_ttv hmat hvec rfl hd hd hd hd
        (by simpa only [hslen] using hElen) halen
      refine ⟨⟨_,hout,?_⟩,targetDims⟩
      rw [htof0, agree_space_iff hd]
      refine ⟨hT.trans hslen, FlatArray.length_ofFn _ _, ?_⟩
      rw [hcoords]
      have hrows : ∀ j : Fin n, S.getD j.val 0 =
          ∑ i : Fin n, E.get (j.val*n+i.val) • T.getD i.val 0 := by
        intro j
        have hj := hrow (Fin.cast hslen.symm j)
        rw [Fin.raw_sum_cast_of_eq hslen] at hj
        simpa only [S,T,hslen,Fin.val_cast] using hj
      change (∑ j : Fin n, a.get j.val • S.getD j.val 0) = _
      rw [Finset.sum_congr rfl (fun j _ => by rw [hrows j])]
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_smul]
      congr 1
      rw [FlatArray.get_ofFn_lt _ _ _ i.isLt, if_neg (Nat.not_le.mpr i.isLt)]
      rw [Fin.sum_univ_eq_sum_range (fun j => a.get j * E.get (j*n+i.val))]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.mul_comm]
      exact mul_comm _ _

end GLang.PartialAdequacy
