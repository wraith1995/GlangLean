import GLang.Proofs.Adequacy.Raw.Conversion.RawCobAdequacyCore
import GLang.Proofs.Adequacy.Foundations.AgreeBasics

namespace GLang

open scoped BigOperators
open Basis (BasisValid)

private theorem raw_cob_term_space_kind
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {s : Space} {tauV : ValTy} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : RawAgree orc sigma rho Ds Gv Dv (.space s) tauV B x y) :
    exists sv, tauV = .space sv := by
  cases tauV with
  | space sv => exact ⟨sv, rfl⟩
  | piTy _ _ => simpa only [RawAgree] using h

private theorem raw_cob_term_space_array
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {s : Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : RawAgree orc sigma rho Ds Gv Dv
      (.space s) (.space sv) B x y) :
    exists a, y = .array a := by
  cases y with
  | array a => exact ⟨a, rfl⟩
  | fn T f => simpa only [RawAgree] using h

/-- Ordinary exact-basis trace for `S.Term.cob`.  The child term may have any
strengthened realization of the source basis; base-kind raw agreement forces
it to be an array, whose length is then aligned with the requested result
realization through `CobAgree` and the sibling space theorem. -/
theorem arm_cob_trace
    {orc : FFSOracleSem}
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
    (ihTy : RawMTyAtSubctx orc Gamma Psi b0 (.space sv))
    (ihE : RawTermDofFactsSubctx orc Delta Gamma Psi e b1 v tauV)
    (ihCob : RawCobFactsSubctx orc Gamma Psi b1 env0 b0)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv) :
    RawMTermTraceSubctx orc Delta Gamma Psi e b0
      (.ttv sv (ValExpr.reshapBase env0 (.tprod sv sv))
        (ValExpr.reshapBase v sv)) (.space sv) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have child := ihE.trace hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨y, hy, hA⟩ := child.result
  have hC := ihCob.agree hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨_, hN⟩ := raw_cob_basis_length orc hbv
    ihSpace hsub hle.2 hc
  have hsof : Basis.sof b1 = Basis.sof b0 := S.Cob.sof_eq hbb
  rw [htof1] at hA
  obtain ⟨sv', rfl⟩ := raw_cob_term_space_kind hA
  obtain ⟨a, rfl⟩ := raw_cob_term_space_array hA
  simp only [RawAgree] at hA
  have hlenA := LegacyAgree.length hA
  have hcA := LegacyAgree.coords hA
  simp only [CobAgree] at hC
  obtain ⟨hT, E, hE, hElen, hrow⟩ := hC
  rw [← hsof] at hN
  have hNN : ValSpace.dof (orc rho [] []) sv =
      ((denotBasis sigma b1).atSpace
        (denotSpaceAux sigma [] (Basis.sof b1))).length := by
    rw [← hN]
    exact hT
  have hNN' : ValSpace.dof (orc rho [] []) sv' =
      ((denotBasis sigma b1).atSpace
        (denotSpaceAux sigma [] (Basis.sof b1))).length :=
    hlenA.1.symm
  have hElen' : E.length =
      ValSpace.dof (orc rho [] []) (.tprod sv sv) := by
    simpa only [ValSpace.dof_tprod, hNN] using hElen
  have haLen : a.length = ValSpace.dof (orc rho [] []) sv :=
    hlenA.2.trans (hNN'.trans hNN.symm)
  have result : RawResultAgree orc sigma rho [] [] []
      (Basis.tof b0) (.space sv) (denotBasis sigma b0)
      (denotTerm sigma e)
      (denotValB_semS orc rho [] []
        (.ttv sv (ValExpr.reshapBase env0 (.tprod sv sv))
          (ValExpr.reshapBase v sv))) := by
    simp only [ValExpr.reshapBase]
    have hreshapeE : denotValB_semS orc rho [] []
        (.reshap env0 (.space (.tprod sv sv)) (.space (.tprod sv sv))) =
          .ok (.array E) :=
      denotValB_semS_reshap_space_ok orc rho [] [] env0 (.tprod sv sv)
        E hE hElen'
    have hreshapeA : denotValB_semS orc rho [] []
        (.reshap v (.space sv) (.space sv)) = .ok (.array a) :=
      denotValB_semS_reshap_space_ok orc rho [] [] v sv a hy haLen
    rw [denotValB_semS.eq_12, hreshapeE, hreshapeA]
    have hshape : ValueShape.ttv (orc rho [] []) sv
        (ValExpr.inferSpaceCtx []
          (.reshap env0 (.space (.tprod sv sv)) (.space (.tprod sv sv))))
        (ValExpr.inferSpaceCtx [] (.reshap v (.space sv) (.space sv))) E a := by
      exact ⟨⟨hElen', haLen⟩, rfl, rfl⟩
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hshape]
    refine ⟨_, rfl, ?_⟩
    rw [htof0]
    rw [RawAgree.eq_def]
    rw [← hsof]
    simp only [ValExpr.inferSpaceCtx, ValTy.spaceOf, ValValSem.arrayOf]
    rw [LegacyAgree.space_iff]
    refine ⟨hN, FlatArray.length_ofFn _ _, ?_⟩
    rw [hcA, Fin.raw_sum_cast_of_eq hNN',
      Fin.raw_sum_cast_of_eq hNN]
    simp only [Fin.val_cast]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hrow j])]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_smul]
    congr 1
    rw [FlatArray.get_ofFn_lt _ _ _ (by rw [hNN]; exact i.isLt)]
    rw [if_neg (by rw [hNN]; exact Nat.not_le.mpr i.isLt)]
    rw [Fin.sum_univ_eq_sum_range (fun j => a.get j *
      E.get (j * ((denotBasis sigma b1).atSpace
        (denotSpaceAux sigma [] (Basis.sof b1))).length + i))]
    apply Finset.sum_congr (by rw [hNN])
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hij : ValSpace.dof (orc rho [] []) sv * j + i <
        ValSpace.dof (orc rho [] []) sv *
          ValSpace.dof (orc rho [] []) sv := by
      calc
        ValSpace.dof (orc rho [] []) sv * j + i <
            ValSpace.dof (orc rho [] []) sv * j +
              ValSpace.dof (orc rho [] []) sv :=
          Nat.add_lt_add_left (lt_of_lt_of_eq i.isLt hNN.symm) _
        _ = ValSpace.dof (orc rho [] []) sv * (j + 1) := by ring
        _ ≤ ValSpace.dof (orc rho [] []) sv *
            ValSpace.dof (orc rho [] []) sv :=
          Nat.mul_le_mul_left _ hj'
    rw [hNN, Nat.mul_comm]
    exact mul_comm _ _
  exact ⟨result, targetDims⟩

/-- The complete term-side pair consumed by the direct mutual induction. -/
theorem arm_cob_facts
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b0 b1 : Basis} {v env0 : ValExpr}
    {sv : ValSpace} {tauV : ValTy}
    (htof0 : Basis.tof b0 = .space (Basis.sof b0))
    (htof1 : Basis.tof b1 = .space (Basis.sof b1))
    (ht : Nonempty (HasType Delta Gamma e (Basis.tof b0)))
    (hbv : BasisValid Gamma b0)
    (hTy : S.TyAt Gamma Psi b0 (.space sv))
    (he : S.Term Delta Gamma Psi e b1 v tauV)
    (hbb : S.Cob Gamma Psi b1 env0 b0)
    (hes : S.Space Gamma Psi (Basis.sof b0) sv)
    (ihTy : RawMTyAtSubctx orc Gamma Psi b0 (.space sv))
    (ihE : RawTermDofFactsSubctx orc Delta Gamma Psi e b1 v tauV)
    (ihCob : RawCobFactsSubctx orc Gamma Psi b1 env0 b0)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv) :
    RawTermDofFactsSubctx orc Delta Gamma Psi e b0
      (.ttv sv (ValExpr.reshapBase env0 (.tprod sv sv))
        (ValExpr.reshapBase v sv)) (.space sv) :=
  ⟨arm_cob_trace htof0 htof1 ht hbv hTy he hbb hes
      ihTy ihE ihCob ihSpace,
    arm_cob_dof⟩

end GLang
