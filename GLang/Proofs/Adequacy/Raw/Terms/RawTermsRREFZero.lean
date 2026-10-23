import GLang.Proofs.Adequacy.TermsRREF

/-!
# Zero-dimensional evaluator read-off for `terms_rref`

The positive-dimensional evaluator calculation lives with the main RREF
semantics development.  This small companion isolates the degenerate case:
all three flat arrays have length zero, so both reshapes succeed and the
RREF representation is the unique empty array.  No numerical property of
row reduction is needed.
-/

namespace GLang

/-- Evaluating the checked `terms_rref` expression in a zero-dimensional
ambient space produces the empty row-major matrix. -/
theorem denotValB_semS_termsRREFRep_zero_ok
    (orc : FFSOracleSem) (rho : ValEnvSem)
    {env0 env1 : ValExpr} {sv : ValSpace}
    {a0 a1 : FlatArray}
    (h0 : denotValB_semS orc rho [] [] env0 = .ok (.array a0))
    (h1 : denotValB_semS orc rho [] [] env1 = .ok (.array a1))
    (hsv : ValSpace.dof (orc rho [] []) sv = 0)
    (ha0 : a0.length = 0)
    (ha1 : a1.length = 0) :
    denotValB_semS orc rho [] []
        (ValExpr.reshapBase
          (.rrefRep env0
            (ValExpr.reshapBase env1 (.tprod sv sv)))
          (.tprod sv sv)) =
      .ok (.array (FlatArray.ofFn 0
        (termsRREFRepDenot 0 0 a0.get a1.get))) := by
  have hdim : ValSpace.dof (orc rho [] []) (.tprod sv sv) = 0 := by
    simp only [ValSpace.dof_tprod, hsv, Nat.zero_mul]
  have hinner : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env1 (.tprod sv sv)) = .ok (.array a1) := by
    apply denotValB_semS_reshap_space_ok
    · exact h1
    · exact ha1.trans hdim.symm
  have hrref : denotValB_semS orc rho [] []
      (.rrefRep env0 (ValExpr.reshapBase env1 (.tprod sv sv))) =
      .ok (.array (FlatArray.ofFn 0
        (termsRREFRepDenot 0 0 a0.get a1.get))) := by
    rw [denotValB_semS, h0, hinner]
    simp only [ValValSem.bindArrays, ValValSem.bindArray,
      ValExpr.reshapBase, ValExpr.inferSpaceCtx, ValTy.spaceOf_space,
      ValSpace.dof_tprod, hsv, ValValSem.arrayOf]
    simp only [ha0, ha1, Nat.zero_div, Nat.zero_mul, and_self,
      if_true]
  apply denotValB_semS_reshap_space_ok
  · exact hrref
  · simp only [FlatArray.length_ofFn, hdim]

end GLang
