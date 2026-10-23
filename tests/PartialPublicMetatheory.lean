import GLang.Metatheory

open GLang

-- Checked progress and adequacy refer to the exact same selected expression
-- and the live partial evaluator, under an actual partial creation history.
example (rho : ValEnvSem) :
    ∃ v tauV, Operational.Term ∅ ∅ ∅ (.real 3) .one v tauV ∧
      ValExpr.inferType v = tauV ∧
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV ∧
      Adequacy.PartialDirect.ResultAgree ⟨∅⟩ rho [] [] [] (Basis.tof .one) tauV
        (denotBasis ⟨∅⟩ .one) (denotTerm ⟨∅⟩ (.real 3))
        (denotValB_partial PartialDirectOracle.oracle rho [] [] v) ∧
      Adequacy.PartialDirect.AgreeDims ⟨∅⟩ rho [] [] [] (Basis.tof .one) tauV
        (denotBasis ⟨∅⟩ .one) :=
  Metatheory.checkedProgressAdequacy
    (PartialAdequacy.Consistent.empty _ rho) (.real_lit 3) .one

-- Progress accepts the same value-context-indexed formation as preservation.
example (h : Operational.ContextHistory Delta Gamma GammaV Psi)
    (ht : HasType Delta Gamma e (Basis.tof b)) (hb : Basis.BasisValid Gamma b) :
    ∃ v tauV, Operational.Term Delta Gamma Psi e b v tauV ∧
      ValExpr.inferType v = tauV ∧
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV :=
  Metatheory.progress h ht hb

example (rho : ValEnvSem) :
    ∃ sv, Operational.Space ∅ ∅ .real sv ∧
      ValSpace.shpOfPartial (PartialDirectOracle.oracle rho [] []) sv =
        .ok (srcShp ⟨∅⟩ [] .real) :=
  Metatheory.spaceProgressAdequacy
    (PartialAdequacy.Consistent.empty _ rho) .real

-- Public consistency supplies the semantic premise of value soundness.
example (hc : Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho) :
    RuntimeValue.PartialEnvWF PartialDirectOracle.oracle GammaV rho :=
  hc.valueEnv
