import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectOracle
import GLang.Value.Supporting.StrictTyping

namespace GLang

-- The vector's annotation differs from the matrix's contracted factor.
def heterogeneousContraction : ValExpr :=
  .ttv .real (.zero (.tprod .real .real)) (.zero (.tprod .real .real))
example : ValHasType ∅ heterogeneousContraction (.space .real) :=
  .ttv_space .real (.zero (.tprod .real .real)) (.zero (.tprod .real .real))

-- Scalar contraction likewise does not require identical operand annotations.
example : ValHasType ∅ (.ttv .real (.rlit 1) (.zero (.tprod .real .real))) (.space .real) :=
  .ttv_real .real (.rlit 1) (.zero (.tprod .real .real)) (by intros; intro h; cases h)

def mismatchedContraction : ValExpr :=
  .ttv .real (.zero (.tprod .real .real)) (.zero .empty)
example : ValHasType ∅ mismatchedContraction (.space .real) :=
  .ttv_space .real (.zero (.tprod .real .real)) (.zero .empty)
example (ρ : ValEnvSem) :
    denotValB_partial PartialDirectOracle.oracle ρ [] [] mismatchedContraction = .error .mismatch := by
  simp [mismatchedContraction, denotValB_partial, PartialValueEval.withDimensions,
    PartialValueEval.dimensions, ValExpr.inferSpaceCtx, ValSpace.dofPartial,
    ValSpace.shpOfPartial, ValValSem.bindArrays, ValValSem.bindArray,
    ValueShape.ttv,
    ValValSem.arrayOf, FlatArray.ofFn, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

end GLang
