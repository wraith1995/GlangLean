import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectOracle
import GLang.Value.Supporting.StrictTyping

namespace GLang

-- Arrays need not have the same syntactic space to be added.
def heterogeneousAdd : ValExpr := .vadd .real (.rlit 2) (.zero (.tprod .real .real))
def heterogeneousAdd_typed : ValHasType ∅ heterogeneousAdd (.space .real) :=
  .vadd (.rlit 2) (.zero (.tprod .real .real)) .real

def mismatchedAdd : ValExpr := .vadd .real (.rlit 2) (.zero .empty)
def mismatchedAdd_typed : ValHasType ∅ mismatchedAdd (.space .real) :=
  .vadd (.rlit 2) (.zero .empty) .real

example (ρ : ValEnvSem) :
    denotValB_partial PartialDirectOracle.oracle ρ [] [] mismatchedAdd = .error .mismatch := by
  simp [mismatchedAdd, denotValB_partial, PartialValueEval.withDimensions,
    PartialValueEval.dimensions, ValExpr.inferSpaceCtx, ValSpace.dofPartial,
    ValSpace.shpOfPartial, ValValSem.bindArrays, ValValSem.bindArray,
    ValValSem.arrayOf, FlatArray.ofFn, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

-- Function operands remain excluded: all operand types must have base kind.
example (Γv : ValCtx) (x : VName) (T U : ValTy) (τ : ValTy) :
    ¬ Nonempty (ValHasType Γv (.vadd .real (.var x (.piTy T U)) (.rlit 0)) τ) := by
  rintro ⟨h⟩
  cases h with
  | vadd hbad _ _ => cases hbad

end GLang
