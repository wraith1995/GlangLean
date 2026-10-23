import GLang.Proofs.Adequacy.Raw.RawApplicationOracleSpec
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialApplicationCompiled
import GLang.Proofs.Preservation.IndexedPreservationHelpers

namespace GLang
example (f a : ValExpr) (target : ValTy) :
    ValExpr.applyAt f a target =
      .reshap (.applyValue f a) target (ValExpr.inferType (.applyValue f a)) := rfl

-- At a function type, the conversion starts at the substituted codomain.
example (f a : ValExpr) (d c target : ValTy)
    (hf : ValExpr.inferType f = .piTy d c) :
    ValExpr.applyAt f a target =
      .reshap (.appV f (.reshap a d (ValExpr.inferType a))) target
        (ValTy.applyCodomain (.reshap a d (ValExpr.inferType a)) c) := by
  simp only [ValExpr.applyAt, ValExpr.applyValue, hf, ValTy.domain,
    ValExpr.inferType]

#print axioms RuntimeValue.TotalSubstitution.codomainLaw
#print axioms directApplicationOracle_spec
#print axioms PartialAdequacy.applyAt_agree
end GLang
