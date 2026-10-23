import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectLocality

/-!
A raw-syntax obstruction to unconditional application query-depth bounds.

This is intentionally ill-typed: `f` expects a real argument but is applied
to itself. Substituting it into the codomain nevertheless reproduces the
original application inside the inferred space's SVD witness. Evaluating that
witness asks for this same inferred space before evaluating the operand.
Thus a depth bound sufficient to remove every recursive-oracle guard cannot
be justified for all raw binary applications by structural syntax size alone.
This example makes no claim that a typed application can exhibit the cycle.
-/

namespace GLang

private def matrix : ValSpace := .tprod .real .real

private def recursiveCodomain : ValTy :=
  .space (.ffs .image matrix (.svds (.appV (.bvar 0) (.bvar 0))))

private def f : ValExpr :=
  .var "f" (.piTy (.space .real) recursiveCodomain)

private def call : ValExpr := .appV f f

example : ValExpr.inferType call =
    .space (.ffs .image matrix (.svds call)) := rfl

example : ValExpr.inferSpace call =
    .ffs .image matrix (.svds call) := rfl

open ValueQueryDependencies

private theorem raw_cycle_not_finite :
    ¬ ValueQueryDependencies.Finite (.space [] (.ffs .image matrix (.svds call))) := by
  intro hf
  have hw := hf.child (child := .expr [] (.svds call)) (by simp [children])
  have hc := hw.exprChild (child := .expr [] call) (by simp [exprChildren])
  have hcall := rank_child_lt hw (child := .expr [] call) (by simp [children, exprChildren])
  have hroot := rank_child_lt hf (child := .expr [] (.svds call)) (by simp [children])
  have hreturn := rank_child_lt hc
    (child := .space [] (.ffs .image matrix (.svds call)))
    (by simp [children, ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx,
      call, f, recursiveCodomain, matrix, ValTy.applyCodomain,
      ValTy.substBound,ValSpace.substBound,ValExpr.substBound,ValExpr.raise,ValTy.raise,ValSpace.raise])
  omega

example (ρ : ValEnvSem) :
    PartialDirectOracle.oracle ρ [] [] .image matrix (.svds call) = .error .mismatch := by
  change PartialDirectOracle.query ⟨ρ,[],[],.image,matrix,.svds call⟩ = _
  rw [PartialDirectOracle.query_eq]
  simp only [PartialDirectOracle.step,DirectOracleWF.Query.certifiedMeasure,
    DirectOracleWF.Query.node, rank, dif_neg raw_cycle_not_finite, Nat.reduceEqDiff, ite_true]

#print axioms RuntimeValue.validExpr_queryFinite
#print axioms PartialDirectLocality.oracle_eq_of_valid

end GLang
