import GLang.Proofs.Value.DenotationChecks
import GLang.Proofs.Value.Queries.ValueQueryDependencies

namespace GLang.DirectOracleWF

/-- All data at one semantic fundamental-subspace dimension query. -/
structure Query where
  rho : ValEnvSem
  Gamma : List ValTy
  Delta : List ValValSem
  prop : ValFFSProp
  parent : ValSpace
  witness : ValExpr

def Query.node (q : Query) : ValueQueryDependencies.Node :=
  .space q.Gamma (.ffs q.prop q.parent q.witness)

/-- Derived from the actual dependency graph, including substituted result
types. The semantic environment and runtime values do not affect this rank. -/
noncomputable def Query.certifiedMeasure (q : Query) : Nat :=
  ValueQueryDependencies.rank q.node

end GLang.DirectOracleWF
