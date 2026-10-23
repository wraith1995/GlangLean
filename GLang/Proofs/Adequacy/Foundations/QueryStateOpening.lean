import GLang.Proofs.Adequacy.Foundations.QueryState
import GLang.Proofs.Value.Queries.ValueQueryOpening

namespace GLang.DirectOracleWF

/-- Named opening and a bound-slot environment have the same certified
query rank, including raw terms for which no finite certificate exists. -/
theorem Query.certifiedMeasure_open_push_prefix
    (rho : ValEnvSem) (y : VName) (sigmaV : ValTy) (value : ValValSem)
    (G : List ValTy) (D : List ValValSem) (property : ValFFSProp)
    (parent : ValSpace) (witness : ValExpr)
    (_hGD : G.length = D.length)
    (hsigmaLC : ValTy.lc sigmaV)
    (_hfreshSigma : y ∉ ValTy.fv sigmaV)
    (_hfreshG : ∀ tauV, tauV ∈ G → y ∉ ValTy.fv tauV)
    (_hparent : y ∉ ValSpace.fv parent)
    (_hwitness : y ∉ ValExpr.fv witness) :
    Query.certifiedMeasure
        ⟨rho.update y value, ValTy.closePrefix (.var y sigmaV) G, D,
          property, ValSpace.openRec G.length (.var y sigmaV) parent,
          ValExpr.openRec G.length (.var y sigmaV) witness⟩ =
      Query.certifiedMeasure
        ⟨rho, G ++ [sigmaV], D ++ [value], property, parent, witness⟩ := by
  simpa only [Query.certifiedMeasure, Query.node, ValueQueryDependencies.openLast,
    ValueQueryDependencies.pushLast, ValSpace.openRec] using
    ValueQueryDependencies.rank_openLast hsigmaLC y (.space G (.ffs property parent witness))

end GLang.DirectOracleWF
