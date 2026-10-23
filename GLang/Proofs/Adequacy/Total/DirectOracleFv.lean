import GLang.Proofs.Adequacy.Total.DirectOracleLocality
import GLang.Proofs.Adequacy.Foundations.FvIrrel

namespace GLang.DirectOracleFv

open DirectOracleWF
open DirectOracleLocality

private theorem derivedDirectQuery_fvIrrel_query (root : Query) :
    forall (y : VName) (value : ValValSem),
      ValTyCtxFresh y root.Gamma ->
      y ∉ ValSpace.fv root.parent ->
      y ∉ ValExpr.fv root.witness ->
      derivedDirectQuery
          { root with rho := root.rho.update y value } =
        derivedDirectQuery root := by
  generalize hn : Query.derivedMeasure root = n
  induction n using Nat.strong_induction_on generalizing root with
  | h n ih =>
      intro y value hGamma hparent hwitness
      let guarded : FFSOracleSem :=
        smallerDerivedOracle root
          (fun query _ => derivedDirectQuery query)
      have guarded_fv : OracleFvIrrel guarded := by
        intro rho name replacement Gamma Delta property parent witness
          hGamma' hparent' hwitness'
        simp only [guarded, smallerDerivedOracle]
        let updated : Query :=
          ⟨rho.update name replacement, Gamma, Delta,
            property, parent, witness⟩
        let plain : Query :=
          ⟨rho, Gamma, Delta, property, parent, witness⟩
        change
          (if _ : Query.derivedMeasure updated < Query.derivedMeasure root then
              derivedDirectQuery updated
            else 0) =
          (if _ : Query.derivedMeasure plain < Query.derivedMeasure root then
              derivedDirectQuery plain
            else 0)
        have hmeasure : Query.derivedMeasure updated =
            Query.derivedMeasure plain := by
          rfl
        by_cases hlt : Query.derivedMeasure plain <
            Query.derivedMeasure root
        · have hlt' : Query.derivedMeasure updated <
              Query.derivedMeasure root := by
            simpa only [hmeasure] using hlt
          rw [dif_pos hlt, dif_pos hlt']
          have hrec := ih (Query.derivedMeasure plain)
            (by simpa only [hn] using hlt) plain rfl name replacement
            hGamma' hparent' hwitness'
          simpa only [updated, plain] using hrec
        · have hlt' : ¬ Query.derivedMeasure updated <
              Query.derivedMeasure root := by
            simpa only [hmeasure] using hlt
          rw [dif_neg hlt, dif_neg hlt']
      let updatedRoot : Query :=
        { root with rho := root.rho.update y value }
      have hrootMeasure : Query.derivedMeasure updatedRoot =
          Query.derivedMeasure root := by
        rfl
      have hguardedRoot :
          smallerDerivedOracle updatedRoot
              (fun query _ => derivedDirectQuery query) = guarded := by
        funext rho Gamma Delta property parent witness
        simp only [guarded, smallerDerivedOracle]
        rw [hrootMeasure]
      rw [derivedDirectQuery_eq updatedRoot, derivedDirectQuery_eq root]
      simp only [derivedStep,hrootMeasure]
      split
      · rfl
      rw [hguardedRoot]
      rw [ValSpace.shpOf_update_of_not_mem_fv guarded_fv
        root.rho y value root.Gamma root.Delta hGamma
        root.parent hparent]
      unfold ffsOperandRank
      rw [ValSpace.shpOf_update_of_not_mem_fv guarded_fv
        root.rho y value root.Gamma root.Delta hGamma
        root.parent hparent]
      rw [denotValB_semS_update_of_not_mem_fv guarded_fv
        root.rho y value root.witness root.Gamma root.Delta
        hwitness hGamma]

/-- The direct oracle satisfies the current context-aware FV contract without
passing through any finite approximation or eventual-value fallback. -/
theorem derivedDirectOracle_fvIrrel :
    OracleFvIrrel derivedDirectOracle := by
  intro rho y value Gamma Delta property parent witness
    hGamma hparent hwitness
  exact derivedDirectQuery_fvIrrel_query
    ⟨rho, Gamma, Delta, property, parent, witness⟩
    y value hGamma hparent hwitness

theorem derivedDirectOracle_bound
    (rho : ValEnvSem) (Gamma : List ValTy) (Delta : List ValValSem)
    (property : ValFFSProp) (parent : ValSpace) (witness : ValExpr) :
    derivedDirectOracle rho Gamma Delta property parent witness <=
      ffsDimUB property
        (ValSpace.shpOf (derivedDirectOracle rho Gamma Delta) parent) := by
  exact derivedDirectQuery_le_dimUB
    ⟨rho, Gamma, Delta, property, parent, witness⟩

/-- The numerical specification unfolds only finite query dependencies. -/
theorem derivedDirectOracle_spec : OracleSpec derivedDirectOracle where
  bound := derivedDirectOracle_bound
  rank := by
    intro rho property parent witness _hinfer hf
    exact derivedDirectQuery_rank_eq_production
      ⟨rho, [], [], property, parent, witness⟩ hf
  fvIrrel := derivedDirectOracle_fvIrrel

end GLang.DirectOracleFv
