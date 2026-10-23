import GLang.Proofs.Adequacy.Total.DirectOracleWF

/-! The guarded rank equation needs finite query dependencies. Value typing
provides that evidence for compiled programs; it is not assumed for all raw syntax. -/
namespace GLang.DirectOracleLocality
open DirectOracleWF ValueQueryDependencies

 theorem guarded_witness_eval_eq (root : Query) (hf : Finite root.node) :
    denotValB_semS (smallerDerivedOracle root (fun q _ => derivedDirectQuery q))
      root.rho root.Gamma root.Delta root.witness =
    denotValB_semS derivedDirectOracle root.rho root.Gamma root.Delta root.witness := by
  exact (guarded_child root hf (child := .expr root.Gamma root.witness)
    (by simp [Query.node,children])).eval root.rho root.Gamma root.Delta root.witness

 theorem derivedDirectQuery_rank_eq_production (root : Query) (hf : Finite root.node) :
    derivedDirectQuery root =
      ffsDim root.prop (ValSpace.shpOf
        (derivedDirectOracle root.rho root.Gamma root.Delta) root.parent)
        (ffsOperandRank derivedDirectOracle root.rho root.Gamma root.Delta
          root.parent root.witness) := by
  rw [derivedDirectQuery_eq,derivedStep]
  have hz : root.derivedMeasure ≠ 0 := Nat.ne_of_gt ((finite_iff_rank_pos _).mp hf)
  rw [if_neg hz]
  dsimp only
  unfold ffsOperandRank
  rw [guarded_parent_shpOf_eq root hf,guarded_witness_eval_eq root hf]

end GLang.DirectOracleLocality
