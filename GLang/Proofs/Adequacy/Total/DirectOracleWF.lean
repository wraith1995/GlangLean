import GLang.Proofs.Adequacy.Foundations.FvIrrel
import GLang.Proofs.Adequacy.Foundations.QueryStateOpening
import GLang.Proofs.Value.Queries.ValueQueryTotalLocality

/-! The compatibility oracle uses the same certified dependency graph as the
error-aware current oracle. Its rank equation is proved on finite queries;
malformed cyclic raw syntax is not claimed to satisfy that equation. -/
namespace GLang.DirectOracleWF
open ValueQueryDependencies

noncomputable abbrev Query.derivedMeasure := Query.certifiedMeasure
abbrev Query.derivedMeasure_open_push_prefix := Query.certifiedMeasure_open_push_prefix

noncomputable def smallerDerivedOracle (q : Query)
    (rec : (q' : Query) → q'.derivedMeasure < q.derivedMeasure → Nat) :
    FFSOracleSem := fun ρ Γ Δ p s e =>
  let q' : Query := ⟨ρ,Γ,Δ,p,s,e⟩
  if h : q'.derivedMeasure < q.derivedMeasure then rec q' h else 0

noncomputable def derivedStep (q : Query)
    (rec : (q' : Query) → q'.derivedMeasure < q.derivedMeasure → Nat) : Nat :=
  if q.derivedMeasure = 0 then 0 else
  let orc := smallerDerivedOracle q rec
  ffsDim q.prop (ValSpace.shpOf (orc q.rho q.Gamma q.Delta) q.parent)
    (ffsOperandRank orc q.rho q.Gamma q.Delta q.parent q.witness)

noncomputable def derivedDirectQuery : Query → Nat :=
  (measure Query.derivedMeasure).wf.fix derivedStep

noncomputable def derivedDirectOracle : FFSOracleSem := fun ρ Γ Δ p s e =>
  derivedDirectQuery ⟨ρ,Γ,Δ,p,s,e⟩

theorem derivedDirectQuery_eq (q : Query) :
    derivedDirectQuery q = derivedStep q (fun q' _ => derivedDirectQuery q') := by
  rw [derivedDirectQuery,WellFounded.fix_eq]
  rfl

/-- Every query reached from a child of a finite root has smaller rank. -/
theorem guarded_child (root : Query) (hf : Finite root.node)
    {child : Node} (hc : child ∈ children root.node) :
    TotalQueryLocality.OracleAgreement
      (smallerDerivedOracle root (fun q _ => derivedDirectQuery q))
      derivedDirectOracle child := by
  intro Γ p s e hr ρ Δ
  have hlt := lt_of_le_of_lt (hr.rank_le (hf.child hc)) (rank_child_lt hf hc)
  have hmeasure : (Query.mk ρ Γ Δ p s e).derivedMeasure < root.derivedMeasure := hlt
  simp only [smallerDerivedOracle,derivedDirectOracle,dif_pos hmeasure]

theorem guarded_parent_shpOf_eq (root : Query) (hf : Finite root.node) :
    ValSpace.shpOf
      (smallerDerivedOracle root (fun q _ => derivedDirectQuery q) root.rho root.Gamma root.Delta)
      root.parent =
    ValSpace.shpOf (derivedDirectOracle root.rho root.Gamma root.Delta) root.parent := by
  have hp := guarded_child root hf (child := .space root.Gamma root.parent)
    (by simp [Query.node,children])
  exact (PaperValueDomains.leafAgreement_shapes _ _ root.parent
    (hp.space root.rho root.Delta)).1

theorem derivedDirectQuery_le_dimUB (root : Query) :
    derivedDirectQuery root ≤ ffsDimUB root.prop
      (ValSpace.shpOf (derivedDirectOracle root.rho root.Gamma root.Delta) root.parent) := by
  rw [derivedDirectQuery_eq,derivedStep]
  by_cases hz : root.derivedMeasure = 0
  · simp [hz]
  · rw [if_neg hz]
    have hf : Finite root.node := (finite_iff_rank_pos _).mpr (by
      change 0 < root.derivedMeasure
      omega)
    have hb := ffsDim_operandRank_le_ffsDimUB
      (smallerDerivedOracle root (fun q _ => derivedDirectQuery q))
      root.rho root.Gamma root.Delta root.prop root.parent root.witness
    rw [guarded_parent_shpOf_eq root hf] at hb
    simpa only [guarded_parent_shpOf_eq root hf] using hb

end GLang.DirectOracleWF
