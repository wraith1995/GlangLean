import GLang.Proofs.Value.Queries.ValueQueryLocality
import GLang.Proofs.Value.Runtime.RuntimeValueQueryFinite
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectOracle

/-! The guarded oracle unfolds on finite dependency graphs. Runtime typing
supplies this condition; it is not claimed for arbitrary malformed syntax. -/
namespace GLang.PartialDirectLocality
open DirectOracleWF ValueQueryDependencies

/-- Every observation reachable through a child of a certified query is
strictly below that query's rank. -/
theorem guarded_child (root : Query) (hf : ValueQueryDependencies.Finite root.node)
    {child : Node} (hc : child ∈ children root.node) :
    OracleAgreement
      (PartialDirectOracle.smallerOracle root (fun q _ => PartialDirectOracle.query q))
      PartialDirectOracle.oracle child := by
  intro Γ p s e hr ρ Δ
  have hlt := lt_of_le_of_lt (hr.rank_le (hf.child hc)) (rank_child_lt hf hc)
  have hmeasure : (Query.mk ρ Γ Δ p s e).certifiedMeasure < root.certifiedMeasure := hlt
  simp only [PartialDirectOracle.smallerOracle, PartialDirectOracle.oracle, dif_pos hmeasure]

/-- The dimension equation holds once its dependency graph is finite. -/
theorem oracle_eq (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr)
    (hf : ValueQueryDependencies.Finite (.space Γ (.ffs p s e))) :
    PartialDirectOracle.oracle ρ Γ Δ p s e =
      ffsDimensionPartial p
        (s.shpOfPartial (PartialDirectOracle.oracle ρ Γ Δ))
        (denotValB_partial PartialDirectOracle.oracle ρ Γ Δ e) := by
  let root : Query := ⟨ρ, Γ, Δ, p, s, e⟩
  change PartialDirectOracle.query root = _
  rw [PartialDirectOracle.query_eq]
  unfold PartialDirectOracle.step
  have hpos : root.certifiedMeasure ≠ 0 := Nat.ne_of_gt ((finite_iff_rank_pos root.node).mp hf)
  rw [if_neg hpos]
  have hp := guarded_child root hf (child := .space Γ s) (by simp [root, Query.node, children])
  have hw := guarded_child root hf (child := .expr Γ e) (by simp [root, Query.node, children])
  have hs := (PartialValueDomains.PartialSpaceAgreement.observations _ _ s (hp.space ρ Δ)).1
  have he := hw.eval ρ Γ Δ e
  exact congrArg₂ (ffsDimensionPartial p) hs he

/-- A successful query cannot come from an uncertified dependency cycle. -/
theorem finite_of_success {ρ : ValEnvSem} {Γ : List ValTy} {Δ : List ValValSem}
    {p : ValFFSProp} {s : ValSpace} {e : ValExpr} {n : Nat}
    (h : PartialDirectOracle.oracle ρ Γ Δ p s e = .ok n) :
    ValueQueryDependencies.Finite (.space Γ (.ffs p s e)) := by
  apply (finite_iff_rank_pos _).mpr
  by_contra hn
  have hz : rank (.space Γ (.ffs p s e)) = 0 := by omega
  change PartialDirectOracle.query ⟨ρ, Γ, Δ, p, s, e⟩ = _ at h
  rw [PartialDirectOracle.query_eq] at h
  simp only [PartialDirectOracle.step, Query.certifiedMeasure, Query.node, hz, if_pos rfl] at h
  contradiction

/-- Existing runtime formation provides the certificate for a closed query. -/
theorem oracle_eq_of_valid {ε : ValCtx} (hv : RuntimeValue.ValCtxValid ε)
    (ρ : ValEnvSem) (p : ValFFSProp) (s : ValSpace) (e : ValExpr)
    (hs : RuntimeValue.ValSValid ε (.ffs p s e)) :
    PartialDirectOracle.oracle ρ [] [] p s e =
      ffsDimensionPartial p
        (s.shpOfPartial (PartialDirectOracle.oracle ρ [] []))
        (denotValB_partial PartialDirectOracle.oracle ρ [] [] e) :=
  oracle_eq ρ [] [] p s e (RuntimeValue.validSpace_queryFinite hv hs)

theorem oracle_operand_error (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr) (err : DimError)
    (hf : ValueQueryDependencies.Finite (.space Γ (.ffs p s e)))
    (he : denotValB_partial PartialDirectOracle.oracle ρ Γ Δ e = .error err) :
    PartialDirectOracle.oracle ρ Γ Δ p s e = .error err := by
  rw [oracle_eq ρ Γ Δ p s e hf, he]
  cases hs : s.shpOfPartial (PartialDirectOracle.oracle ρ Γ Δ) with
  | error er => cases er; cases err; rfl
  | ok sh => rfl

theorem oracle_shape_error (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr) (err : DimError)
    (hf : ValueQueryDependencies.Finite (.space Γ (.ffs p s e)))
    (hs : s.shpOfPartial (PartialDirectOracle.oracle ρ Γ Δ) = .error err) :
    PartialDirectOracle.oracle ρ Γ Δ p s e = .error err := by
  rw [oracle_eq ρ Γ Δ p s e hf, hs]
  rfl

theorem oracle_matrix (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr) (m n : Nat) (a : FlatArray)
    (hf : ValueQueryDependencies.Finite (.space Γ (.ffs p s e)))
    (hs : s.shpOfPartial (PartialDirectOracle.oracle ρ Γ Δ) = .ok [m, n])
    (he : denotValB_partial PartialDirectOracle.oracle ρ Γ Δ e = .ok (.array a))
    (hlen : a.length = m * n) :
    PartialDirectOracle.oracle ρ Γ Δ p s e =
      .ok (ffsDim p [m, n] (denotAsMatrix m n a.get).rank) := by
  rw [oracle_eq ρ Γ Δ p s e hf, hs, he]
  exact ffsDimensionPartial_matrix p m n a hlen

end GLang.PartialDirectLocality
