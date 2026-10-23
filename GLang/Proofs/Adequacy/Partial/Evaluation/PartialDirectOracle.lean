import GLang.Proofs.Value.DenotationChecks
import GLang.Proofs.Adequacy.Foundations.QueryState

namespace GLang.PartialDirectOracle
open DirectOracleWF

noncomputable def smallerOracle (q : Query)
    (rec : (q' : Query) → q'.certifiedMeasure < q.certifiedMeasure → Except DimError Nat) :
    PartialFFSOracleSem := fun ρ Γ Δ p s e =>
  let q' : Query := ⟨ρ, Γ, Δ, p, s, e⟩
  if h : q'.certifiedMeasure < q.certifiedMeasure then rec q' h else .error .mismatch

noncomputable def step (q : Query)
    (rec : (q' : Query) → q'.certifiedMeasure < q.certifiedMeasure → Except DimError Nat) :
    Except DimError Nat :=
  if q.certifiedMeasure = 0 then .error .mismatch else
  let orc := smallerOracle q rec
  ffsDimensionPartial q.prop
    (q.parent.shpOfPartial (orc q.rho q.Gamma q.Delta))
    (denotValB_partial orc q.rho q.Gamma q.Delta q.witness)

noncomputable def query : Query → Except DimError Nat :=
  (measure Query.certifiedMeasure).wf.fix step

noncomputable def oracle : PartialFFSOracleSem := fun ρ Γ Δ p s e =>
  query ⟨ρ, Γ, Δ, p, s, e⟩

theorem query_eq (q : Query) :
    query q = step q (fun q' _ => query q') := by
  rw [query, WellFounded.fix_eq]
  rfl

/-- Only decreasing callbacks are answered by recursion. -/
theorem smallerOracle_of_lt (q q' : Query)
    (rec : (q' : Query) → q'.certifiedMeasure < q.certifiedMeasure → Except DimError Nat)
    (h : q'.certifiedMeasure < q.certifiedMeasure) :
    smallerOracle q rec q'.rho q'.Gamma q'.Delta q'.prop q'.parent q'.witness = rec q' h := by
  cases q'
  simp only [smallerOracle, dif_pos h]

/-- A recursive cycle is not silently given rank or dimension zero. -/
theorem smallerOracle_self (q : Query)
    (rec : (q' : Query) → q'.certifiedMeasure < q.certifiedMeasure → Except DimError Nat) :
    smallerOracle q rec q.rho q.Gamma q.Delta q.prop q.parent q.witness =
      .error .mismatch := by
  cases q
  simp [smallerOracle]

end GLang.PartialDirectOracle

namespace GLang.Adequacy.Partial

noncomputable abbrev shapeOf (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (s : ValSpace) : Except DimError (List Nat) :=
  s.shpOfPartial (PartialDirectOracle.oracle ρ Γ Δ)

noncomputable abbrev dimOf (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (s : ValSpace) : Except DimError Nat :=
  s.dofPartial (PartialDirectOracle.oracle ρ Γ Δ)

noncomputable abbrev evalVal (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (e : ValExpr) : Except DimError ValValSem :=
  denotValB_partial PartialDirectOracle.oracle ρ Γ Δ e

noncomputable abbrev evalValCheckedAt (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (τ : ValTy) (e : ValExpr) : Except DimError τ.carrierEl :=
  denotValB_partialCheckedAt PartialDirectOracle.oracle ρ Γ Δ τ e

/-- The actual error-aware evaluator satisfies membership in the partial type
interpretation. This is a supporting validation theorem, not source adequacy
or extensionality of arbitrary externally supplied callbacks. -/
theorem evalValCheckedAt_sound (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (τ : ValTy) (e : ValExpr) :
    PartialValType.ResultContains
      (denotValTyPartial PartialDirectOracle.oracle ρ Γ Δ τ)
      (evalValCheckedAt ρ Γ Δ τ e) :=
  denotValB_partialCheckedAt_sound PartialDirectOracle.oracle ρ Γ Δ τ e

end GLang.Adequacy.Partial
