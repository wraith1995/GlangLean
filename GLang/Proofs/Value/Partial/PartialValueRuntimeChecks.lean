import GLang.Proofs.Value.Partial.PartialValueCarrier
import GLang.Proofs.Value.Partial.PartialValueRuntimeRelation

/-! Runtime boundaries for independently realized value types. -/
namespace GLang.PartialValueEval

/-- Every successful boundary check has the declared dependent type. -/
theorem checkResult_sound (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy)
    (r : Except DimError ValValSem) :
    PartialValType.ResultContains (denotValTyPartial orc ρ Γ Δ t)
      (checkResult orc ρ Γ Δ t r) := by
  cases r with
  | error e => exact PartialValType.resultContains_error _ _
  | ok v =>
    cases h : t.carrierFromVal v with
    | error e => simpa [checkResult, h] using
        (PartialValType.resultContains_error (denotValTyPartial orc ρ Γ Δ t) e)
    | ok a => simpa [checkResult, h] using checkValTyPartial_sound orc ρ Γ Δ t a

/-- The boundary check is the existing recursive validator after decoding. -/
theorem checkResult_eq_validate (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy)
    (r : Except DimError ValValSem) :
    checkResult orc ρ Γ Δ t r =
      PartialValueDomains.validate (denotValTyPartial orc ρ Γ Δ t)
        (r.bind t.carrierFromVal) := by
  cases r with
  | error e => simp [checkResult, Except.bind]
  | ok v =>
    cases h : t.carrierFromVal v with
    | error e => simp [checkResult, h, Except.bind]
    | ok a =>
      simp only [checkResult, h, Except.bind, checkValTyPartial]
      cases denotValTyPartial orc ρ Γ Δ t <;> rfl

/-- Checking preserves the full recursive relation at coherent types; it does
not merely establish the lengths of immediate array results. -/
theorem checkResult_related (orc : PartialFFSOracleSem) (ρ ρ' : ValEnvSem)
    (Γ Γ' : List ValTy) (Δ Δ' : List ValValSem) (t : ValTy)
    (r r' : Except DimError ValValSem)
    (hc : PartialValueDomains.PartialCoherent t
      (denotValTyPartial orc ρ Γ Δ t) (denotValTyPartial orc ρ' Γ' Δ' t))
    (hr : PaperValueDomains.PartialRel
      (PartialValueDomains.PartialRuntimeRelated t
        (denotValTyPartial orc ρ Γ Δ t) (denotValTyPartial orc ρ' Γ' Δ' t)) r r') :
    PaperValueDomains.PartialRel
      (PartialValueDomains.PartialRelated t
        (denotValTyPartial orc ρ Γ Δ t) (denotValTyPartial orc ρ' Γ' Δ' t))
      (checkResult orc ρ Γ Δ t r) (checkResult orc ρ' Γ' Δ' t r') := by
  rw [checkResult_eq_validate, checkResult_eq_validate]
  exact PartialValueDomains.validate_related t _ _ hc _ _
    (PartialValueDomains.partial_extract_results hr)

/-- Reifying a checked result preserves its successful membership. -/
theorem checkRuntime_sound (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy)
    (r : Except DimError ValValSem) :
    PartialValType.ResultContains (denotValTyPartial orc ρ Γ Δ t)
      ((checkRuntime orc ρ Γ Δ t r).bind t.carrierFromVal) := by
  rw [checkRuntime, PartialValueDomains.carrier_result_roundtrip]
  exact checkResult_sound orc ρ Γ Δ t r

/-- The application boundary enforces its output type, including returned
functions, regardless of the annotations used to produce its operands. -/
theorem applyChecked_sound (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (domain output : ValTy)
    (function argument : Except DimError ValValSem) :
    PartialValType.ResultContains (denotValTyPartial orc ρ Γ Δ output)
      ((applyChecked orc ρ Γ Δ domain output function argument).bind output.carrierFromVal) := by
  cases function with
  | error e => exact PartialValType.resultContains_error _ _
  | ok f =>
    cases h : checkResult orc ρ Γ Δ domain argument with
    | error e => simpa [applyChecked, h, Except.bind] using
        (PartialValType.resultContains_error (denotValTyPartial orc ρ Γ Δ output) e)
    | ok a => simpa [applyChecked, h, Except.bind] using
        checkRuntime_sound orc ρ Γ Δ output (f.applyTyped a)

/-- Runtime reification of checked related results preserves their recursive relation. -/
theorem checkRuntime_related (orc : PartialFFSOracleSem) (ρ ρ' : ValEnvSem)
    (Γ Γ' : List ValTy) (Δ Δ' : List ValValSem) (t : ValTy)
    (r r' : Except DimError ValValSem)
    (hc : PartialValueDomains.PartialCoherent t
      (denotValTyPartial orc ρ Γ Δ t) (denotValTyPartial orc ρ' Γ' Δ' t))
    (hr : PaperValueDomains.PartialRel
      (PartialValueDomains.PartialRuntimeRelated t
        (denotValTyPartial orc ρ Γ Δ t) (denotValTyPartial orc ρ' Γ' Δ' t)) r r') :
    PaperValueDomains.PartialRel
      (PartialValueDomains.PartialRuntimeRelated t
        (denotValTyPartial orc ρ Γ Δ t) (denotValTyPartial orc ρ' Γ' Δ' t))
      (checkRuntime orc ρ Γ Δ t r) (checkRuntime orc ρ' Γ' Δ' t r') :=
  PaperValueDomains.PartialRel.map _ _
    (fun a b hab => PartialValueDomains.partial_reify_related t _ _ a b hab)
    (checkResult_related orc ρ ρ' Γ Γ' Δ Δ' t r r' hc hr)

/-- Evaluation followed by the result boundary equals checked value denotation. -/
theorem checkResult_eval_eq_checked (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy) (e : ValExpr) :
    checkResult orc ρ Γ Δ t (denotValB_partial orc ρ Γ Δ e) =
      denotValB_partialCheckedAt orc ρ Γ Δ t e := rfl

end GLang.PartialValueEval
