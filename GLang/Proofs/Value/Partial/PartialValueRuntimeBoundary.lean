import GLang.Value.TypeInterpretation

/-! Runtime checks used recursively by the value evaluator. -/
namespace GLang.PartialValueEval

/-- Decode and recursively check a result against its declared output type. -/
noncomputable def checkResult (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy)
    (r : Except DimError ValValSem) : Except DimError t.carrierEl :=
  match r with
  | .error e => .error e
  | .ok v =>
    match t.carrierFromVal v with
    | .error e => .error e
    | .ok a => checkValTyPartial orc ρ Γ Δ t a

/-- Runtime-value form of the same check, suitable for recursive evaluation. -/
noncomputable def checkRuntime (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy)
    (r : Except DimError ValValSem) : Except DimError ValValSem :=
  (checkResult orc ρ Γ Δ t r).map t.carrierToVal

/-- Application checks the supplied argument in the function's domain and the
returned value in the independently supplied result type. Neither check
requires equality of the argument's annotation with the function's domain. -/
noncomputable def applyChecked (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (domain output : ValTy)
    (function argument : Except DimError ValValSem) : Except DimError ValValSem :=
  match function with
  | .error e => .error e
  | .ok f =>
    match checkResult orc ρ Γ Δ domain argument with
    | .error e => .error e
    | .ok a => checkRuntime orc ρ Γ Δ output (f.applyTyped a)

end GLang.PartialValueEval
