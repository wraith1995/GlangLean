import GLang.Proofs.Value.Partial.PartialValueReshapeRuntime

/-! Native binary application and compatibility helpers for explicit conversions. -/
namespace GLang.PartialValueEval

/-- Check the function's domain and call it. The result has its dependent
codomain; application takes no independently selected output type. -/
noncomputable def applyDomainChecked (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (domain : ValTy)
    (function argument : Except DimError ValValSem) : Except DimError ValValSem :=
  match function with
  | .error e => .error e
  | .ok f =>
      (checkResult orc ρ Γ Δ domain argument).bind (fun a => f.applyTyped a)

/-- Apply a function at its declared domain, then transport its dependent result
to the independently realized output type. The compiler expresses these conversions with explicit reshape nodes. -/
noncomputable def applyBetween (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem)
    (domain codomain argumentType output : ValTy)
    (function argument : Except DimError ValValSem) : Except DimError ValValSem :=
  match function, argument with
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok f, .ok v =>
    match reshapeBetween orc ρ Γ Δ Γ Δ v domain argumentType with
    | .error e => .error e
    | .ok arg =>
      match domain.carrierFromVal arg with
      | .error e => .error e
      | .ok a =>
        match f.applyTyped a with
        | .error e => .error e
        | .ok result =>
          reshapeBetween orc ρ Γ Δ
            (domain :: Γ) (domain.carrierToVal a :: Δ) result output codomain

end GLang.PartialValueEval
