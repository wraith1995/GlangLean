import GLang.Proofs.Value.Partial.PartialValueRuntimeBoundary

namespace GLang.PartialValueEval

/-- Partial array reinterpretation in distinct source and target worlds. -/
noncomputable def reshapeArray (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γt : List ValTy) (Δt : List ValValSem)
    (Γs : List ValTy) (Δs : List ValValSem)
    (a : FlatArray) (st ss : ValSpace) : Except DimError ValValSem :=
  match ss.dofPartial (orc ρ Γs Δs), st.dofPartial (orc ρ Γt Δt) with
  | .ok ns, .ok nt =>
      if a.length = ns ∧ ns = nt then .ok (.array a) else .error .mismatch
  | .error e, _ => .error e
  | _, .error e => .error e

/-- Higher-order reshape retains partial dimensions beneath each binder and
uses the reshaped source argument for the source-dependent codomain. -/
noncomputable def reshapeBetween (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γt : List ValTy) (Δt : List ValValSem)
    (Γs : List ValTy) (Δs : List ValValSem) :
    ValValSem → ValTy → ValTy → Except DimError ValValSem
  | .array a, .space st, .space ss => reshapeArray orc ρ Γt Δt Γs Δs a st ss
  | _, .space _, _ => .error .mismatch
  | v, .piTy dt ct, .piTy ds cs =>
      match denotValTyPartial orc ρ Γt Δt dt, denotValTyPartial orc ρ Γs Δs ds with
      | .error e, _ => .error e
      | _, .error e => .error e
      | .ok target, .ok _ =>
        .ok (.fn dt.carrierEl (fun a =>
          match target.check a with
          | .error e => .error e
          | .ok checked =>
            let argT := dt.carrierToVal checked
            match reshapeBetween orc ρ Γs Δs Γt Δt argT ds dt with
            | .error e => .error e
            | .ok argS =>
              match ds.carrierFromVal argS with
              | .error e => .error e
              | .ok source =>
                match v.applyTyped source with
                | .error e => .error e
                | .ok result =>
                    reshapeBetween orc ρ (dt :: Γt) (argT :: Δt)
                      (ds :: Γs) (argS :: Δs) result ct cs))
  | _, .piTy _ _, .space _ => .error .mismatch
termination_by _v t s => ValTy.kindSize t + ValTy.kindSize s
decreasing_by all_goals (simp only [ValTy.kindSize_piTy]; omega)

/-- Arrays retain the declared dimension checks. Function conversion uses the
inferred source type, so independently realized domains are converted before
calling the function. -/
noncomputable def reshapeInferred (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (v : ValValSem)
    (target source inferred : ValTy) : Except DimError ValValSem :=
  match source with
  | .space _ => reshapeBetween orc ρ Γ Δ Γ Δ v target source
  | .piTy _ _ =>
    match inferred with
    | .space _ => .error .mismatch
    | .piTy _ _ => reshapeBetween orc ρ Γ Δ Γ Δ v target inferred

@[simp] theorem reshapeInferred_self (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (v : ValValSem) (target source : ValTy) :
    reshapeInferred orc ρ Γ Δ v target source source =
      reshapeBetween orc ρ Γ Δ Γ Δ v target source := by
  cases source <;> rfl

end GLang.PartialValueEval
