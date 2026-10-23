import GLang.Proofs.Value.Presentation.PaperValueOperationalBoundary
import GLang.Proofs.Value.Presentation.PaperValueEnvironmentExtension
import GLang.Metatheory
import Lean

open GLang GLang.PaperValueOperationalBoundary GLang.PaperValueResults

example : ¬ (∀ {Δ Γ Ψ Γv σ ρ}, RawConsistent directOracle Δ Γ Ψ Γv σ ρ →
    PaperValueResults.EnvWF Γv ρ) :=
  consistency_not_value_env

example {Δ Γ Ψ Γv σ ρ}
    (h : Adequacy.PartialDirect.Consistent Δ Γ Ψ Γv σ ρ) :
    RuntimeValue.PartialEnvWF PartialDirectOracle.oracle Γv ρ :=
  h.valueEnv

example {Δ Γ Ψ Γv σ ρ} (h : Adequacy.Direct.Consistent Δ Γ Ψ Γv σ ρ) :
    RawConsistent directOracle Δ Γ Ψ Γv σ ρ := h.raw

example (ρ : ValEnvSem) : Adequacy.Direct.Consistent ∅ ∅ ∅ ∅ ⟨∅⟩ ρ :=
  Adequacy.Direct.Consistent.empty ρ

-- Guard both the supporting raw-consistency counterexample (including valid
-- value contexts) and the positive, full-original-typing extension theorem.
open Lean Elab Command
elab "check_operational_boundary_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``partial_arguments_related, ``malicious_agrees, ``malicious_not_related,
      ``valid_consistency_not_value_env, ``consistency_not_value_env,
      ``EnvWF.extend, ``EnvWF.extend_of_eval,
      ``Adequacy.Direct.Consistent.contextHistory, ``Adequacy.Direct.Consistent.empty] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected operational-boundary assumption {n}: {ax}"
  logInfo "Operational consistency counterexample and typed environment extension: no new axioms."
check_operational_boundary_axioms
