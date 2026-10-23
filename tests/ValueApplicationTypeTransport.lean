import GLang.Proofs.Value.Partial.PartialValueTypedApplication
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialApplicationTransport
import GLang.Proofs.Preservation.OperationalTypedContextSoundness

namespace GLang
open PartialValueEval

private noncomputable def scalar : ValValSem := .arrayOf 1 (fun _ => 0)
private noncomputable def constantScalar : ValValSem := .fn FlatArray (fun _ => .ok scalar)
private noncomputable def returnsFunction : ValValSem := .fn FlatArray (fun _ => .ok constantScalar)

-- Different annotations with the same dimension do not require syntax casts.
example (ρ : ValEnvSem) :
    applyBetween PartialDirectOracle.oracle ρ [] [] (.space .real) (.space .real)
      (.space (.tprod .real .real)) (.space (.tprod .real .real))
      (.ok constantScalar) (.ok scalar) = .ok scalar := by
  simp [applyBetween, reshapeBetween, reshapeArray,
    ValSpace.dofPartial, ValSpace.shpOfPartial, ValTy.carrierFromVal,
    ValTy.carrierEl, ValTy.carrierToVal,
    ValValSem.applyTyped, constantScalar, scalar, ValValSem.arrayOf, FlatArray.ofFn,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

-- An actual two-dimensional function returned under a scalar-domain annotation
-- must reject the scalar argument, even if its callback happens to ignore it.
example (ρ : ValEnvSem) :
    ∃ f, applyBetween PartialDirectOracle.oracle ρ [] []
      (.space .real) (.piTy (.space (.dsum .real .real)) (.space .real))
      (.space .real) (.piTy (.space .real) (.space .real))
      (.ok returnsFunction) (.ok scalar) = .ok f ∧
      f.applyTyped (FlatArray.ofFn 1 (fun _ => 0)) = .error .mismatch := by
  simp [applyBetween, reshapeBetween, reshapeArray, denotValTyPartial,
    PartialValType.check, PartialValType.space, ValTy.carrierEl,
    ValSpace.dofPartial, ValSpace.shpOfPartial, ValTy.carrierFromVal, ValTy.carrierToVal,
    ValValSem.applyTyped, returnsFunction, constantScalar, scalar,
    ValValSem.arrayOf, FlatArray.ofFn, Bind.bind, Except.bind, Pure.pure, Except.pure]

-- Equal-dimensional higher-order domains are accepted despite distinct syntax.
example (ρ : ValEnvSem) :
    ∃ f, applyBetween PartialDirectOracle.oracle ρ [] []
      (.space .real) (.piTy (.space (.tprod .real .real)) (.space .real))
      (.space .real) (.piTy (.space .real) (.space .real))
      (.ok returnsFunction) (.ok scalar) = .ok f ∧
      f.applyTyped (FlatArray.ofFn 1 (fun _ => 0)) = .ok scalar := by
  simp [applyBetween, reshapeBetween, reshapeArray, denotValTyPartial,
    PartialValType.check, PartialValType.space, ValTy.carrierEl,
    ValSpace.dofPartial, ValSpace.shpOfPartial, ValTy.carrierFromVal, ValTy.carrierToVal,
    ValValSem.applyTyped, returnsFunction, constantScalar, scalar,
    ValValSem.arrayOf, FlatArray.ofFn, Bind.bind, Except.bind, Pure.pure, Except.pure]

end GLang

open Lean Elab Command
elab "check_application_transport_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``GLang.PartialValueDomains.partial_applyBetween_family,
      ``GLang.PartialValueDomains.partial_applyBetween_typed_family,
      ``GLang.PartialAdequacy.applyBetween_agree,
      ``GLang.Operational.TypedContext.lookup_sound] do
    for ax in ← Lean.collectAxioms name do
      unless permitted.contains ax do
        throwError "Unexpected application-transport axiom in {name}: {ax}"
  logInfo "Independent application typing preserves the full recursive relation without project axioms."
check_application_transport_axioms
