import GLang.Proofs.Value.Partial.PartialValueCorrespondence
import GLang.Proofs.Value.Partial.PartialValueFirstOrderCorrespondence
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectOracle
import GLang.Proofs.Value.Partial.PartialValueRuntimeRelation

namespace GLang.PartialValueCorrespondenceTests
open PartialValueDomains PaperValueDomains.ExtensionalQuotient

-- Failed dimensions denote an empty successful domain, not arrays of length 0.
example (s : ValSpace) :
    (arrayDomainRepresentation (.space s) (.error .mismatch)).Carrier = Empty := rfl

-- A successfully interpreted zero-dimensional space still has a genuine array.
example (s : ValSpace) :
    (arrayDomainRepresentation (.space s) (.ok (PartialValType.space s 0))).Carrier = SizedFlatArray 0 := rfl

-- Arbitrarily nested higher-order mathematical domains can be built without
-- assuming that arbitrary raw callbacks are extensional.
noncomputable def scalar := Representation.space .real 1
noncomputable def scalarArrow := Representation.piTy scalar (fun _ => scalar)
noncomputable def scalarFunctional := Representation.piTy scalarArrow (fun _ => scalar)

example : scalarFunctional.Carrier = ((SizedFlatArray 1 → Except DimError (SizedFlatArray 1)) →
    Except DimError (SizedFlatArray 1)) := rfl

-- There is no fabricated successful value in a failed function fibre.
example (τ : ValTy) (r : (Representation.failed τ).per.result.Support) :
    r.val = .error .mismatch := PartialValueDomains.PER.empty_result_error _ r

noncomputable example (s t : ValSpace) (ρ : ValEnvSem) (e : ValExpr) :=
  arrayDomainDenotation (.piTy s (.space t)) PartialDirectOracle.oracle ρ [] [] e

def realArrow : ValTy := .piTy (.space .real) (.space .real)
def higherOrderId : ValExpr := .vlam realArrow realArrow (.bvar 0)

def realArrow_valid (ε : ValCtx) : ValTValid ε realArrow (.arrow .base .base) := by
  apply ValTValid.piTy ∅ (.space .real)
  intro x hx
  exact .space .real

def higherOrderId_typed : ValHasType ∅ higherOrderId (.piTy realArrow realArrow) := by
  apply ValHasType.vlam ∅
  · apply ValTValid.piTy ∅ (realArrow_valid ∅)
    intro x hx
    exact realArrow_valid _
  · intro x hx
    simpa only [realArrow,ValExpr.openVar,ValExpr.openRec,ValTy.openVar,ValTy.openRec,
      ValSpace.openRec,↓reduceIte] using
      (ValHasType.var (ε := Finmap.insert x realArrow ∅) (x := x) (τ := realArrow)
        (by simp))

-- Concrete closed second-order identity has a recursive mathematical denotation.
noncomputable def higherOrderIdentityDenotation (ρ : ValEnvSem) :=
  partialValueDenotation ρ (PartialEnvWF.empty _ _) higherOrderId_typed

-- Full original typing, including a FUNCTION input: no ArrayDomains premise,
-- unary-only callback premise, or assumed evaluator invariance is required.
noncomputable example (ε : ValCtx) (ρ : ValEnvSem) (d c out : ValTy) (e : ValExpr)
    (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (he : ValHasType ε e (.piTy (.piTy d c) out)) :=
  partialValueDenotation ρ hρ he

example (ε : ValCtx) (ρ : ValEnvSem) (τ : ValTy) (e : ValExpr)
    (hρ : PartialEnvWF PartialDirectOracle.oracle ε ρ) (he : ValHasType ε e τ)
    (herr : denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ = .error .mismatch) :
    partialValueDenotation ρ hρ he = .error .mismatch :=
  partialValueDenotation_type_error ρ hρ he .mismatch herr

end GLang.PartialValueCorrespondenceTests

open Lean Elab Command
elab "check_partial_correspondence_axioms" : command => do
  let pure := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``GLang.PartialValueDomains.PER.dependentFunctionEquiv,
      ``GLang.PartialValueDomains.partialFamily_laws,
      ``GLang.PartialValueDomains.partialRecursiveDomain,
      ``GLang.PartialValueDomains.validate_related_right,
      ``GLang.PartialValueDomains.validate_related,
      ``GLang.PartialValueDomains.partialRuntime_family_transport,
      ``GLang.PartialValueDomains.partialRuntime_family_trans,
      ``GLang.PartialValueDomains.partialRuntime_normalize_right,
      ``GLang.PartialValueDomains.partialRuntimeRelated_heq,
      ``GLang.PartialValueDomains.partial_reshape_family,
      ``GLang.PartialValueDomains.carrier_roundtrip,
      ``GLang.PartialValueDomains.partial_reify_related,
      ``GLang.PartialValueDomains.partial_extract_related,
      ``GLang.PartialValueDomains.partial_extract_results,
      ``GLang.PartialValueDomains.carrier_apply,
      ``GLang.PartialValueDomains.decodeDomain_related_left,
      ``GLang.PartialValueDomains.PER.empty_result_error,
      ``GLang.PartialValueDomains.arrayDomainRepresentation_sound] do
    for ax in ← Lean.collectAxioms n do
      unless pure.contains ax do
        throwError "Unexpected partial correspondence axiom {n}: {ax}"
  let runtime := pure.push ``GLang.Matrix.exists_gsvd
  for n in [``GLang.PartialValueDomains.partial_originalExpr_related_family,
      ``GLang.PartialValueDomains.partial_originalType_coherent_family,
      ``GLang.PartialValueDomains.partialValueDomainSoundness,
      ``GLang.PartialValueDomains.partialValueCheckedDomainSoundness,
      ``GLang.PartialValueDomains.partialValueDenotation,
      ``GLang.PartialValueDomains.partialValueDenotation_raw_eq,
      ``GLang.PartialValueDomains.partialValueDenotation_error,
      ``GLang.PartialValueDomains.partialValueDenotation_type_error,
      ``GLang.PartialValueDomains.partialValueClass_family_eq,
      ``GLang.PartialValueDomains.arrayDomainDenotation,
      ``GLang.PartialValueDomains.arrayDomainDenotation_error,
      ``GLang.PartialValueDomains.checked_eq_validate,
      ``GLang.PartialValueDomains.checked_class_eq] do
    for ax in ← Lean.collectAxioms n do
      unless runtime.contains ax do
        throwError "Unexpected partial runtime correspondence axiom {n}: {ax}"
  logInfo "Full original-typed partial higher-order correspondence passes axiom audit."
check_partial_correspondence_axioms
