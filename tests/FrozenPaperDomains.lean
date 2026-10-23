import GLang.Paper
import GLang.Artifact
import Lean

namespace GLang.FrozenPaperDomainTests
open PartialValueDomains PaperValueDomainResults

-- Errors are distinct from successfully interpreted zero-dimensional arrays.
example (s : ValSpace) (err : DimError) :
    ValueDomain (.space s) (.error err) rfl = Except DimError Empty := rfl
example (s : ValSpace) :
    ValueDomain (.space s) (.ok (PartialValType.space s 0)) rfl =
      Except DimError (SizedFlatArray 0) := rfl

private abbrev scalar : ValTy := .space .real
private abbrev arrowType : PartialValType (.piTy scalar scalar) :=
  (PartialValType.space .real 1, fun _ => .ok (PartialValType.space .real 1))
private theorem arrowCoherent :
    PartialCoherent (.piTy scalar scalar) (.ok arrowType) (.ok arrowType) :=
  ⟨rfl, fun _ _ _ => rfl⟩

-- The product ranges over successful arguments; every result includes error.
example : ValueDomain (.piTy scalar scalar) (.ok arrowType) arrowCoherent =
    Except DimError (SizedFlatArray 1 → Except DimError (SizedFlatArray 1)) := rfl

-- A genuinely higher-order domain: arbitrary mathematical function arguments.
private abbrev functionalType : PartialValType (.piTy (.piTy scalar scalar) scalar) :=
  (arrowType, fun _ => .ok (PartialValType.space .real 1))
private theorem functionalCoherent : PartialCoherent (.piTy (.piTy scalar scalar) scalar)
    (.ok functionalType) (.ok functionalType) := ⟨arrowCoherent, fun _ _ _ => rfl⟩
example : ValueDomain (.piTy (.piTy scalar scalar) scalar)
    (.ok functionalType) functionalCoherent =
    Except DimError ((SizedFlatArray 1 → Except DimError (SizedFlatArray 1)) →
      Except DimError (SizedFlatArray 1)) := rfl

-- The domain equivalence is onto all mathematical functions, including those
-- that have no value-language program; it is not just a soundness injection.
example (f : (SizedFlatArray 1 → Except DimError (SizedFlatArray 1)) →
    Except DimError (SizedFlatArray 1)) :
    ∃ v : ValValSem,
      PartialRuntimeRelated (.piTy (.piTy scalar scalar) scalar)
        (.ok functionalType) (.ok functionalType) v v := by
  obtain ⟨v, hv, _⟩ := representable _ (.ok functionalType) functionalCoherent f
  exact ⟨v, hv⟩

-- Failed fibers remain error-only; they do not reject the outer function.
private abbrev failedFiber : PartialValType (.piTy scalar scalar) :=
  (PartialValType.space .real 1, fun _ => .error .mismatch)
example : ValueDomain (.piTy scalar scalar) (.ok failedFiber)
    (show PartialCoherent _ _ _ from ⟨rfl, fun _ _ _ => rfl⟩) =
    Except DimError (SizedFlatArray 1 → Except DimError Empty) := rfl
example (f : SizedFlatArray 1 → Except DimError Empty) (a : SizedFlatArray 1) :
    f a = .error .mismatch := by
  cases h : f a with
  | error e => cases e; rfl
  | ok impossible => exact impossible.elim

example (q : PartialFFSOracleSem) (ρ : ValEnvSem) (d c : ValTy)
    (h : denotValTyPartial q ρ [] [] d = .error .mismatch) :
    denotValTyPartial q ρ [] [] (.piTy d c) = .error .mismatch :=
  denotValTyPartial_pi_domain_error q ρ [] [] d c .mismatch h

example (ε : ValCtx) (ρ : ValEnvSem)
    (h : ∀ x τ, ε.lookup x = some τ →
      (∃ k, Nonempty (RuntimeValue.ValTValid ε τ k)) ∧ Member ρ τ (ρ x)) :
    RuntimeValue.PartialEnvWF PartialDirectOracle.oracle ε ρ :=
  (environment_iff ε ρ).2 h
example (ρ : ValEnvSem) : RuntimeValue.PartialEnvWF PartialDirectOracle.oracle ∅ ρ :=
  RuntimeValue.PartialEnvWF.empty _ ρ
example (ρ : ValEnvSem) (s : ValSpace) (a : FlatArray)
    (h : s.dofPartial (PartialDirectOracle.oracle ρ [] []) = .error .mismatch) :
    ¬ Member ρ (.space s) (.array a) := by
  rw [member_space_iff, h]
  simp

-- Decoding alone is too weak: a malformed successful function result decodes
-- to an error, but must not be admitted as a legitimate partial callback.
private def malformed : ValValSem :=
  .fn FlatArray (fun _ => .ok (.fn Unit (fun _ => .error .mismatch)))
example : (ValTy.piTy scalar scalar).carrierFromVal malformed =
    .ok (fun _ => .error .mismatch) := by
  simp [malformed, scalar, ValTy.carrierFromVal, ValTy.carrierEl]
example : PartialRelated (.piTy scalar scalar) (.ok arrowType) (.ok arrowType)
    (fun _ => .error .mismatch) (fun _ => .error .mismatch) := fun _ _ _ => rfl
example : ¬ PartialRuntimeRelated (.piTy scalar scalar)
    (.ok arrowType) (.ok arrowType) malformed malformed := by
  rintro ⟨hA, hB, h⟩
  change ∀ a b : FlatArray, a = b ∧ a.length = 1 ∧ b.length = 1 → False at h
  have bad := h (FlatArray.ofFn 1 (fun _ => 0)) (FlatArray.ofFn 1 (fun _ => 0))
    (by simp [FlatArray.ofFn])
  exact bad

-- Current semantic consistency supplies this membership assumption directly.
example (hc : Adequacy.PartialDirect.Consistent Δ ε Ψ Γv σ ρ) :
    RuntimeValue.PartialEnvWF PartialDirectOracle.oracle Γv ρ := hc.valueEnv

-- Agreement entails success on every agreeing argument, in the actual
-- dependent fiber. The raw argument is retained in the value environment.
example (q : PartialFFSOracleSem) (σ : DEnv) (ρ : ValEnvSem)
    (Ds : List DVal) (Γ : List ValTy) (Δ : List ValValSem)
    (d c : Ty) (dv cv : ValTy) (B : BasisDenot) (f : DVal) (g : ValValSem)
    (hg : PartialAdequacy.Agree q σ ρ Ds Γ Δ (.piTy d c) (.piTy dv cv) B f g)
    (a : (denotTyAux σ Ds d).El) (w : ValValSem)
    (ha : PartialAdequacy.Agree q σ ρ Ds Γ Δ d dv B.domainBasis
      ((denotTyAux σ Ds d).embed a) w) :
    ∃ arg z, dv.carrierFromVal w = .ok arg ∧ g.applyTyped arg = .ok z ∧
      PartialAdequacy.Agree q σ ρ ((denotTyAux σ Ds d).embed a :: Ds)
        (dv :: Γ) (w :: Δ) c cv (B.applyEl a) (f.applyEl a) z := by
  obtain ⟨arg, hdecode, _⟩ := ha.decode
  simp only [PartialAdequacy.Agree] at hg
  obtain ⟨_, _, callback, rfl, hf⟩ := hg
  obtain ⟨z, hz, hzagree⟩ := hf a w arg hdecode ha
  exact ⟨arg, z, hdecode, by simpa only [ValValSem.applyTyped_fn] using hz, hzagree⟩

-- Shape agreement and basis/frame validity are distinct conjuncts, as printed.
example : PaperAdequacyResults.TypeAgreement σ ρ T Tv B ↔
    PartialAdequacy.DimsAt PartialDirectOracle.oracle σ ρ [] [] [] T Tv B ∧
      Adequacy.Direct.BasisAt σ [] T B := Iff.rfl
example (h : PartialAdequacy.DimsAt q σ ρ Ds Γ Δ (.space s) (.space sv) B) :
    sv.shpOfPartial (q ρ Γ Δ) = .ok (srcShp σ Ds s) := by
  simpa only [PartialAdequacy.DimsAt] using h

open Lean Elab Command in
elab "check_frozen_domain_owners" : command => do
  for n in #[``PaperValueDomainResults.environment_iff,
      ``PaperValueDomainResults.type_coherent, ``PaperValueDomainResults.representable,
      ``PaperValueDomainResults.environment_member,
      ``RuntimeValue.partialValueDenotation_raw_eq,
      ``PartialAdequacy.Agree.openRec_bind_src,
      ``PartialAdequacy.DimsAt.valueOpenPush,
      ``PartialAdequacy.ResultAgree.valueOpenPush] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected recursive-domain axiom in {n}: {ax}"
  logInfo "Frozen recursive domains, live environment owners and raw/checked bridge: foundations only."
check_frozen_domain_owners

end GLang.FrozenPaperDomainTests
