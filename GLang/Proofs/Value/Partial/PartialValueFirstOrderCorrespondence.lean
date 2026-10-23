import GLang.Proofs.Value.Partial.PartialValueQuotient
import GLang.Proofs.Value.DenotationChecks

/-! Correspondence for partial dependent types whose argument domains are
arrays. Codomains may themselves be dependent function types. This module
connects the actual partial evaluator, without evaluator-invariance premises;
function-valued argument domains require the separate relational theorem. -/
namespace GLang.PartialValueDomains
open PaperValueDomains PaperValueDomains.ExtensionalQuotient

/-- Curried dependent functions with finite-array arguments. -/
inductive ArrayDomains : ValTy → Type where
  | space (s : ValSpace) : ArrayDomains (.space s)
  | piTy (s : ValSpace) {c : ValTy} : ArrayDomains c → ArrayDomains (.piTy (.space s) c)

noncomputable def arrayDomainRepresentation {τ : ValTy} (h : ArrayDomains τ)
    (T : Except DimError (PartialValType τ)) : Representation τ :=
  match h with
  | .space s => match T with
    | .error _ => Representation.failed _
    | .ok n => Representation.space s n
  | .piTy s hc => match T with
    | .error _ => Representation.failed _
    | .ok (n, fiber) => Representation.piTy (Representation.space s n)
        (fun q => arrayDomainRepresentation hc (fiber q.out.val))

/-- For array arguments, membership already enforces extensionality because
related input representatives are literally equal arrays. Recursive returned
functions and failed dependent fibres are handled without totalization. -/
theorem arrayDomainRepresentation_sound {τ : ValTy} (h : ArrayDomains τ)
    (T : Except DimError (PartialValType τ)) (r : Except DimError τ.carrierEl)
    (hr : PartialValType.ResultContains T r) :
    (arrayDomainRepresentation h T).per.result.rel r r := by
  induction h with
  | space s =>
    cases T with
    | error e =>
      cases r with
      | error e => rfl
      | ok a => exact False.elim hr
    | ok n =>
      cases r with
      | error e => rfl
      | ok a => exact ⟨rfl, hr, hr⟩
  | piTy s hc ih =>
    cases T with
    | error e =>
      cases r with
      | error e => rfl
      | ok f => exact False.elim hr
    | ok T =>
      rcases T with ⟨n, fiber⟩
      cases r with
      | error e => rfl
      | ok f =>
        intro a b hab
        have he : a.val = b.val := hab.1
        let q := (Quotient.mk _ a : (Representation.space s n).per.Domain)
        have hqa : q.out.val = a.val := (Quotient.exact (Quotient.out_eq q)).1
        change (arrayDomainRepresentation hc (fiber q.out.val)).per.result.rel
          (f a.val) (f b.val)
        rw [he, hqa, he]
        exact ih (fiber b.val) (f b.val) (hr b.val b.property.2.1)

/-- The actual checked partial evaluator denotes finite arrays or complete
partial dependent sections, recursively through all curried result types. -/
noncomputable def arrayDomainDenotation {τ : ValTy} (h : ArrayDomains τ)
    (orc : PartialFFSOracleSem) (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (e : ValExpr) :
    Except DimError (arrayDomainRepresentation h (denotValTyPartial orc ρ Γ Δ τ)).Carrier :=
  (arrayDomainRepresentation h (denotValTyPartial orc ρ Γ Δ τ)).resultEquiv
    (Quotient.mk _ ⟨denotValB_partialCheckedAt orc ρ Γ Δ τ e,
      arrayDomainRepresentation_sound h _ _
        (denotValB_partialCheckedAt_sound orc ρ Γ Δ τ e)⟩)

/-- Evaluator errors are preserved exactly by the mathematical denotation. -/
theorem arrayDomainDenotation_error {τ : ValTy} (h : ArrayDomains τ)
    (orc : PartialFFSOracleSem) (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (e : ValExpr) (err : DimError)
    (he : denotValB_partialCheckedAt orc ρ Γ Δ τ e = .error err) :
    arrayDomainDenotation h orc ρ Γ Δ e = .error err := by
  unfold arrayDomainDenotation
  simp only [he, Representation.resultEquiv_error]

end GLang.PartialValueDomains
