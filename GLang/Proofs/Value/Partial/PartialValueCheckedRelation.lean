import GLang.Proofs.Value.Partial.PartialValueRecursiveDomain
import GLang.Proofs.Value.DenotationChecks

/-! Checking preserves extensional partial results at coherent types. This is
a relational checker theorem, not an assumption about evaluator invariance. -/
namespace GLang.PartialValueDomains
open PaperValueDomains PaperValueDomains.ExtensionalQuotient

/-- Validate a partial structural-carrier result. A failed type admits only
its error, including when its unchecked input happens to be successful. -/
def validate {τ : ValTy} (T : Except DimError (PartialValType τ))
    (r : Except DimError τ.carrierEl) : Except DimError τ.carrierEl :=
  match T with
  | .error e => .error e
  | .ok t => r.bind t.check

@[simp] theorem validate_error {τ : ValTy} (T : Except DimError (PartialValType τ))
    (err : DimError) : validate T (.error err) = .error err := by
  cases T with
  | error e => cases e; cases err; rfl
  | ok t => rfl

private theorem validate_function {d c : ValTy} (D : PartialValType d)
    (F : d.carrierEl → Except DimError (PartialValType c))
    (f : (.piTy d c : ValTy).carrierEl) :
    validate (τ := .piTy d c) (.ok (D,F)) (.ok f) =
      .ok (fun a => validate (F a) (f a)) := by
  apply congrArg Except.ok
  funext a
  cases F a <;> cases f a <;> rfl

/-- Checking one side preserves the represented result, including higher-order
functions, type errors, and errors in argument-dependent result fibres. -/
theorem validate_related_right (τ : ValTy)
    (T U : Except DimError (PartialValType τ)) (hc : PartialCoherent τ T U)
    (r s : Except DimError τ.carrierEl)
    (h : PartialRel (PartialRelated τ T U) r s) :
    PartialRel (PartialRelated τ T U) r (validate U s) := by
  cases r with
  | error e =>
    cases s with
    | error e' => simpa only [validate_error] using h
    | ok b => exact False.elim h
  | ok a =>
    cases s with
    | error e => exact False.elim h
    | ok b =>
      cases τ with
      | space v =>
        cases T <;> cases U <;> try exact False.elim h
        rename_i n m
        have hb := h.2.2
        simpa only [validate, Except.bind, PartialValType.check, if_pos hb] using h
      | piTy d c =>
        cases T <;> cases U <;> try exact False.elim h
        rename_i T U
        rcases T with ⟨D,F⟩
        rcases U with ⟨E,G⟩
        rw [validate_function E G b]
        intro x y hxy
        exact validate_related_right c (F x) (G y) (hc.2 x y hxy)
          (a x) (b y) (h x y hxy)
termination_by sizeOf τ

/-- The two-sided relational checker theorem. -/
theorem validate_related (τ : ValTy)
    (T U : Except DimError (PartialValType τ)) (hc : PartialCoherent τ T U)
    (r s : Except DimError τ.carrierEl)
    (h : PartialRel (PartialRelated τ T U) r s) :
    PartialRel (PartialRelated τ T U) (validate T r) (validate U s) := by
  have hr := validate_related_right τ T U hc r s h
  have hs := PartialRel.symm (fun a b hab => partialRelated_symm τ T U a b hab) hr
  exact PartialRel.symm (fun a b hab => partialRelated_symm τ U T a b hab)
    (validate_related_right τ U T (partialCoherent_symm τ T U hc) _ _ hs)

/-- The actual checked evaluator performs precisely this validation of the
raw evaluator's ordinary structural-carrier decoding. -/
theorem checked_eq_validate (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy) (e : ValExpr) :
    denotValB_partialCheckedAt orc ρ Γ Δ τ e =
      validate (denotValTyPartial orc ρ Γ Δ τ)
        ((denotValB_partial orc ρ Γ Δ e).bind τ.carrierFromVal) := by
  unfold denotValB_partialCheckedAt
  cases denotValB_partial orc ρ Γ Δ e with
  | error err => simp only [Except.bind, validate_error]
  | ok v =>
    simp only [Except.bind]
    cases he : τ.carrierFromVal v with
    | error err => simp only [validate_error]
    | ok a =>
      unfold checkValTyPartial
      cases denotValTyPartial orc ρ Γ Δ τ <;> rfl

/-- A related raw decoded computation and its actual checked evaluation
represent the same mathematical value. -/
theorem checked_class_eq (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy) (e : ValExpr)
    (hc : PartialCoherent τ (denotValTyPartial orc ρ Γ Δ τ) (denotValTyPartial orc ρ Γ Δ τ))
    (hr : PartialRel (PartialRelated τ (denotValTyPartial orc ρ Γ Δ τ)
      (denotValTyPartial orc ρ Γ Δ τ))
      ((denotValB_partial orc ρ Γ Δ e).bind τ.carrierFromVal)
      ((denotValB_partial orc ρ Γ Δ e).bind τ.carrierFromVal)) :
    (Quotient.mk _ ⟨(denotValB_partial orc ρ Γ Δ e).bind τ.carrierFromVal, hr⟩ :
      (partialPER τ (denotValTyPartial orc ρ Γ Δ τ) hc).result.Domain) =
    Quotient.mk _ ⟨denotValB_partialCheckedAt orc ρ Γ Δ τ e, by
      rw [checked_eq_validate]
      exact validate_related τ _ _ hc _ _ hr⟩ := by
  apply Quotient.sound
  change PartialRel (PartialRelated τ (denotValTyPartial orc ρ Γ Δ τ)
    (denotValTyPartial orc ρ Γ Δ τ))
    ((denotValB_partial orc ρ Γ Δ e).bind τ.carrierFromVal)
    (denotValB_partialCheckedAt orc ρ Γ Δ τ e)
  rw [checked_eq_validate]
  exact validate_related_right τ _ _ hc _ _ hr

end GLang.PartialValueDomains
