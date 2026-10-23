import GLang.Value.Dimensions

/-! Type interpretation and domain membership. Base dimensions may fail
immediately; dependent codomains are interpreted at each argument. -/
namespace GLang

abbrev PartialFFSOracleSem :=
  ValEnvSem → List ValTy → List ValValSem → PartialFFSOracle

/-- A successful type interpretation. Pi codomains are partial families over
the domain's structural carrier; membership below restricts those arguments
to the actual interpreted domain. -/
def PartialValType : ValTy → Type
  | .space _ => Nat
  | .piTy d c => PartialValType d × (d.carrierEl → Except DimError (PartialValType c))

namespace PartialValType

def space (s : ValSpace) (n : Nat) : PartialValType (.space s) := n

def piTy {d c : ValTy} (domain : PartialValType d)
    (fiber : d.carrierEl → Except DimError (PartialValType c)) :
    PartialValType (.piTy d c) := (domain, fiber)

/-- Membership in the non-error part of a successfully interpreted type.
A failed dependent fiber admits only an error result, never a successful
value with an invented dimension. -/
def Contains : {τ : ValTy} → PartialValType τ → τ.carrierEl → Prop
  | .space _, n, a => a.length = n
  | .piTy _ _, (domain, fiber), f =>
      ∀ a, Contains domain a →
        match fiber a, f a with
        | .error _, .error _ => True
        | .error _, .ok _ => False
        | .ok _, .error _ => True
        | .ok target, .ok b => Contains target b

/-- The actual non-error domain as a subset of the raw structural carrier. -/
def Domain {τ : ValTy} (T : PartialValType τ) : Type :=
  {v : τ.carrierEl // T.Contains v}

/-- A failed type interpretation has no successful values. -/
def ResultContains {τ : ValTy} (T : Except DimError (PartialValType τ))
    (v : Except DimError τ.carrierEl) : Prop :=
  match T, v with
  | .error _, .error _ => True
  | .error _, .ok _ => False
  | .ok _, .error _ => True
  | .ok t, .ok a => t.Contains a

@[simp] theorem resultContains_error {τ : ValTy}
    (T : Except DimError (PartialValType τ)) (err : DimError) :
    ResultContains T (.error err) := by
  cases T <;> trivial

@[simp] theorem failed_type_no_success {τ : ValTy} (err : DimError)
    (v : τ.carrierEl) : ¬ ResultContains (.error err) (.ok v) := by
  intro h
  exact h

/-- Finite base domains are exactly arrays of the interpreted length. -/
def spaceDomainEquiv (s : ValSpace) (n : Nat) :
    Domain (τ := .space s) (PartialValType.space s n) ≃ SizedFlatArray n := Equiv.refl _

/-- Application to an admitted argument preserves membership in its partial
fiber, including the case where interpreting that fiber fails. -/
theorem apply_mem {d c : ValTy} {domain : PartialValType d}
    {fiber : d.carrierEl → Except DimError (PartialValType c)}
    {f : (ValTy.piTy d c).carrierEl}
    (hf : (PartialValType.piTy domain fiber).Contains f)
    {a : d.carrierEl} (ha : domain.Contains a) :
    ResultContains (fiber a) (f a) := hf a ha

/-- An admitted section must return the error at an admitted argument whose
codomain fails to denote. There is currently one DimError constructor. -/
theorem apply_failed_fiber {d c : ValTy} {domain : PartialValType d}
    {fiber : d.carrierEl → Except DimError (PartialValType c)}
    {f : (ValTy.piTy d c).carrierEl}
    (hf : (PartialValType.piTy domain fiber).Contains f)
    {a : d.carrierEl} (ha : domain.Contains a) {err : DimError}
    (he : fiber a = .error err) : f a = .error err := by
  have h := apply_mem hf ha
  rw [he] at h
  cases hv : f a with
  | error e => cases e; cases err; rfl
  | ok v => simp [ResultContains, hv] at h

/-- Check the result at a partially interpreted type. At an arrow the raw
argument is passed to the original callback unchanged; only its result is
checked in the fiber selected by that same argument. -/
def check : {τ : ValTy} → PartialValType τ → τ.carrierEl → Except DimError τ.carrierEl
  | .space _, n, a => if a.length = n then .ok a else .error .mismatch
  | .piTy _ _, (_, fiber), f => .ok (fun a =>
      match fiber a with
      | .error e => .error e
      | .ok target =>
          match f a with
          | .error e => .error e
          | .ok b => check target b)

/-- Successful checks have the declared finite size at every admitted
argument, and no successful output can inhabit a failed dependent fiber.
This is membership soundness, not extensionality of arbitrary raw callbacks. -/
theorem check_sound : {τ : ValTy} → (T : PartialValType τ) → (v : τ.carrierEl) →
    ResultContains (.ok T) (check T v)
  | .space s, n, a => by
      simp only [check]
      split
      · assumption
      · trivial
  | .piTy d c, (domain, fiber), f => by
      intro a _ha
      cases hT : fiber a with
      | error e => simp [hT]
      | ok target =>
          cases hf : f a with
          | error e => simp [hT, hf]
          | ok b =>
              have ih := check_sound target b
              simpa only [check, hT, hf] using ih

theorem check_idempotent : {τ : ValTy} → (T : PartialValType τ) → (v : τ.carrierEl) →
    (check T v).bind (check T) = check T v
  | .space s, n, a => by
      simp only [check]
      split <;> simp_all [Except.bind]
  | .piTy d c, (domain, fiber), f => by
      simp only [check, Except.bind]
      apply congrArg Except.ok
      funext a
      cases ht : fiber a with
      | error e => rfl
      | ok target =>
          cases hf : f a with
          | error e => rfl
          | ok b =>
              have ih := check_idempotent target b
              cases hb : check target b <;> simpa only [hb, Except.bind] using ih

@[simp] theorem check_space_ok (s : ValSpace) (n : Nat) (a : FlatArray)
    (ha : a.length = n) : check (space s n) a = .ok a := by
  simp only [check, space, if_pos ha]

@[simp] theorem check_space_error (s : ValSpace) (n : Nat) (a : FlatArray)
    (ha : a.length ≠ n) : check (space s n) a = .error .mismatch := by
  simp only [check, space, if_neg ha]

end PartialValType

/-- Partial interpretation of a value type. Domain failures propagate at once;
codomain interpretation is suspended beneath the binder. The raw argument
used to index a dependent fiber is retained without resizing. -/
noncomputable def denotValTyPartial (orc : PartialFFSOracleSem) :
    (ρ : ValEnvSem) → (Γ : List ValTy) → (Δ : List ValValSem) →
    (τ : ValTy) → Except DimError (PartialValType τ)
  | ρ, Γ, Δ, .space s =>
      match s.dofPartial (orc ρ Γ Δ) with
      | .error e => .error e
      | .ok n => .ok (PartialValType.space s n)
  | ρ, Γ, Δ, .piTy d c =>
      match denotValTyPartial orc ρ Γ Δ d with
      | .error e => .error e
      | .ok domain => .ok (PartialValType.piTy domain (fun a =>
          denotValTyPartial orc ρ (d :: Γ) (d.carrierToVal a :: Δ) c))

@[simp] theorem denotValTyPartial_space_error (orc : PartialFFSOracleSem)
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (s : ValSpace) (err : DimError)
    (h : s.dofPartial (orc ρ Γ Δ) = .error err) :
    denotValTyPartial orc ρ Γ Δ (.space s) = .error err := by
  simp only [denotValTyPartial, h]

@[simp] theorem denotValTyPartial_pi_domain_error (orc : PartialFFSOracleSem)
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (d c : ValTy) (err : DimError)
    (h : denotValTyPartial orc ρ Γ Δ d = .error err) :
    denotValTyPartial orc ρ Γ Δ (.piTy d c) = .error err := by
  simp only [denotValTyPartial, h]

/-- A failed codomain does not eagerly reject a function type: the partial
fiber is retained under the function binder. -/
theorem denotValTyPartial_pi_ok (orc : PartialFFSOracleSem)
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (d c : ValTy) (domain : PartialValType d)
    (h : denotValTyPartial orc ρ Γ Δ d = .ok domain) :
    denotValTyPartial orc ρ Γ Δ (.piTy d c) =
      .ok (PartialValType.piTy domain (fun a =>
        denotValTyPartial orc ρ (d :: Γ) (d.carrierToVal a :: Δ) c)) := by
  simp only [denotValTyPartial, h]

/-- Check a structural-carrier result without totalizing any dimension or
codomain failure. Dependent checks remain suspended in returned functions. -/
noncomputable def checkValTyPartial (orc : PartialFFSOracleSem)
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (τ : ValTy) (v : τ.carrierEl) : Except DimError τ.carrierEl :=
  match denotValTyPartial orc ρ Γ Δ τ with
  | .error e => .error e
  | .ok T => T.check v

/-- The checked result belongs to the partial interpretation of its type. -/
theorem checkValTyPartial_sound (orc : PartialFFSOracleSem)
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (τ : ValTy) (v : τ.carrierEl) :
    PartialValType.ResultContains (denotValTyPartial orc ρ Γ Δ τ)
      (checkValTyPartial orc ρ Γ Δ τ v) := by
  cases h : denotValTyPartial orc ρ Γ Δ τ with
  | error e => simp [checkValTyPartial, h]
  | ok T => simpa only [checkValTyPartial, h] using PartialValType.check_sound T v

end GLang
