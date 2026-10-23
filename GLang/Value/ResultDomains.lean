import GLang.Proofs.Adequacy.Foundations.ValueSoundnessSemS

/-! Result domains for finite arrays and dependent functions. Errors are
admitted both at the function level and at each application. -/
namespace GLang.PaperValueDomains

universe u v

abbrev Result (A : Type u) := Except DimError A
abbrev Dimension := Result Nat
abbrev Shape := Result (List Nat)
abbrev Array (n : Nat) := Result (SizedFlatArray n)

/-- Partial dependent sections over successful inputs. Instantiate `A` with the
successful part of the recursively interpreted argument type and `B` with its
successful result fibres. The two error alternatives are intentionally distinct. -/
abbrev Section (A : Type u) (B : A → Type v) :=
  Result ((a : A) → Result (B a))

/-- Strict dependent application; its successful result records the chosen
fibre. There is no need to define a fibre at an error argument. -/
def apply {A : Type u} {B : A → Type v}
    (f : Section A B) (a : Result A) : Result (Sigma B) :=
  match f with
  | .error e => .error e
  | .ok g => match a with
    | .error e => .error e
    | .ok x => match g x with
      | .error e => .error e
      | .ok y => .ok ⟨x, y⟩

@[simp] theorem apply_error_function {A : Type u} {B : A → Type v}
    (a : Result A) : apply (.error .mismatch : Section A B) a = .error .mismatch := rfl

@[simp] theorem apply_error_argument {A : Type u} {B : A → Type v}
    (g : (a : A) → Result (B a)) :
    apply (.ok g) (.error .mismatch) = .error .mismatch := rfl

@[simp] theorem apply_ok {A : Type u} {B : A → Type v}
    (g : (a : A) → Result (B a)) (a : A) :
    apply (.ok g) (.ok a) = (g a).map (fun b => ⟨a, b⟩) := by
  cases h : g a <;> simp [apply, h, Except.map]

/-- The canonical space-result condition is the finite-array length condition. -/
theorem array_membership (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (s : ValSpace) (a : FlatArray) :
    ValCanonicalSoundOfDenotSemS orc ρ Γ Δ (.space s) (.array a) ↔
      a.length = ValSpace.dof (orc ρ Γ Δ) s := Iff.rfl

/-- Restrict an existing canonical function to any chosen successful-input
family. This justifies restriction of its domain; identifying all recursively
restricted higher-order representations is a separate bridge obligation. -/
theorem restrict_function {orc : FFSOracleSem} {ρ : ValEnvSem}
    {Γ : List ValTy} {Δ : List ValValSem} {τ₀ τ₁ : ValTy}
    {T : Type} {f : T → Result ValValSem}
    (hf : ValCanonicalSoundOfDenotSemS orc ρ Γ Δ (.piTy τ₀ τ₁) (.fn T f))
    {A : Type} (encode : A → T) :
    ∃ h : T = (denotValTyS orc ρ Γ Δ τ₀).El,
      ∀ (a : A) (out : ValValSem), f (encode a) = .ok out →
        ValCanonicalSoundOfDenotSemS orc ρ (τ₀ :: Γ)
          (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) (h ▸ encode a) :: Δ) τ₁ out := by
  obtain ⟨h, hf⟩ := hf
  exact ⟨h, fun a out ho => hf (encode a) out ho⟩

end GLang.PaperValueDomains
