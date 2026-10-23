import GLang.Value.ResultDomains
import GLang.Public.PaperValueResults
import GLang.Proofs.Value.Presentation.PaperValueEnvironment

namespace GLang.PaperValueDomains

/-- Hereditary admissibility of a raw typed value. Function outputs are checked
only at recursively admissible inputs, and errors remain admissible results. -/
def Admissible (orc : FFSOracleSem) :
    (ρ : ValEnvSem) → (Γ : List ValTy) → (Δ : List ValValSem) →
    (τ : ValTy) → (denotValTyS orc ρ Γ Δ τ).El → Prop
  | ρ, Γ, Δ, .space s, a => a.length = ValSpace.dof (orc ρ Γ Δ) s
  | ρ, Γ, Δ, .piTy τ₀ τ₁, f =>
      ∀ a, Admissible orc ρ Γ Δ τ₀ a →
        ∀ out, f a = .ok out →
          Admissible orc ρ (τ₀ :: Γ)
            (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) a :: Δ) τ₁ out

/-- Successful recursively admissible inputs, retaining their representative. -/
def Represented (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy) :=
  {a : (denotValTyS orc ρ Γ Δ τ).El // Admissible orc ρ Γ Δ τ a}

/-- Runtime values represent the recursive domain when they produce represented
outputs on admissible inputs. The dependent world is the evaluator's exact one. -/
def Represents (orc : FFSOracleSem) :
    ValEnvSem → List ValTy → List ValValSem → ValTy → ValValSem → Prop
  | ρ, Γ, Δ, .space s, .array a => a.length = ValSpace.dof (orc ρ Γ Δ) s
  | _, _, _, .space _, .fn _ _ => False
  | _, _, _, .piTy _ _, .array _ => False
  | ρ, Γ, Δ, .piTy τ₀ τ₁, .fn T f =>
      ∃ h : T = (denotValTyS orc ρ Γ Δ τ₀).El,
        ∀ a, Admissible orc ρ Γ Δ τ₀ (h ▸ a) →
          ∀ out, f a = .ok out →
            Represents orc ρ (τ₀ :: Γ)
              (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) (h ▸ a) :: Δ) τ₁ out

/-- Canonical soundness implies recursive representation. -/
theorem canonical_represents (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy) (v : ValValSem)
    (h : ValCanonicalSoundOfDenotSemS orc ρ Γ Δ τ v) :
    Represents orc ρ Γ Δ τ v := by
  cases τ with
  | space s => cases v <;> exact h
  | piTy τ₀ τ₁ =>
    cases v with
    | array a => exact h.elim
    | fn T f =>
      obtain ⟨heq, hf⟩ := h
      exact ⟨heq, fun a _ out ho => canonical_represents orc ρ _ _ τ₁ _ (hf a out ho)⟩

termination_by sizeOf τ

/-- Observe an admissible raw function only on successful represented inputs.
The resulting section has precisely the reification-indexed dependent fibres. -/
def observe (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ₀ τ₁ : ValTy)
    (f : Represented orc ρ Γ Δ (.piTy τ₀ τ₁)) :
    (a : Represented orc ρ Γ Δ τ₀) →
      Result (Represented orc ρ (τ₀ :: Γ)
        (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) a.val :: Δ) τ₁) :=
  fun a => match h : f.val a.val with
    | .error e => .error e
    | .ok out => .ok ⟨out, f.property a.val a.property out h⟩

/-- Extraction of a represented runtime value succeeds and preserves recursive
admissibility. In particular, higher-order extraction keeps the exact dependent
fibre selected by ordinary reification of its raw argument. -/
theorem represents_extract (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy) (v : ValValSem)
    (h : Represents orc ρ Γ Δ τ v) :
    ∃ a, ValValSem.toEl (denotValTyS orc ρ Γ Δ τ) v = .ok a ∧
      Admissible orc ρ Γ Δ τ a := by
  classical
  cases τ with
  | space s =>
    cases v with
    | array a => exact ⟨a, rfl, h⟩
    | fn T f => exact h.elim
  | piTy τ₀ τ₁ =>
    cases v with
    | array a => exact h.elim
    | fn T f =>
      obtain ⟨heq, hf⟩ := h
      subst T
      simp only [denotValTyS, ValValSem.toEl, dite_true]
      refine ⟨(fun y => match f y with
        | .error e => .error e
        | .ok v => ValValSem.toEl
            (denotValTyS orc ρ (τ₀ :: Γ)
              (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) y :: Δ) τ₁) v), rfl, ?_⟩
      intro a ha out ho
      cases hfa : f a with
      | error err => simp [hfa] at ho
      | ok raw =>
        obtain ⟨b, hb, hab⟩ := represents_extract orc ρ _ _ τ₁ _ (hf a ha raw hfa)
        simp only [hfa, hb] at ho
        cases ho
        exact hab

termination_by sizeOf τ

/-- Reification of an admissible typed value satisfies the runtime relation.
This is a semantic bridge, not a round-trip equality of raw representatives. -/
theorem admissible_reifies (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy)
    (a : (denotValTyS orc ρ Γ Δ τ).El)
    (ha : Admissible orc ρ Γ Δ τ a) :
    Represents orc ρ Γ Δ τ (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ) a) := by
  cases τ with
  | space s => exact FlatArray.length_resize _ _
  | piTy τ₀ τ₁ =>
    refine ⟨rfl, ?_⟩
    intro x hx out ho
    change (a x).map _ = .ok out at ho
    cases hax : a x with
    | error err => simp [hax, Except.map] at ho
    | ok raw =>
      simp only [hax, Except.map, Except.ok.injEq] at ho
      subst out
      exact admissible_reifies orc ρ _ _ τ₁ raw (ha x hx raw hax)
termination_by sizeOf τ

def representedSpaceEquiv (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (s : ValSpace) :
    Represented orc ρ Γ Δ (.space s) ≃
      SizedFlatArray (ValSpace.dof (orc ρ Γ Δ) s) := Equiv.refl _

/-- Error-preserving correspondence to a represented partial result. Success
uses typed extraction, and both error alternatives must be the same error. -/
def ResultRepresents (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy) :
    Result ValValSem → Result (Represented orc ρ Γ Δ τ) → Prop
  | .error e, .error e' => e = e'
  | .ok v, .ok a => ValValSem.toEl (denotValTyS orc ρ Γ Δ τ) v = .ok a.val
  | _, _ => False

/-- Every recursively represented partial runtime result has an error-preserving
represented result. This statement does not discard failing applications. -/
theorem result_representation (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy)
    (r : Result ValValSem)
    (hr : ∀ v, r = .ok v → Represents orc ρ Γ Δ τ v) :
    ∃ q, ResultRepresents orc ρ Γ Δ τ r q := by
  cases r with
  | error e => exact ⟨.error e, rfl⟩
  | ok v =>
    obtain ⟨a, he, ha⟩ := represents_extract orc ρ Γ Δ τ v (hr v rfl)
    exact ⟨.ok ⟨a, ha⟩, he⟩

theorem checked_represents {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : PaperValueResults.EnvWF ε ρ)
    (he : ValHasType ε e τ) :
    ∀ out, denotValB_semSChecked directOracle ρ [] [] e = .ok out →
      Represents directOracle ρ [] [] τ out := by
  intro out ho
  exact canonical_represents _ _ _ _ _ _
    (Metatheory.valueSoundnessLegacy ρ [] [] he out ho)

theorem valueSoundness_represented {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : PaperValueResults.EnvWF ε ρ)
    (he : ValHasType ε e τ) :
    (∃ k, Nonempty (ValTValid ε τ k)) ∧
    (∀ s : ValSpace, ValSpace.dof (directOracle ρ [] []) s =
      (ValSpace.shpOf (directOracle ρ [] []) s).foldr (· * ·) 1) ∧
    ∃ q, ResultRepresents directOracle ρ [] [] τ
      (denotValB_semSChecked directOracle ρ [] [] e) q := by
  obtain ⟨hctx⟩ := hρ.1
  exact ⟨Metatheory.valueTypeSoundness he hctx, fun s => GLang.valueShapeSoundness _ s, result_representation _ _ _ _ _ _
    (checked_represents ρ hρ he)⟩

end GLang.PaperValueDomains
