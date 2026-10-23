import GLang.Proofs.Value.Presentation.PaperValueCorrespondence
open GLang GLang.PaperValueDomains

namespace CorrespondenceTests
variable (orc : FFSOracleSem) (ρ : ValEnvSem)

-- These differ only on malformed (non-length-one) inputs.
def unrestricted : FlatArray → Result FlatArray := fun _ => .ok (FlatArray.zeros 1)
def restricted : FlatArray → Result FlatArray :=
  fun a => if a.length = 1 then .ok (FlatArray.zeros 1) else .error .mismatch

theorem same_successful_inputs (a : SizedFlatArray 1) :
    unrestricted a.val = restricted a.val := by
  simp [unrestricted, restricted, a.property]

theorem different_raw_inputs : unrestricted FlatArray.empty ≠ restricted FlatArray.empty := by
  simp [unrestricted, restricted, FlatArray.empty, FlatArray.ofFn]

example : Admissible orc ρ [] [] (.piTy (.space .real) (.space .real)) unrestricted := by
  intro a _ out h
  cases h
  simp [Admissible, FlatArray.zeros, FlatArray.ofFn]

example : Admissible orc ρ [] [] (.piTy (.space .real) (.space .real)) restricted := by
  intro a ha out h
  have ha' : a.length = 1 := by simpa [Admissible, ValSpace.dof, ValSpace.shpOf] using ha
  simp [restricted, ha'] at h
  cases h
  simp [Admissible, FlatArray.zeros, FlatArray.ofFn]

-- An unrestricted higher-order callback can probe precisely the hidden behavior.
def probe : (FlatArray → Result FlatArray) → Result FlatArray :=
  fun f => match f FlatArray.empty with
    | .error e => .error e
    | .ok _ => .ok (FlatArray.zeros 1)

example : probe unrestricted = .ok (FlatArray.zeros 1) := rfl
example : probe restricted = .error .mismatch := by
  simp [probe, restricted, FlatArray.empty, FlatArray.ofFn]
example : Admissible orc ρ [] []
    (.piTy (.piTy (.space .real) (.space .real)) (.space .real)) probe := by
  intro f _ out h
  change probe f = Except.ok out at h
  unfold probe at h
  split at h
  · contradiction
  · cases h
    simp [Admissible, FlatArray.zeros, FlatArray.ofFn]

-- General dependent fibres: the local environment is extended by the exact
-- ordinary reification of the selected successful representative.
example (Γ : List ValTy) (Δ : List ValValSem) (τ₀ τ₁ : ValTy)
    (f : Represented orc ρ Γ Δ (.piTy τ₀ τ₁))
    (a : Represented orc ρ Γ Δ τ₀) :
    Result (Represented orc ρ (τ₀ :: Γ)
      (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) a.val :: Δ) τ₁) :=
  observe orc ρ Γ Δ τ₀ τ₁ f a

example (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy) :
    ResultRepresents orc ρ Γ Δ τ (.error .mismatch) (.error .mismatch) := rfl

example (s : ValSpace) (a : FlatArray)
    (h : a.length ≠ ValSpace.dof (orc ρ [] []) s) :
    ¬ Represents orc ρ [] [] (.space s) (.array a) := h

#print axioms canonical_represents
#print axioms represents_extract
#print axioms admissible_reifies
#print axioms result_representation
#print axioms valueSoundness_represented
end CorrespondenceTests

namespace CorrespondenceTests
-- The higher-order probe is allowed even by the *existing stronger canonical*
-- contract; hence admissibility alone is not the cause of this distinction.
def runtimeProbe : ValValSem :=
  .fn (FlatArray → Result FlatArray) (fun f => (probe f).map ValValSem.array)

example (orc : FFSOracleSem) (ρ : ValEnvSem) :
    ValCanonicalSoundOfDenotSemS orc ρ [] []
      (.piTy (.piTy (.space .real) (.space .real)) (.space .real)) runtimeProbe := by
  refine ⟨rfl, ?_⟩
  intro f out h
  change (probe f).map ValValSem.array = .ok out at h
  unfold probe at h
  split at h
  · simp [Except.map] at h
  · simp only [Except.map, Except.ok.injEq] at h
    subst out
    simp [ValCanonicalSoundOfDenotSemS, FlatArray.zeros, FlatArray.ofFn]
end CorrespondenceTests

namespace CorrespondenceTests
-- No function of just the successful-input restriction can reproduce this
-- higher-order probe on both of the preceding admissible representatives.
theorem probe_does_not_factor :
    ¬ ∃ P : (SizedFlatArray 1 → Result FlatArray) → Result FlatArray,
      P (fun a => unrestricted a.val) = probe unrestricted ∧
      P (fun a => restricted a.val) = probe restricted := by
  rintro ⟨P, h₀, h₁⟩
  have heq : (fun a : SizedFlatArray 1 => unrestricted a.val) =
      (fun a : SizedFlatArray 1 => restricted a.val) :=
    funext same_successful_inputs
  have h := (h₀.symm.trans (congrArg P heq)).trans h₁
  simp [probe, unrestricted, restricted, FlatArray.empty, FlatArray.ofFn] at h
end CorrespondenceTests
