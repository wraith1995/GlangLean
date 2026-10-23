import GLang.Public.PaperValueResults
import Lean

open GLang GLang.PaperValueDomains GLang.PaperValueResults
namespace ValueEnvironmentTests
noncomputable section

def always : FlatArray → Except DimError FlatArray := fun _ => .ok (FlatArray.zeros 1)
def onlyValid : FlatArray → Except DimError FlatArray :=
  fun a => if a.length = 1 then .ok (FlatArray.zeros 1) else .error .mismatch

def probe : ValValSem :=
  .fn (FlatArray → Except DimError FlatArray) fun f =>
    match f FlatArray.empty with
    | .error e => .error e
    | .ok _ => .ok (.array (FlatArray.zeros 1))

def probeType : ValTy :=
  .piTy (.piTy (.space .real) (.space .real)) (.space .real)

theorem probe_canonical (ρ : ValEnvSem) :
    ValCanonicalSoundOfDenotSemS directOracle ρ [] [] probeType probe := by
  refine ⟨rfl, ?_⟩
  intro f v hv
  change ((match f FlatArray.empty with
    | .error e => .error e
    | .ok _ => .ok (.array (FlatArray.zeros 1))) : Except DimError ValValSem) = .ok v at hv
  split at hv
  · contradiction
  · cases hv
    simp [ValCanonicalSoundOfDenotSemS, FlatArray.zeros, FlatArray.ofFn]

theorem probe_rejected (ε : ValCtx) (ρ : ValEnvSem) (x : VName)
    (hx : ε.lookup x = some probeType) (hv : ρ x = probe) : ¬ EnvWF ε ρ := by
  intro h
  have hp := h.member hx
  rw [hv] at hp
  obtain ⟨_, _, hr⟩ := hp
  have hab : Related directOracle (.piTy (.space .real) (.space .real))
      ⟨ρ, [], []⟩ ⟨ρ, [], []⟩ always onlyValid := by
    intro a b h
    have hb : b.length = 1 := by simpa [Related] using h.2.2
    simp [always, onlyValid, hb, PartialRel, Related, FlatArray.zeros, FlatArray.ofFn]
  have bad := hr always onlyValid hab
  simp [always, onlyValid, FlatArray.empty, FlatArray.ofFn, PartialRel] at bad

-- Ordinary exact arrays are still admitted, and no unused entry is inspected.
example : EnvWF (Finmap.insert "x" (.space .real) ∅)
    (fun _ => .array (FlatArray.zeros 1)) := by
  constructor
  · refine ⟨?_⟩
    intro x τ hx
    by_cases h : x = "x"
    · subst x
      simp at hx
      subst τ
      exact ⟨.base, .space .real⟩
    · simp [h] at hx
  · intro x τ hx
    by_cases h : x = "x"
    · subst x
      simp at hx
      subst τ
      simp [RuntimeRelated, Related, FlatArray.zeros, FlatArray.ofFn]
    · simp [h] at hx

example (ρ : ValEnvSem) : EnvWF ∅ ρ := EnvWF.empty ρ

open Lean Elab Command
elab "check_environment_repair_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``EnvWF.member, ``EnvWF.empty, ``probe_canonical, ``probe_rejected] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "Unexpected environment assumption: {n}: {ax}"

check_environment_repair_axioms
end
end ValueEnvironmentTests
