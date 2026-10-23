import GLang.Proofs.Adequacy.Total.DirectOracle
import GLang.Proofs.Value.Presentation.PaperValueExtensionality
import GLang.Proofs.Value.Soundness.ValueSoundVals

/-! Extensional value-environment membership, used by value soundness.
Source operational consistency does not require this stronger membership. -/
namespace GLang.PaperValueResults

def EnvWF (ε : ValCtx) (ρ : ValEnvSem) : Prop :=
  Nonempty (ValCtxValid ε) ∧ PaperValueDomains.EnvironmentsRelated directOracle ε ρ ρ

/-- Only declared bindings are constrained; undeclared runtime entries are
irrelevant to the environment membership judgment. -/
theorem EnvWF.member {ε : ValCtx} {ρ : ValEnvSem} (h : EnvWF ε ρ)
    {x : VName} {τ : ValTy} (hx : ε.lookup x = some τ) :
    PaperValueDomains.RuntimeRelated directOracle τ ⟨ρ, [], []⟩ ⟨ρ, [], []⟩
      (ρ x) (ρ x) := h.2 x τ hx

/-- Empty value contexts require no conditions on unused runtime entries. -/
theorem EnvWF.empty (ρ : ValEnvSem) : EnvWF ∅ ρ := by
  constructor
  · exact ⟨fun x τ hx => by simp at hx⟩
  · intro x τ hx
    simp at hx

end GLang.PaperValueResults
