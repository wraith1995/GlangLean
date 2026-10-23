

import GLang.Proofs.Progress.Supporting.ProgressMasterDefs

/-! `Basis.IsTyBasis` was originally pinned in this file. -/

namespace GLang.V2

/-- **Stored-basis hereditary well-formedness** — the environment-side guard
    of the P7/P8 statements: every basis keyed in `Ψ` is `IsTyBasis`. -/
def StoredWF (Ψ : EvalCtx) : Prop :=
  ∀ x b, (x, b) ∈ Ψ → Basis.IsTyBasis b

def BasisTransport : Prop :=
  ∀ (Γ : NLCtx) (Ψ : EvalCtx) (e : Term) (b₁ b₂ : Basis) (v₁ : ValExpr),
    PCarrier Ψ → VarsCovered ∅ Γ Ψ → StoredWF Ψ →
    Basis.BasisValid Γ b₁ → Basis.IsTyBasis b₁ →
    Basis.BasisValid Γ b₂ → Basis.IsTyBasis b₂ →
    Basis.tof b₂ = Basis.tof b₁ →
    ValExpr.OpStep Ψ e b₁ v₁ →
    ∃ v₂, ValExpr.OpStep Ψ e b₂ v₂

end GLang.V2
