import GLang.Proofs.Adequacy.Foundations.Consistent

namespace GLang

/-- **The arrow-kind realization-change obligation** (D5, open): at a Π type `LegacyAgree` depends
    on the value type structurally (the argument carrier `denotValTyS … τv₀` and the codomain
    stacks), and `LegacyAgreeDims`'s `∃ B` pins the codomain only for arguments agreeing at ONE
    basis, so the change of realization is not a `dof` rewrite. Stated with both `S.Ty`
    derivations (a Ψ-monotone determinism lemma for `S.Ty` would discharge it by `τv = τv₀`). -/
def AgreeRealizeTransport (orc : FFSOracleSem) : Prop :=
  ∀ {Γ Γ₀ : NLCtx} {Ψ Ψ₀ : EvalCtx} {τ₀ τ₁ : Ty} {τv τv₀ : ValTy}
    (σ : DEnv) (ρ : ValEnvSem) (B : BasisDenot) (x : DVal) (y : ValValSem),
    S.Ty Γ Ψ (.piTy τ₀ τ₁) τv → S.Ty Γ₀ Ψ₀ (.piTy τ₀ τ₁) τv₀ →
    LegacyAgreeDims orc σ ρ [] [] [] (.piTy τ₀ τ₁) τv →
    LegacyAgreeDims orc σ ρ [] [] [] (.piTy τ₀ τ₁) τv₀ →
    LegacyAgree orc σ ρ [] [] [] (.piTy τ₀ τ₁) τv₀ B x y →
    LegacyAgree orc σ ρ [] [] [] (.piTy τ₀ τ₁) τv B x y

def StoreFix (orc : FFSOracleSem) : Prop :=
  ∀ {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem},
    LegacyConsistent orc Δ Γ Ψ Γv σ ρ →
    ∀ (x : VName) (b : Basis) (v : ValExpr), EvalCtx.lookup Ψ (x, b) = some v →
      denotValB_semS orc ρ [] [] v = .ok (ρ x)

end GLang
