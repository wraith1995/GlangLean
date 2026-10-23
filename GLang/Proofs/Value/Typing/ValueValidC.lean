

import GLang.Value.Inference

namespace GLang

mutual
  /-- Context-free `⊢ \lsv : svalid` (cf. `ValSValid`, `ε` dropped). -/
  inductive ValSValidC : ValSpace → Type
    | real  : ValSValidC .real
    | empty : ValSValidC .empty
    | dsum  {s₀ s₁} : ValSValidC s₀ → ValSValidC s₁ → ValSValidC (.dsum s₀ s₁)
    | tprod {s₀ s₁} : ValSValidC s₀ → ValSValidC s₁ → ValSValidC (.tprod s₀ s₁)
    -- FFS: the witness's INFERRED type has the matrix shape (was `ValHasType ε leev …`).
    | ffs {p s₀ s₁ leev}
        : ValSValidC s₀
        → ValSValidC s₁
        → ValExpr.inferType leev = .space (.tprod s₀ s₁)
        → ValSValidC (.ffs p (.tprod s₀ s₁) leev)

  /-- Context-free `⊢ \ltyv : tvalid` with kind (cf. `ValTValid`, `ε` dropped; the
      `piTy` rule loses its `x ∉ ε` premise). -/
  inductive ValTValidC : ValTy → ValKind → Type
    | space {s} : ValSValidC s → ValTValidC (.space s) .base
    -- LN (cofinite): the codomain is a body; validate it opened at a fresh `x`
    -- (context-free — the opened var `var x τ₀` is valid with no premise).
    | piTy {τ₀ τ₁ k₀ k₁} (L : Finset VName)
        : ValTValidC τ₀ k₀
        → (∀ x, x ∉ L → ValTValidC (ValTy.openVar x τ₀ τ₁) k₁)
        → ValTValidC (.piTy τ₀ τ₁) (.arrow k₀ k₁)
end

/-- "`τ` is a valid value-type (at some kind)" — the regularity conjunct. -/
def ValTyOk (τ : ValTy) : Prop := ∃ k, Nonempty (ValTValidC τ k)

/-- The FFS bridge (gen-4): `τ` and `τ'` are reshape-coercible iff valid at a
    common kind. -/
def ReshapEq (τ τ' : ValTy) : Prop :=
  ∃ k, Nonempty (ValTValidC τ k) ∧ Nonempty (ValTValidC τ' k)

end GLang

