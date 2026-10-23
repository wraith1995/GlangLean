

import GLang.Operational.Ordinary
import GLang.Value.Supporting.StrictTyping
import GLang.Proofs.Value.Typing.ValTValidKindUnique
import Mathlib.Data.Fintype.EquivFin  -- `Infinite.exists_notMem_finset`

namespace GLang

/-- The kind read directly off a SOURCE type's head. -/
def Ty.sourceKind : Ty → ValKind
  | .space _    => .base
  | .piTy τ₀ τ₁ => .arrow τ₀.sourceKind τ₁.sourceKind

def ValTy.structuralKind : ValTy → ValKind
  | .space _    => .base
  | .piTy τ₀ τ₁ => .arrow τ₀.structuralKind τ₁.structuralKind

/-- `sourceKind` is invariant under substitution: `Ty.subst` preserves the
    `.space` / `.piTy` head of every node. -/
theorem Ty.sourceKind_subst (x : Name) (e : Term) :
    (τ : Ty) → (Ty.subst x e τ).sourceKind = τ.sourceKind
  | .space _ => rfl
  | .piTy τ₀ τ₁ => by
      simp only [Ty.subst, Ty.sourceKind,
        Ty.sourceKind_subst x e τ₀, Ty.sourceKind_subst x e τ₁]

/-- `sourceKind` is invariant under `openRec`: opening preserves the `.space` /
    `.piTy` head of every source node. (LN: the source codomain opens via
    `openRec`, not the named `Ty.subst`.) -/
theorem Ty.sourceKind_openRec (k : Nat) (u : Term) :
    (τ : Ty) → (Ty.openRec k u τ).sourceKind = τ.sourceKind
  | .space _ => rfl
  | .piTy τ₀ τ₁ => by
      simp only [Ty.openRec, Ty.sourceKind,
        Ty.sourceKind_openRec k u τ₀, Ty.sourceKind_openRec (k+1) u τ₁]

/-- `structuralKind` is invariant under `openRec`: opening preserves the
    `.space` / `.piTy` head of every node, hence the structural kind. (Replaces
    the named `structuralKind_subst`; the LN codomain opens via `openRec`.) -/
theorem ValTy.structuralKind_openRec (k : Nat) (u : ValExpr) :
    (τ : ValTy) → (ValTy.openRec k u τ).structuralKind = τ.structuralKind
  | .space _ => rfl
  | .piTy τ₀ τ₁ => by
      simp only [ValTy.openRec, ValTy.structuralKind,
        ValTy.structuralKind_openRec k u τ₀, ValTy.structuralKind_openRec (k+1) u τ₁]

/-- The `ValTValid`-kind of a value-type equals its structural kind. The two
    sub-kinds of a `.piTy` recurse on the two sub-derivations — no `subst`
    machinery needed. -/
theorem ValTValid.kind_eq_structural {ε : ValCtx} {τ : ValTy} {k : ValKind}
    (h : ValTValid ε τ k) : k = τ.structuralKind :=
  match h with
  | .space _ => rfl
  | .piTy L h₀ h₁ => by
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset L
      have hc := ValTValid.kind_eq_structural (h₁ y hy)
      rw [ValTy.openVar, ValTy.structuralKind_openRec] at hc
      simp only [ValTy.structuralKind, ValTValid.kind_eq_structural h₀, hc]
  termination_by ValTy.kindSize τ
  decreasing_by
    all_goals simp only [ValTy.kindSize_piTy, ValTy.openVar, ValTy.kindSize_openRec]; omega

/-- Every realization `τv` of a source type `τ` has its structural kind equal to
    `τ`'s source kind. `ValTy.EvalT` lives in a 4-way mutual block
    (`EvalS`/`EvalT`/`OpStep`/`EvalBB`), so plain `induction` is unavailable; we
    use the shared recursor with `motive_2` carrying the statement (the other
    three motives are `True`). The `.piTy` codomain consumes the cofinite body
    premise opened at a fresh `y`; the `_subst` lemmas discard the opening. -/
theorem ValTy.EvalT.structuralKind_eq_sourceKind {Ψ : EvalCtx} {τ : Ty}
    {τv : ValTy} (h : ValTy.EvalT Ψ τ τv) :
    τv.structuralKind = τ.sourceKind := by
  refine ValTy.EvalT.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ τ' τv' _ => τv'.structuralKind = τ'.sourceKind)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?space ?piTy
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    h
  case space =>
    -- `.space s ⇒ .space sv`: both sides are `.base`.
    intro _ _ _ _ _
    rfl
  case piTy =>
    -- `.piTy τ₀ τ₁ ⇒ .piTy τv₀ τv₁` (LN: nameless binder).  `ih₀` is the domain
    -- `motive_2` IH; `ih₁` the cofinite body `motive_2` IH (a `∀ y, y ∉ L → …`).
    intro _ _ τ₀ τ₁ τv₀ τv₁ _ _ L _ ih₀ ih₁
    -- Codomain: open both source/value bodies at a common fresh `y ∉ L`. The VALUE
    -- side opens by `ValTy.openVar`; the SOURCE side by `Ty.openVar` (both LN).
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset L
    have hcod := ih₁ y hy
    dsimp only at hcod
    rw [ValTy.openVar, ValTy.structuralKind_openRec, Ty.openVar,
      Ty.sourceKind_openRec] at hcod
    simp only [ValTy.structuralKind, Ty.sourceKind, ih₀, hcod]
  all_goals (intros; exact trivial)

/-- Two realizations of the SAME source type have equal `structuralKind`. -/
theorem ValTy.EvalT.structuralKind_determined {Ψ : EvalCtx} {τ : Ty}
    {τv₁ τv₂ : ValTy}
    (h₁ : ValTy.EvalT Ψ τ τv₁) (h₂ : ValTy.EvalT Ψ τ τv₂) :
    τv₁.structuralKind = τv₂.structuralKind := by
  rw [h₁.structuralKind_eq_sourceKind, h₂.structuralKind_eq_sourceKind]

/-- **Realization-kind determinacy.** The `ValTValid`-kinds of two realizations
    of the same source type `τ` (under possibly different value contexts) agree.

    This is the `nllam-3-kind` need: the codomain realization `τv₁` (kind `k₁`)
    and the body-value type `τv₂` (kind `k₂`), both realizations of the same
    source `τ₁`, have `k₁ = k₂`, so the `reshap` (equal-kinds) typechecks.
    (Specialize `ρ₁ = ρ₂` for the same-context use site.) -/
theorem ValTy.EvalT.kind_determined {Ψ : EvalCtx} {τ : Ty} {τv₁ τv₂ : ValTy}
    (h₁ : ValTy.EvalT Ψ τ τv₁) (h₂ : ValTy.EvalT Ψ τ τv₂)
    {ρ₁ ρ₂ : ValCtx} {k₁ k₂ : ValKind}
    (hk₁ : ValTValid ρ₁ τv₁ k₁) (hk₂ : ValTValid ρ₂ τv₂ k₂) : k₁ = k₂ := by
  rw [hk₁.kind_eq_structural, hk₂.kind_eq_structural,
    h₁.structuralKind_determined h₂]

end GLang
