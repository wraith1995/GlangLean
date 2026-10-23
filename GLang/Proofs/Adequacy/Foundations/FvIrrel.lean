import GLang.Proofs.Value.Binding.ValueBetaFv
import GLang.Proofs.Adequacy.Foundations.Agree
import GLang.Proofs.Adequacy.Foundations.Dims

namespace GLang

/-- Every type in a de Bruijn type context avoids `y`. -/
def ValTyCtxFresh (y : VName) (Γ : List ValTy) : Prop :=
  ∀ τ ∈ Γ, y ∉ ValTy.fv τ

/-- Extending a fresh de Bruijn type context preserves freshness. -/
theorem ValTyCtxFresh.cons {y : VName} {τ : ValTy} {Γ : List ValTy}
    (hτ : y ∉ ValTy.fv τ) (hΓ : ValTyCtxFresh y Γ) :
    ValTyCtxFresh y (τ :: Γ) := by
  intro τ' hτ'
  rcases List.mem_cons.mp hτ' with rfl | hτ'
  · exact hτ
  · exact hΓ τ' hτ'

def OracleFvIrrel (orc : FFSOracleSem) : Prop :=
  ∀ (ρ : ValEnvSem) (y : VName) (w : ValValSem) (Γ : List ValTy) (Δ : List ValValSem)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr),
    ValTyCtxFresh y Γ →
    y ∉ ValSpace.fv s → y ∉ ValExpr.fv e →
    orc (ρ.update y w) Γ Δ p s e = orc ρ Γ Δ p s e

/-- `dof` transport under an update at a name outside the space's free names. -/
theorem ValSpace.dof_update_of_not_mem_fv {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) (Γ : List ValTy) (Δ : List ValValSem)
    (hΓ : ValTyCtxFresh y Γ) :
    ∀ s : ValSpace, y ∉ ValSpace.fv s →
      ValSpace.dof (orc (ρ.update y w) Γ Δ) s = ValSpace.dof (orc ρ Γ Δ) s
  | .empty, _ => by simp
  | .real, _ => by simp
  | .dsum s₀ s₁, hy => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hy
      simp only [ValSpace.dof_dsum]
      rw [ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ s₀ hy.1,
        ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ s₁ hy.2]
  | .tprod s₀ s₁, hy => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hy
      simp only [ValSpace.dof_tprod]
      rw [ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ s₀ hy.1,
        ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ s₁ hy.2]
  | .ffs p s e, hy => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hy
      simp only [ValSpace.dof_ffs]
      exact hirr ρ y w Γ Δ p s e hΓ hy.1 hy.2

/-- `shpOf` transport under an update at a name outside the space's free names. -/
theorem ValSpace.shpOf_update_of_not_mem_fv {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) (Γ : List ValTy) (Δ : List ValValSem)
    (hΓ : ValTyCtxFresh y Γ) (s : ValSpace) (hy : y ∉ ValSpace.fv s) :
    ValSpace.shpOf (orc (ρ.update y w) Γ Δ) s = ValSpace.shpOf (orc ρ Γ Δ) s := by
  cases s with
  | empty => simp
  | real => simp
  | dsum s₀ s₁ =>
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hy
      simp only [ValSpace.shpOf_dsum]
      rw [ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ s₀ hy.1,
        ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ s₁ hy.2]
  | tprod s₀ s₁ =>
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hy
      simp only [ValSpace.shpOf_tprod]
      rw [ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ s₀ hy.1,
        ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ s₁ hy.2]
  | ffs p s e =>
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hy
      simp only [ValSpace.shpOf_ffs]
      rw [hirr ρ y w Γ Δ p s e hΓ hy.1 hy.2]

end GLang

namespace GLang

/-! ## Free names of the syntactic inference functions under a de Bruijn type context

`inferSpaceCtx Γ e` / `inferTypeCtx Γ e` read `Γ` only at `.bvar k` (`Γ.getD k default`), so
their free names lie in `fv e ∪ ⋃ fv Γ`. Stated in "not-mem" form, which is what the
transports consume. -/

theorem ValSpace.notMem_fv_empty (y : VName) : y ∉ ValSpace.fv .empty := by
  simp [ValSpace.fv]

theorem ValSpace.notMem_fv_real (y : VName) : y ∉ ValSpace.fv .real := by
  simp [ValSpace.fv]

theorem ValTy.notMem_fv_getD {y : VName} {Γ : List ValTy} (hΓ : ∀ τ ∈ Γ, y ∉ ValTy.fv τ)
    (k : Nat) : y ∉ ValTy.fv (Γ.getD k default) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : Γ[k]? with
  | none => simp [ValTy.fv, ValSpace.fv]
  | some τ => exact hΓ τ (List.mem_of_getElem? h)

theorem ValTyCtx.notMem_fv_lookupUse {y : VName} {Γ : List ValTy}
    (hΓ : ∀ τ ∈ Γ, y ∉ ValTy.fv τ) (k : Nat) :
    y ∉ ValTy.fv (ValTyCtx.lookupUse Γ k) := by
  simpa using ValTy.notMem_fv_getD hΓ k

theorem ValTy.notMem_fv_domain {y : VName} {τ : ValTy} (hy : y ∉ ValTy.fv τ) :
    y ∉ ValTy.fv (ValTy.domain τ) := by
  cases τ with
  | space s => exact hy
  | piTy τ₀ τ₁ =>
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      exact hy.1

theorem ValSpace.notMem_fv_spaceOf {y : VName} {τ : ValTy} (hy : y ∉ ValTy.fv τ) :
    y ∉ ValSpace.fv (ValTy.spaceOf τ) :=
  fun h => hy (ValSpace.fv_spaceOf_subset τ h)

/-- Split a `y ∉ fv (match-discriminant)` hypothesis after `cases` on the discriminant. -/
macro "fv_split" h:ident : tactic =>
  `(tactic| (simp only [ValSpace.fv, ValTy.fv, Finset.mem_union, not_or,
      Finset.notMem_empty, not_false_eq_true] at $h:ident ⊢))

theorem ValExpr.notMem_fv_inferTypeCtx (y : VName) :
    ∀ (e : ValExpr) (Γ : List ValTy), y ∉ ValExpr.fv e → (∀ τ ∈ Γ, y ∉ ValTy.fv τ) →
      y ∉ ValTy.fv (ValExpr.inferTypeCtx Γ e)
  | .zero s, _, hy, _ => hy
  | .rlit _, _, _, _ => ValSpace.notMem_fv_real y
  | .scale _ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      exact ValExpr.notMem_fv_inferTypeCtx y e₁ Γ hy.2 hΓ
  | .vadd s _ _, Γ, hy, _ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      exact hy.1.1
  | .dsumE e₀ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      simp only [ValExpr.inferTypeCtx, ValTy.fv, ValSpace.fv, Finset.mem_union, not_or]
      exact ⟨ValSpace.notMem_fv_spaceOf (ValExpr.notMem_fv_inferTypeCtx y e₀ Γ hy.1 hΓ),
        ValSpace.notMem_fv_spaceOf (ValExpr.notMem_fv_inferTypeCtx y e₁ Γ hy.2 hΓ)⟩
  | .tprodE e₀ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      simp only [ValExpr.inferTypeCtx, ValTy.fv, ValSpace.fv, Finset.mem_union, not_or]
      exact ⟨ValSpace.notMem_fv_spaceOf (ValExpr.notMem_fv_inferTypeCtx y e₀ Γ hy.1 hΓ),
        ValSpace.notMem_fv_spaceOf (ValExpr.notMem_fv_inferTypeCtx y e₁ Γ hy.2 hΓ)⟩
  | .delta _ _, _, hy, _ => hy
  | .idelta s, _, hy, _ => by
      simp only [ValExpr.fv] at hy
      simp only [ValExpr.inferTypeCtx, ValTy.fv, ValSpace.fv, Finset.mem_union, not_or]
      exact ⟨hy, hy⟩
  | .vsum _ [], _, _, _ => ValSpace.notMem_fv_empty y
  | .vsum s (e :: es), Γ, hy, hΓ => by
      simp only [ValExpr.fv, ValExpr.fvList, Finset.mem_union, not_or] at hy
      exact ValExpr.notMem_fv_inferTypeCtx y e Γ hy.2.1 hΓ
  | .vlam _ _ _, _, hy, _ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      simp only [ValExpr.inferTypeCtx, ValTy.fv, Finset.mem_union, not_or]
      exact hy.1
  | .bvar k, Γ, _, hΓ => ValTyCtx.notMem_fv_lookupUse hΓ k
  | .var _ τ, _, hy, _ => by
      simp only [ValExpr.fv, Finset.mem_insert, not_or] at hy
      exact hy.2
  | .appV f a, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have hf := ValExpr.notMem_fv_inferTypeCtx y f Γ hy.1 hΓ
      simp only [ValExpr.inferTypeCtx]
      cases h : ValExpr.inferTypeCtx Γ f with
      | space s => exact ValSpace.notMem_fv_empty y
      | piTy d c =>
        rw [h] at hf
        simp only [ValTy.fv, Finset.mem_union, not_or] at hf
        intro hm
        rcases Finset.mem_union.mp (ValTy.fv_substBound_subset a c 0 hm) with hm | hm
        · exact hf.2 hm
        · exact hy.2 hm
  | .reshap _ τ _, _, hy, _ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      exact hy.1.2
  | .ttv _ e₀ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e₀ Γ hy.1.2 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e₀ <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .mtm _ _ _ _ e₀ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih₀ := ValExpr.notMem_fv_inferTypeCtx y e₀ Γ hy.1.2 hΓ
      have ih₁ := ValExpr.notMem_fv_inferTypeCtx y e₁ Γ hy.2 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih₀ ih₁
      cases h₀ : ValExpr.inferTypeCtx Γ e₀ with
      | piTy _ _ => intro ih₀ ih₁; dsimp only; exact ValSpace.notMem_fv_empty y
      | space s₀ =>
        cases h₁ : ValExpr.inferTypeCtx Γ e₁ with
        | piTy _ _ => intro ih₀ ih₁; cases s₀ <;> dsimp only <;> exact ValSpace.notMem_fv_empty y
        | space s₁ =>
          intro ih₀ ih₁
          cases s₀ <;> cases s₁ <;> (try dsimp only) <;> (try fv_split ih₀) <;>
            (try fv_split ih₁) <;> (try tauto)
  | .vkrn e₀ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih₀ := ValExpr.notMem_fv_inferTypeCtx y e₀ Γ hy.1 hΓ
      have ih₁ := ValExpr.notMem_fv_inferTypeCtx y e₁ Γ hy.2 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih₀ ih₁
      cases h₀ : ValExpr.inferTypeCtx Γ e₀ with
      | piTy _ _ => intro ih₀ ih₁; dsimp only; exact ValSpace.notMem_fv_empty y
      | space s₀ =>
        cases h₁ : ValExpr.inferTypeCtx Γ e₁ with
        | piTy _ _ => intro ih₀ ih₁; cases s₀ <;> dsimp only <;> exact ValSpace.notMem_fv_empty y
        | space s₁ =>
          intro ih₀ ih₁
          cases s₀ <;> cases s₁ <;> (try dsimp only) <;> (try fv_split ih₀) <;>
            (try fv_split ih₁) <;> (try tauto)
  | .vblk e₀ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih₀ := ValExpr.notMem_fv_inferTypeCtx y e₀ Γ hy.1 hΓ
      have ih₁ := ValExpr.notMem_fv_inferTypeCtx y e₁ Γ hy.2 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih₀ ih₁
      cases h₀ : ValExpr.inferTypeCtx Γ e₀ with
      | piTy _ _ => intro ih₀ ih₁; dsimp only; exact ValSpace.notMem_fv_empty y
      | space s₀ =>
        cases h₁ : ValExpr.inferTypeCtx Γ e₁ with
        | piTy _ _ => intro ih₀ ih₁; cases s₀ <;> dsimp only <;> exact ValSpace.notMem_fv_empty y
        | space s₁ =>
          intro ih₀ ih₁
          cases s₀ <;> cases s₁ <;> (try dsimp only) <;> (try fv_split ih₀) <;>
            (try fv_split ih₁) <;> (try tauto)
  | .vtrans e, Γ, hy, hΓ => by
      simp only [ValExpr.fv] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e Γ hy hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .gsvdS e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .gsvdU e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .gsvdUI e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .gsvdV e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .gsvdVI e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .pinv e, Γ, hy, hΓ => by
      simp only [ValExpr.fv] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e Γ hy hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .gpinv e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .rrefRep _ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e₁ Γ hy.2 hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e₁ <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .inv e, Γ, hy, hΓ => by
      simp only [ValExpr.fv] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e Γ hy hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)
  | .svds e, Γ, hy, hΓ => by
      simp only [ValExpr.fv] at hy
      have ih := ValExpr.notMem_fv_inferTypeCtx y e Γ hy hΓ
      simp only [ValExpr.inferTypeCtx]
      revert ih; cases ValExpr.inferTypeCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
      all_goals (rename_i sp; cases sp <;> (try dsimp only) <;> (try fv_split ih) <;> tauto)

theorem ValExpr.notMem_fv_inferSpaceCtx (y : VName) :
    ∀ (e : ValExpr) (Γ : List ValTy), y ∉ ValExpr.fv e → (∀ τ ∈ Γ, y ∉ ValTy.fv τ) →
      y ∉ ValSpace.fv (ValExpr.inferSpaceCtx Γ e)
  | .zero s, _, hy, _ => hy
  | .rlit _, _, _, _ => ValSpace.notMem_fv_real y
  | .scale _ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      exact ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
  | .vadd s _ _, Γ, hy, _ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      exact hy.1.1
  | .dsumE e₀ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      simp only [ValExpr.inferSpaceCtx, ValSpace.fv, Finset.mem_union, not_or]
      exact ⟨ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ,
        ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ⟩
  | .tprodE e₀ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      simp only [ValExpr.inferSpaceCtx, ValSpace.fv, Finset.mem_union, not_or]
      exact ⟨ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ,
        ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ⟩
  | .delta _ _, _, hy, _ => hy
  | .idelta s, _, hy, _ => by
      simp only [ValExpr.fv] at hy
      simp only [ValExpr.inferSpaceCtx, ValSpace.fv, Finset.mem_union, not_or]
      exact ⟨hy, hy⟩
  | .vsum _ [], _, _, _ => ValSpace.notMem_fv_empty y
  | .vsum s (e :: es), Γ, hy, hΓ => by
      simp only [ValExpr.fv, ValExpr.fvList, Finset.mem_union, not_or] at hy
      exact ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.2.1 hΓ
  | .vlam _ _ _, _, _, _ => ValSpace.notMem_fv_empty y
  | .bvar k, Γ, _, hΓ =>
      ValSpace.notMem_fv_spaceOf (ValTyCtx.notMem_fv_lookupUse hΓ k)
  | .var _ τ, _, hy, _ => by
      simp only [ValExpr.fv, Finset.mem_insert, not_or] at hy
      exact ValSpace.notMem_fv_spaceOf hy.2
  | .appV f a, Γ, hy, hΓ =>
      ValSpace.notMem_fv_spaceOf (ValExpr.notMem_fv_inferTypeCtx y (.appV f a) Γ hy hΓ)
  | .reshap _ τ _, _, hy, _ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      exact ValSpace.notMem_fv_spaceOf hy.1.2
  | .ttv _ e₀ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1.2 hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih; cases ValExpr.inferSpaceCtx Γ e₀ <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
  | .mtm _ _ _ _ e₀ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih₀ := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1.2 hΓ
      have ih₁ := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih₀ ih₁; cases ValExpr.inferSpaceCtx Γ e₀ <;> cases ValExpr.inferSpaceCtx Γ e₁ <;>
        intro ih₀ ih₁ <;> (try dsimp only) <;> (try fv_split ih₀) <;> (try fv_split ih₁) <;>
        (try tauto)
  | .vkrn e₀ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih₀ := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ
      have ih₁ := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih₀ ih₁; cases ValExpr.inferSpaceCtx Γ e₀ <;> cases ValExpr.inferSpaceCtx Γ e₁ <;>
        intro ih₀ ih₁ <;> (try dsimp only) <;> (try fv_split ih₀) <;> (try fv_split ih₁) <;>
        (try tauto)
  | .vblk e₀ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih₀ := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ
      have ih₁ := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih₀ ih₁; cases ValExpr.inferSpaceCtx Γ e₀ <;> cases ValExpr.inferSpaceCtx Γ e₁ <;>
        intro ih₀ ih₁ <;> (try dsimp only) <;> (try fv_split ih₀) <;> (try fv_split ih₁) <;>
        (try tauto)
  | .vtrans e, Γ, hy, hΓ => by
      simp only [ValExpr.fv] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih; cases ValExpr.inferSpaceCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
  | .gsvdS e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferSpaceCtx]
      fv_split ih; tauto
  | .gsvdU e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih; cases ValExpr.inferSpaceCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
  | .gsvdUI e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih; cases ValExpr.inferSpaceCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
  | .gsvdV e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih; cases ValExpr.inferSpaceCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
  | .gsvdVI e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih; cases ValExpr.inferSpaceCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
  | .pinv e, Γ, hy, hΓ => by
      simp only [ValExpr.fv] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih; cases ValExpr.inferSpaceCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
  | .gpinv e _ _, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih; cases ValExpr.inferSpaceCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
  | .rrefRep _ e₁, Γ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih; cases ValExpr.inferSpaceCtx Γ e₁ <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
  | .inv e, Γ, hy, hΓ => by
      simp only [ValExpr.fv] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      simp only [ValExpr.inferSpaceCtx]
      revert ih; cases ValExpr.inferSpaceCtx Γ e <;> intro ih <;> (try dsimp only) <;>
        (try fv_split ih) <;> (try tauto)
  | .svds e, Γ, hy, hΓ => by
      simp only [ValExpr.fv] at hy
      have ih := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      simp only [ValExpr.inferSpaceCtx]
      fv_split ih; tauto

/-! ## The transports: `denotValTyS`, `reshapDenotSemS`, `denotValB_semS`

All three read `ρ` only through the oracle `orc ρ Γ Δ` (via `dof`) and, for `denotValB_semS`,
through the `.var x _` lookup. Under `OracleFvIrrel orc`, an update at a name `y` outside the
free names is therefore invisible. `denotValB_semS` additionally consults `inferSpaceCtx Γ`,
which reads the de Bruijn type context at `.bvar`s, hence the extra scoping hypothesis on `Γ`
(trivial at `Γ = []`, preserved under `.vlam` by the annotation's freshness). -/

theorem denotValTyS_update_of_not_mem_fv {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) :
    ∀ (τ : ValTy) (Γ : List ValTy) (Δ : List ValValSem),
      ValTyCtxFresh y Γ → y ∉ ValTy.fv τ →
      denotValTyS orc (ρ.update y w) Γ Δ τ = denotValTyS orc ρ Γ Δ τ
  | .space s, Γ, Δ, hΓ, hy => by
      simp only [ValTy.fv] at hy
      rw [denotValTyS_space, denotValTyS_space,
        ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ s hy]
  | .piTy τ₀ τ₁, Γ, Δ, hΓ, hy => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      rw [denotValTyS, denotValTyS]
      (try dsimp only)
      rw [denotValTyS_update_of_not_mem_fv hirr ρ y w τ₀ Γ Δ hΓ hy.1]
      congr 1
      funext v
      exact denotValTyS_update_of_not_mem_fv hirr ρ y w τ₁ (τ₀ :: Γ) _
        (ValTyCtxFresh.cons hy.1 hΓ) hy.2

theorem reshapDenotSemBetweenS_update_of_not_mem_fv {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc) (ρ : ValEnvSem) (y : VName) (w : ValValSem) :
    ∀ (v : ValValSem) (τt τs : ValTy)
      (Γt : List ValTy) (Δt : List ValValSem)
      (Γs : List ValTy) (Δs : List ValValSem),
      ValTyCtxFresh y Γt → ValTyCtxFresh y Γs →
      y ∉ ValTy.fv τt → y ∉ ValTy.fv τs →
      reshapDenotSemBetweenS orc (ρ.update y w) Γt Δt Γs Δs v τt τs =
        reshapDenotSemBetweenS orc ρ Γt Δt Γs Δs v τt τs
  | .array a, .space s, τs, Γt, Δt, Γs, Δs, hΓt, hΓs, hyt, hys => by
      simp only [ValTy.fv] at hyt
      cases τs with
      | space ss =>
          simp only [ValTy.fv] at hys
          simp only [reshapDenotSemBetweenS, reshapArrayBetweenS]
          rw [ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γs Δs hΓs ss hys,
            ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γt Δt hΓt s hyt]
      | piTy _ _ => simp [reshapDenotSemBetweenS, reshapArrayBetweenS]
  | .fn T f, .space s, τs, Γt, Δt, Γs, Δs, _, _, _, _ => by
      rw [reshapDenotSemBetweenS.eq_2, reshapDenotSemBetweenS.eq_2]
  | v, .piTy τt₀ τt₁, .piTy τs₀ τs₁, Γt, Δt, Γs, Δs,
      hΓt, hΓs, hyt, hys => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hyt hys
      rw [reshapDenotSemBetweenS.eq_3, reshapDenotSemBetweenS.eq_3]
      rw [denotValTyS_update_of_not_mem_fv hirr ρ y w τt₀ Γt Δt hΓt hyt.1,
        denotValTyS_update_of_not_mem_fv hirr ρ y w τs₀ Γs Δs hΓs hys.1]
      apply congrArg Except.ok
      apply congrArg _
      funext a
      dsimp only
      generalize hcheck : ValValSem.fromElChecked
        (denotValTyS orc ρ Γt Δt τt₀) a = checkResult
      cases checkResult with
      | error _ => simp [hcheck]
      | ok argT =>
          simp only [hcheck]
          rw [reshapDenotSemBetweenS_update_of_not_mem_fv hirr ρ y w
            argT τs₀ τt₀ Γs Δs Γt Δt hΓs hΓt hys.1 hyt.1]
          generalize harg : reshapDenotSemBetweenS orc ρ Γs Δs Γt Δt
            argT τs₀ τt₀ = argResult
          cases argResult with
          | error _ => simp
          | ok argS =>
              generalize hdecode : ValValSem.toEl (denotValTyS orc ρ Γs Δs τs₀) argS =
                decodeResult
              cases decodeResult with
              | error _ => simp [hdecode]
              | ok argEl =>
                  generalize happ : v.applyTyped argEl = appResult
                  cases appResult with
                  | error _ => simp [hdecode, happ]
                  | ok res =>
                      simp only [hdecode, happ]
                      exact reshapDenotSemBetweenS_update_of_not_mem_fv hirr ρ y w
                        res τt₁ τs₁
                        (τt₀ :: Γt) (argT :: Δt)
                        (τs₀ :: Γs) (argS :: Δs)
                        (ValTyCtxFresh.cons hyt.1 hΓt)
                        (ValTyCtxFresh.cons hys.1 hΓs) hyt.2 hys.2
  | v, .piTy τt₀ τt₁, .space s, Γt, Δt, Γs, Δs, _, _, _, _ => by
      rw [reshapDenotSemBetweenS.eq_4, reshapDenotSemBetweenS.eq_4]
  termination_by _ τt τs _ _ _ _ _ _ => ValTy.kindSize τt + ValTy.kindSize τs
  decreasing_by all_goals simp only [ValTy.kindSize_piTy]; omega

theorem reshapDenotSemS_update_of_not_mem_fv {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) (Γ : List ValTy) (Δ : List ValValSem)
    (hΓ : ValTyCtxFresh y Γ) :
    ∀ (v : ValValSem) (τt τs : ValTy), y ∉ ValTy.fv τt → y ∉ ValTy.fv τs →
      reshapDenotSemS orc (ρ.update y w) Γ Δ v τt τs = reshapDenotSemS orc ρ Γ Δ v τt τs := by
  intro v τt τs hyt hys
  rw [reshapDenotSemS_eq_between, reshapDenotSemS_eq_between]
  exact reshapDenotSemBetweenS_update_of_not_mem_fv hirr ρ y w
    v τt τs Γ Δ Γ Δ hΓ hΓ hyt hys

/-- The `.vlam` context extension keeps the scoping hypothesis on `Γ`. -/
theorem ValTy.notMem_fv_cons {y : VName} {τ₀ : ValTy} {Γ : List ValTy}
    (h₀ : y ∉ ValTy.fv τ₀) (hΓ : ∀ τ ∈ Γ, y ∉ ValTy.fv τ) :
    ∀ τ ∈ τ₀ :: Γ, y ∉ ValTy.fv τ := by
  intro τ hτ
  rcases List.mem_cons.mp hτ with rfl | hτ
  · exact h₀
  · exact hΓ τ hτ

/-- Uniform finisher for the `match`-shaped array arms: after `congr 1; funext i`, split the
    discriminant(s) and rewrite the residual `dof`s. -/
macro "fv_dof_finish" hdof:ident h:ident : tactic =>
  `(tactic| (first
      | rfl
      | (simp only [ValSpace.fv, Finset.mem_union, not_or] at $h:ident
         rw [$hdof:ident _ ($h:ident).1, $hdof:ident _ ($h:ident).2])
      | (simp only [ValSpace.fv, Finset.mem_union, not_or] at $h:ident
         rw [$hdof:ident _ ($h:ident).1])
      | (simp only [ValSpace.fv, Finset.mem_union, not_or] at $h:ident
         rw [$hdof:ident _ ($h:ident).2])
      | rw [$hdof:ident _ $h:ident]))

macro "fv_dof_finish_strict" hdof:ident h:ident : tactic =>
  `(tactic| (first
      | rfl
      | (simp only [ValSpace.fv, Finset.mem_union, not_or] at $h:ident
         simp only [ValSpace.dof_tprod, $hdof:ident _ ($h:ident).1, $hdof:ident _ ($h:ident).2] <;> rfl)
      | (simp only [ValSpace.fv, Finset.mem_union, not_or] at $h:ident
         simp only [ValSpace.dof_tprod, $hdof:ident _ ($h:ident).1] <;> rfl)
      | (simp only [ValSpace.fv, Finset.mem_union, not_or] at $h:ident
         simp only [ValSpace.dof_tprod, $hdof:ident _ ($h:ident).2] <;> rfl)
      | simp only [ValSpace.dof_tprod, $hdof:ident _ $h:ident] <;> rfl))

/-- Domain-carrier congruence for the `.appV` arm, phrased on the carrier SEMANTICS (not just
    `.El`) so that it follows by `subst` — no dependent-cast motive. -/
theorem appV_match_congr (v₀ v₁ : ValValSem) {S S' : ValTypeSem} (hS : S = S') :
    (match v₀ with
     | .fn T f =>
         haveI := Classical.dec (T = S.El)
         if h : T = S.El then
           match ValValSem.toElDomainChecked S v₁ with
           | .error err => Except.error err
           | .ok arg => f (h ▸ arg)
         else Except.error DimError.mismatch
     | .array _ => Except.error DimError.mismatch)
      = (match v₀ with
     | .fn T f =>
         haveI := Classical.dec (T = S'.El)
         if h : T = S'.El then
           match ValValSem.toElDomainChecked S' v₁ with
           | .error err => Except.error err
           | .ok arg => f (h ▸ arg)
         else Except.error DimError.mismatch
     | .array _ => Except.error DimError.mismatch) := by
  subst hS; rfl

theorem denotValB_semS_update_of_not_mem_fv {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) :
    ∀ (e : ValExpr) (Γ : List ValTy) (Δ : List ValValSem),
      y ∉ ValExpr.fv e → (∀ τ ∈ Γ, y ∉ ValTy.fv τ) →
      denotValB_semS orc (ρ.update y w) Γ Δ e = denotValB_semS orc ρ Γ Δ e
  | .bvar n, Γ, Δ, _, _ => by rw [denotValB_semS, denotValB_semS]
  | .var x τ, Γ, Δ, hy, _ => by
      simp only [ValExpr.fv, Finset.mem_insert, not_or] at hy
      rw [denotValB_semS, denotValB_semS, ValEnvSem.update_other _ _ _ _ (Ne.symm hy.1)]
  | .rlit r, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.rlit r) Γ hy hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole]
  | .zero s, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.zero s) Γ hy hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole]
  | .scale e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.scale e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₀ Γ Δ hy.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₁ Γ Δ hy.2 hΓ]
      simp only [ValueShape.scale, hdof _
        (ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ)]
  | .vadd s e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      rw [denotValB_semS, denotValB_semS, hdof _ hy.1.1,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₀ Γ Δ hy.1.2 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₁ Γ Δ hy.2 hΓ]
  | .delta n s, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.delta n s) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole, hdof _ hy]
  | .idelta s, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.idelta s) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole, hdof _ hy]
  | .tprodE e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.tprodE e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h1 := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole, hdof _ h1,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₀ Γ Δ hy.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₁ Γ Δ hy.2 hΓ]
      simp only [ValueShape.pair, hdof _ h1, hdof _
        (ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ)]
  | .dsumE e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.dsumE e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole, hdof _ h0,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₀ Γ Δ hy.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₁ Γ Δ hy.2 hΓ]
      simp only [ValueShape.pair, hdof _ h0, hdof _
        (ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ)]
  | .vtrans e, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.vtrans e) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy hΓ]
      simp only [ValueShape.tensor]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
        fv_dof_finish_strict hdof h0
  | .ttv s e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.ttv s e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1.2 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole, hdof _ hy.1.1,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₀ Γ Δ hy.1.2 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₁ Γ Δ hy.2 hΓ]
      simp only [ValueShape.ttv, ValueShape.pair, hdof _ h0, hdof _ hy.1.1,
        hdof _ (ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ)]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e₀ <;> intro h0 <;> (try dsimp only) <;>
        simp only [hdof _ hy.1.1, hdof _
          (ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ)] <;>
        fv_dof_finish_strict hdof h0
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.mtm n₀ n₁ s₀ s₁ e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1.2 hΓ
      have h1 := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole, hdof _ hy.1.1.1,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₀ Γ Δ hy.1.2 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₁ Γ Δ hy.2 hΓ]
      simp only [ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, hdof _ hy.1.1.1]
      congr 1; funext i
      revert h0 h1
      cases ValExpr.inferSpaceCtx Γ e₀ <;> cases ValExpr.inferSpaceCtx Γ e₁ <;>
        intro h0 h1 <;> (try simp only [ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, false_and, and_false, if_false]) <;> (try rfl)
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h0 h1
      simp only [hdof _ hy.1.1.1, hdof _ h0.1, hdof _ h0.2, hdof _ h1.1, hdof _ h1.2]
  | .vkrn e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.vkrn e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ
      have h1 := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₀ Γ Δ hy.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₁ Γ Δ hy.2 hΓ]
      simp only [ValueShape.matrices, ValueShape.tensor]
      congr 1; funext i
      revert h0 h1
      cases ValExpr.inferSpaceCtx Γ e₀ <;> cases ValExpr.inferSpaceCtx Γ e₁ <;>
        intro h0 h1 <;> (try simp only [ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, false_and, and_false, if_false]) <;> (try rfl)
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h0 h1
      simp only [hdof _ h0.1, hdof _ h0.2, hdof _ h1.1, hdof _ h1.2]
  | .vblk e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.vblk e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ
      have h1 := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₀ Γ Δ hy.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₁ Γ Δ hy.2 hΓ]
      simp only [ValueShape.matrices, ValueShape.tensor]
      congr 1; funext i
      revert h0 h1
      cases ValExpr.inferSpaceCtx Γ e₀ <;> cases ValExpr.inferSpaceCtx Γ e₁ <;>
        intro h0 h1 <;> (try simp only [ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, false_and, and_false, if_false]) <;> (try rfl)
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h0 h1
      simp only [hdof _ h0.1, hdof _ h0.2, hdof _ h1.1, hdof _ h1.2]
  | .vsum s es, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.vsum s es) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole, hdof _ hy.1]
      have hm : ((es.take (ValSpace.dof (orc ρ Γ Δ) s)).attach.map
          (fun e => denotValB_semS orc (ρ.update y w) Γ Δ e.val)) =
          ((es.take (ValSpace.dof (orc ρ Γ Δ) s)).attach.map
          (fun e => denotValB_semS orc ρ Γ Δ e.val)) := by
        apply List.map_congr_left
        intro e _
        have hmem : (e : ValExpr) ∈ es := List.mem_of_mem_take e.property
        have hfve : y ∉ ValExpr.fv (e : ValExpr) := fun hc =>
          hy.2 (ValExpr.mem_fvList.mpr ⟨e, hmem, hc⟩)
        exact denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hfve hΓ
      simp only [hm]
  | .reshap e τ τ₀, Γ, Δ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      rw [denotValB_semS, denotValB_semS,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy.1.1 hΓ]
      cases hden : denotValB_semS orc ρ Γ Δ e with
      | error err => rfl
      | ok v =>
          exact reshapDenotSemS_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ v τ τ₀
            hy.1.2 hy.2
  | .pinv e, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.pinv e) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy hΓ]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
        fv_dof_finish hdof h0
  | .inv e, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.inv e) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy hΓ]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
        fv_dof_finish hdof h0
  | .svds e, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.svds e) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy hΓ]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
        fv_dof_finish hdof h0
  | .gsvdS e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gsvdS e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy.1.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w a Γ Δ hy.1.2 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w b Γ Δ hy.2 hΓ]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
        fv_dof_finish hdof h0
  | .gsvdU e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gsvdU e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy.1.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w a Γ Δ hy.1.2 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w b Γ Δ hy.2 hΓ]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
        fv_dof_finish hdof h0
  | .gsvdUI e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gsvdUI e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy.1.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w a Γ Δ hy.1.2 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w b Γ Δ hy.2 hΓ]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
        fv_dof_finish hdof h0
  | .gsvdV e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gsvdV e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy.1.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w a Γ Δ hy.1.2 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w b Γ Δ hy.2 hΓ]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
        fv_dof_finish hdof h0
  | .gsvdVI e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gsvdVI e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy.1.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w a Γ Δ hy.1.2 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w b Γ Δ hy.2 hΓ]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
        fv_dof_finish hdof h0
  | .gpinv e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gpinv e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e Γ Δ hy.1.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w a Γ Δ hy.1.2 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w b Γ Δ hy.2 hΓ]
      congr 1; funext i
      revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
        fv_dof_finish hdof h0
  | .rrefRep e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.rrefRep e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ
      have h1 := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      rw [denotValB_semS, denotValB_semS, hdof _ hwhole,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₀ Γ Δ hy.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₁ Γ Δ hy.2 hΓ]
      congr 1; funext i
      revert h1; cases ValExpr.inferSpaceCtx Γ e₁ <;> intro h1 <;> (try dsimp only) <;>
        fv_dof_finish hdof h1
  | .vlam τ₀ τ₁ body, Γ, Δ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      rw [denotValB_semS, denotValB_semS]
      (try dsimp only)
      rw [denotValTyS_update_of_not_mem_fv hirr ρ y w τ₀ Γ Δ hΓ hy.1.1]
      congr 1
      apply congrArg (ValValSem.fn (denotValTyS orc ρ Γ Δ τ₀).El)
      funext v
      exact denotValB_semS_update_of_not_mem_fv hirr ρ y w body (τ₀ :: Γ) _ hy.2
        (ValTy.notMem_fv_cons hy.1.1 hΓ)
  | .appV e₀ e₁, Γ, Δ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have hdom : y ∉ ValTy.fv (ValExpr.inferTypeCtx Γ e₀).domain :=
        ValTy.notMem_fv_domain (ValExpr.notMem_fv_inferTypeCtx y e₀ Γ hy.1 hΓ)
      rw [denotValB_semS, denotValB_semS]
      (try dsimp only)
      rw [denotValB_semS_update_of_not_mem_fv hirr ρ y w e₀ Γ Δ hy.1 hΓ,
        denotValB_semS_update_of_not_mem_fv hirr ρ y w e₁ Γ Δ hy.2 hΓ]
      cases h₀ : denotValB_semS orc ρ Γ Δ e₀ with
      | error err => rfl
      | ok v₀ =>
          cases v₀ with
          | array a => rfl
          | fn T f =>
              cases h₁ : denotValB_semS orc ρ Γ Δ e₁ with
              | error err => rfl
              | ok v₁ =>
                  exact appV_match_congr (.fn T f) v₁
                    (denotValTyS_update_of_not_mem_fv hirr ρ y w _ Γ Δ hΓ hdom)
  termination_by e _ _ => ValExpr.size e
  decreasing_by
    all_goals
      first
      | (have hmem : _ ∈ _ := List.mem_of_getElem? ‹_[_]? = some _›
         have hle := ValExpr.size_le_sizeList hmem
         simp only [ValExpr.size]
         omega)
      | (have hle := ValExpr.size_le_sizeList ‹_ ∈ _›
         simp only [ValExpr.size]
         omega)
      | (simp [ValExpr.size]; omega)
      | (simp only [ValExpr.size]; omega)

/-! ## `LegacyAgree` / `LegacyAgreeDims` / `CobAgree` transports

`LegacyAgree`/`LegacyAgreeDims` read `ρ` only through `dof`/`shpOf (orc ρ Γv Δv) sv` and
`denotValTyS orc ρ Γv Δv τv₀`, all on (sub)terms of the VALUE type `τv`. The value stack `Δv`
does not carry named syntax, but the de Bruijn type context `Γv` does; consequently the generic
transport requires both `ValTyCtxFresh y Γv` and `y ∉ ValTy.fv τv`. -/

theorem LegacyAgree.update_of_not_mem_fv {orc : FFSOracleSem} (hirr : OracleFvIrrel orc) (σ : DEnv)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) :
    ∀ (τ : Ty) (τv : ValTy) (Δs : List DVal) (Γv : List ValTy) (Δv : List ValValSem)
      (B : BasisDenot) (x : DVal) (yv : ValValSem), ValTyCtxFresh y Γv →
      y ∉ ValTy.fv τv →
      (LegacyAgree orc σ (ρ.update y w) Δs Γv Δv τ τv B x yv ↔ LegacyAgree orc σ ρ Δs Γv Δv τ τv B x yv)
  | .space s, .space sv, Δs, Γv, Δv, B, x, .array a, hΓv, hy => by
      simp only [ValTy.fv] at hy
      rw [LegacyAgree, LegacyAgree,
        ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γv Δv hΓv sv hy]
  | .space _, .space _, _, _, _, _, _, .fn _ _, _, _ => by rw [LegacyAgree, LegacyAgree]
  | .piTy τ₀ τ₁, .piTy τv₀ τv₁, Δs, Γv, Δv, B, x, yv, hΓv, hy => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      rw [LegacyAgree, LegacyAgree]
      (try dsimp only)
      rw [denotValTyS_update_of_not_mem_fv hirr ρ y w τv₀ Γv Δv hΓv hy.1]
      exact forall_congr' fun x' => forall_congr' fun y' =>
        imp_congr (LegacyAgree.update_of_not_mem_fv hirr σ ρ y w τ₀ τv₀ _ _ _ _ _ _ hΓv hy.1)
          (exists_congr fun y'' => and_congr Iff.rfl
            (LegacyAgree.update_of_not_mem_fv hirr σ ρ y w τ₁ τv₁ _ _ _ _ _ _
              (ValTyCtxFresh.cons hy.1 hΓv) hy.2))
  | .space _, .piTy _ _, _, _, _, _, _, _, _, _ => by rw [LegacyAgree, LegacyAgree]
  | .piTy _ _, .space _, _, _, _, _, _, _, _, _ => by rw [LegacyAgree, LegacyAgree]

theorem LegacyAgreeDims.update_of_not_mem_fv {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (σ : DEnv) (ρ : ValEnvSem) (y : VName) (w : ValValSem) :
    ∀ (τ : Ty) (τv : ValTy) (Δs : List DVal) (Γv : List ValTy) (Δv : List ValValSem),
      ValTyCtxFresh y Γv → y ∉ ValTy.fv τv →
      (LegacyAgreeDims orc σ (ρ.update y w) Δs Γv Δv τ τv ↔ LegacyAgreeDims orc σ ρ Δs Γv Δv τ τv)
  | .space s, .space sv, Δs, Γv, Δv, hΓv, hy => by
      simp only [ValTy.fv] at hy
      rw [LegacyAgreeDims, LegacyAgreeDims,
        ValSpace.shpOf_update_of_not_mem_fv hirr ρ y w Γv Δv hΓv sv hy]
  | .piTy τ₀ τ₁, .piTy τv₀ τv₁, Δs, Γv, Δv, hΓv, hy => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      rw [LegacyAgreeDims, LegacyAgreeDims]
      (try dsimp only)
      rw [denotValTyS_update_of_not_mem_fv hirr ρ y w τv₀ Γv Δv hΓv hy.1]
      exact and_congr
        (LegacyAgreeDims.update_of_not_mem_fv hirr σ ρ y w τ₀ τv₀ _ _ _ hΓv hy.1)
        (exists_congr fun B => forall_congr' fun x' => forall_congr' fun y' =>
          imp_congr
            (LegacyAgree.update_of_not_mem_fv hirr σ ρ y w τ₀ τv₀ _ _ _ _ _ _ hΓv hy.1)
            (LegacyAgreeDims.update_of_not_mem_fv hirr σ ρ y w τ₁ τv₁ _ _ _
              (ValTyCtxFresh.cons hy.1 hΓv) hy.2))
  | .space _, .piTy _ _, _, _, _, _, _ => by rw [LegacyAgreeDims, LegacyAgreeDims]
  | .piTy _ _, .space _, _, _, _, _, _ => by rw [LegacyAgreeDims, LegacyAgreeDims]

theorem CobAgree.update_of_not_mem_fv {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (σ : DEnv) (ρ : ValEnvSem) (y : VName) (w : ValValSem) (bSrc bTgt : Basis)
    (env : ValExpr) (hy : y ∉ ValExpr.fv env) :
    CobAgree orc σ (ρ.update y w) bSrc bTgt env ↔ CobAgree orc σ ρ bSrc bTgt env := by
  unfold CobAgree
  rw [denotValB_semS_update_of_not_mem_fv hirr ρ y w env [] [] hy (by simp [ValTyCtxFresh])]

theorem OracleFvIrrel.const (orc₀ : FFSOracle) : OracleFvIrrel (FFSOracleSem.const orc₀) :=
  fun _ _ _ _ _ _ _ _ _ _ _ => rfl

end GLang
