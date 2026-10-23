/- Kind uniqueness for the value-type validity judgment `ValTValid`. -/

import GLang.Value.Supporting.StrictTyping
import Mathlib.Data.Fintype.EquivFin  -- `Infinite.exists_notMem_finset`

namespace GLang

theorem ValTValid.kind_unique {ε : ValCtx} {τ : ValTy} {k₁ k₂ : ValKind}
    (h₁ : ValTValid ε τ k₁) (h₂ : ValTValid ε τ k₂) : k₁ = k₂ :=
  match h₁, h₂ with
  | .space _, .space _ => rfl
  | .piTy L₁ h₁₀ h₁₁, .piTy L₂ h₂₀ h₂₁ => by
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L₁ ∪ L₂)
      simp only [Finset.mem_union, not_or] at hy
      rw [ValTValid.kind_unique h₁₀ h₂₀,
          ValTValid.kind_unique (h₁₁ y hy.1) (h₂₁ y hy.2)]
  termination_by ValTy.kindSize τ
  decreasing_by
    · simp only [ValTy.kindSize_piTy]; omega
    · simp only [ValTy.kindSize_piTy, ValTy.openVar, ValTy.kindSize_openRec]; omega

end GLang
