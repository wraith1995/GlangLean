

import GLang.Proofs.Preservation.PreservationV2Helpers
import GLang.Operational.Ordinary

namespace GLang

theorem term_dsumE_v2 {Ψ : EvalCtx} {ρ' : Finset VName} {b₀ b₁ : Basis} {v₀ v₁ : ValExpr}
    (htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
    (htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
    (ih0 : (∃ τv, ValTy.EvalT Ψ (Basis.tof b₀) τv ∧ ReshapEq (ValExpr.inferType v₀) τv)
          ∧ ValTyOk (ValExpr.inferType v₀)
          ∧ (ValTy.fv (ValExpr.inferType v₀) ∪ ValExpr.fv v₀ ⊆ ρ'))
    (ih1 : (∃ τv, ValTy.EvalT Ψ (Basis.tof b₁) τv ∧ ReshapEq (ValExpr.inferType v₁) τv)
          ∧ ValTyOk (ValExpr.inferType v₁)
          ∧ (ValTy.fv (ValExpr.inferType v₁) ∪ ValExpr.fv v₁ ⊆ ρ')) :
    (∃ τv, ValTy.EvalT Ψ (Basis.tof (.dsum b₀ b₁)) τv
          ∧ ReshapEq (ValExpr.inferType (.dsumE v₀ v₁)) τv)
    ∧ ValTyOk (ValExpr.inferType (.dsumE v₀ v₁))
    ∧ (ValTy.fv (ValExpr.inferType (.dsumE v₀ v₁)) ∪ ValExpr.fv (.dsumE v₀ v₁) ⊆ ρ') := by
  -- Step 1: unpack the IHs into value spaces.
  obtain ⟨⟨τv₀, hev0, hre0⟩, _ih0b, ih0c⟩ := ih0
  rw [htof₀] at hev0
  obtain ⟨sv₀, hesv0, rfl⟩ := evalT_space_inv hev0
  obtain ⟨valsv0⟩ := ReshapEq.snd_space hre0
  obtain ⟨⟨τv₁, hev1, hre1⟩, _ih1b, ih1c⟩ := ih1
  rw [htof₁] at hev1
  obtain ⟨sv₁, hesv1, rfl⟩ := evalT_space_inv hev1
  obtain ⟨valsv1⟩ := ReshapEq.snd_space hre1
  -- Step 2: component source shapes.
  obtain ⟨s'₀, h0eq, ⟨vs'0⟩⟩ := ReshapEq.fst_base_space hre0
  obtain ⟨s'₁, h1eq, ⟨vs'1⟩⟩ := ReshapEq.fst_base_space hre1
  have hinfer : ValExpr.inferType (.dsumE v₀ v₁) = .space (.dsum s'₀ s'₁) := by
    simp only [ValExpr.inferType, h0eq, h1eq, ValTy.spaceOf]
  refine ⟨⟨.space (.dsum sv₀ sv₁), ?_, ?_⟩, ?_, ?_⟩
  · -- EvalT half.
    show ValTy.EvalT Ψ (Basis.tof (.dsum b₀ b₁)) (.space (.dsum sv₀ sv₁))
    simp only [Basis.tof, Basis.sof]
    exact ValTy.EvalT.space (ValSpace.EvalS.dsum hesv0 hesv1)
  · -- ReshapEq half.
    rw [hinfer]
    exact ReshapEq.of_valid_eqStructKind
      (ValTValidC.space (ValSValidC.dsum vs'0 vs'1))
      (ValTValidC.space (ValSValidC.dsum valsv0 valsv1))
      (by simp [ValTy.structuralKind])
  · -- ValTyOk half.
    rw [hinfer]
    exact ⟨.base, ⟨ValTValidC.space (ValSValidC.dsum vs'0 vs'1)⟩⟩
  · -- fv half.
    rw [hinfer]
    simp only [ValTy.fv, ValSpace.fv, ValExpr.fv]
    intro a ha
    rcases Finset.mem_union.mp ha with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ih0c (Finset.mem_union.mpr (Or.inl
          (by rw [h0eq] at *; exact h)))
      · exact ih1c (Finset.mem_union.mpr (Or.inl
          (by rw [h1eq] at *; exact h)))
    · rcases Finset.mem_union.mp h with h | h
      · exact ih0c (Finset.mem_union.mpr (Or.inr h))
      · exact ih1c (Finset.mem_union.mpr (Or.inr h))

theorem term_tprodE_v2 {Ψ : EvalCtx} {ρ' : Finset VName} {b₀ b₁ : Basis} {v₀ v₁ : ValExpr}
    (htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
    (htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
    (ih0 : (∃ τv, ValTy.EvalT Ψ (Basis.tof b₀) τv ∧ ReshapEq (ValExpr.inferType v₀) τv)
          ∧ ValTyOk (ValExpr.inferType v₀)
          ∧ (ValTy.fv (ValExpr.inferType v₀) ∪ ValExpr.fv v₀ ⊆ ρ'))
    (ih1 : (∃ τv, ValTy.EvalT Ψ (Basis.tof b₁) τv ∧ ReshapEq (ValExpr.inferType v₁) τv)
          ∧ ValTyOk (ValExpr.inferType v₁)
          ∧ (ValTy.fv (ValExpr.inferType v₁) ∪ ValExpr.fv v₁ ⊆ ρ')) :
    (∃ τv, ValTy.EvalT Ψ (Basis.tof (.tprod b₀ b₁)) τv
          ∧ ReshapEq (ValExpr.inferType (.tprodE v₀ v₁)) τv)
    ∧ ValTyOk (ValExpr.inferType (.tprodE v₀ v₁))
    ∧ (ValTy.fv (ValExpr.inferType (.tprodE v₀ v₁)) ∪ ValExpr.fv (.tprodE v₀ v₁) ⊆ ρ') := by
  obtain ⟨⟨τv₀, hev0, hre0⟩, _ih0b, ih0c⟩ := ih0
  rw [htof₀] at hev0
  obtain ⟨sv₀, hesv0, rfl⟩ := evalT_space_inv hev0
  obtain ⟨valsv0⟩ := ReshapEq.snd_space hre0
  obtain ⟨⟨τv₁, hev1, hre1⟩, _ih1b, ih1c⟩ := ih1
  rw [htof₁] at hev1
  obtain ⟨sv₁, hesv1, rfl⟩ := evalT_space_inv hev1
  obtain ⟨valsv1⟩ := ReshapEq.snd_space hre1
  obtain ⟨s'₀, h0eq, ⟨vs'0⟩⟩ := ReshapEq.fst_base_space hre0
  obtain ⟨s'₁, h1eq, ⟨vs'1⟩⟩ := ReshapEq.fst_base_space hre1
  have hinfer : ValExpr.inferType (.tprodE v₀ v₁) = .space (.tprod s'₀ s'₁) := by
    simp only [ValExpr.inferType, h0eq, h1eq, ValTy.spaceOf]
  refine ⟨⟨.space (.tprod sv₀ sv₁), ?_, ?_⟩, ?_, ?_⟩
  · show ValTy.EvalT Ψ (Basis.tof (.tprod b₀ b₁)) (.space (.tprod sv₀ sv₁))
    simp only [Basis.tof, Basis.sof]
    exact ValTy.EvalT.space (ValSpace.EvalS.tprod hesv0 hesv1)
  · rw [hinfer]
    exact ReshapEq.of_valid_eqStructKind
      (ValTValidC.space (ValSValidC.tprod vs'0 vs'1))
      (ValTValidC.space (ValSValidC.tprod valsv0 valsv1))
      (by simp [ValTy.structuralKind])
  · rw [hinfer]
    exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod vs'0 vs'1)⟩⟩
  · rw [hinfer]
    simp only [ValTy.fv, ValSpace.fv, ValExpr.fv]
    intro a ha
    rcases Finset.mem_union.mp ha with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ih0c (Finset.mem_union.mpr (Or.inl
          (by rw [h0eq] at *; exact h)))
      · exact ih1c (Finset.mem_union.mpr (Or.inl
          (by rw [h1eq] at *; exact h)))
    · rcases Finset.mem_union.mp h with h | h
      · exact ih0c (Finset.mem_union.mpr (Or.inr h))
      · exact ih1c (Finset.mem_union.mpr (Or.inr h))

end GLang

