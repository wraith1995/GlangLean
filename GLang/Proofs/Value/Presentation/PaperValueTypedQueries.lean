import GLang.Proofs.Value.Presentation.PaperValuePrimitiveLocality
import GLang.Proofs.Value.Soundness.ValueSoundVals
import GLang.Proofs.Value.Typing.ValueInfer

namespace GLang.PaperValueDomains

/-- Numerical operands retain their original base typing derivations. -/
theorem original_primitive_operand_typed {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (h : ValHasType ε e τ) (hp : ArrayPrimitive e)
    (a : ValExpr) (ha : a ∈ primitiveOperands e) :
    ∃ s, Nonempty (ValHasType ε a (.space s)) := by
  cases h <;> simp_all [ArrayPrimitive, primitiveOperands]
  all_goals first
    | exact ⟨_, ⟨by assumption⟩⟩
    | (rename_i s0 s es hdet hsv hf hsvr; exact ⟨s, ⟨hf a ha⟩⟩)
    | aesop (add safe constructors Nonempty)

private theorem inferredSpace_valid {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (h : ValHasType ε e (.space s)) (hc : ValCtxValid ε) (Γ : List ValTy) :
    Nonempty (ValSValid ε (ValExpr.inferSpaceCtx Γ e)) := by
  rw [ValExpr.inferSpaceCtx_eq_of_typed h]
  exact ⟨valTValid_space_inv (h.regular hc).2⟩

/-- Every dimension actually inspected by a primitive has an original
space-validity derivation. Context validity is used only for regularity. -/
theorem original_primitive_query_valid {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (h : ValHasType ε e τ) (hp : ArrayPrimitive e) (hc : ValCtxValid ε)
    (Γ : List ValTy) (s : ValSpace) (hs : s ∈ primitiveQuerySpaces Γ e) :
    Nonempty (ValSValid ε s) := by
  have hb : ∃ s, τ = ValTy.space s := by
    cases h <;> simp_all [ArrayPrimitive]
  obtain ⟨out, rfl⟩ := hb
  have hout := inferredSpace_valid h hc Γ
  simp only [primitiveQuerySpaces, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact hout
  cases h <;> simp_all [ArrayPrimitive, primitiveInputSpaces]
  all_goals first
    | (rcases hs with rfl | rfl | rfl)
    | (rcases hs with rfl | rfl)
    | subst s
  all_goals first
    | exact ⟨by assumption⟩
    | solve_by_elim (maxDepth := 4) [inferredSpace_valid]
    | assumption

end GLang.PaperValueDomains
