import GLang.Proofs.Value.Presentation.PaperValuePrimitiveLocality
import GLang.Proofs.Value.Runtime.RuntimeValueRegular
import GLang.Proofs.Value.Runtime.RuntimeValueInfer

namespace GLang.RuntimeValue
open PaperValueDomains

private theorem inferredSpace_valid {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (h : ValHasType ε e (.space s)) (hc : ValCtxValid ε) (Γ : List ValTy) :
    Nonempty (ValSValid ε (ValExpr.inferSpaceCtx Γ e)) := by
  rw [ValExpr.inferSpaceCtx_eq_of_typed h]
  exact ⟨valTValid_space_inv (h.regular hc).2⟩

/-- Every dimension actually inspected by a primitive has an original
space-validity derivation. Context validity is used only for regularity. -/
theorem original_primitive_query_valid {ε : ValCtx} {e : ValExpr} {out : ValSpace}
    (h : ValHasType ε e (.space out)) (hp : ArrayPrimitive e) (hc : ValCtxValid ε)
    (hb : ∀ a ∈ primitiveOperands e, ∃ s, Nonempty (ValHasType ε a (.space s)))
    (Γ : List ValTy) (s : ValSpace) (hs : s ∈ primitiveQuerySpaces Γ e) :
    Nonempty (ValSValid ε s) := by
  have hinput : ∀ a ∈ primitiveOperands e,
      Nonempty (ValSValid ε (ValExpr.inferSpaceCtx Γ a)) := by
    intro a ha
    obtain ⟨t,ht⟩ := hb a ha
    exact inferredSpace_valid ht.some hc Γ
  have hout := inferredSpace_valid h hc Γ
  simp only [primitiveQuerySpaces, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact hout
  cases h <;> simp_all [ArrayPrimitive, primitiveInputSpaces,primitiveOperands]
  all_goals first
    | (rcases hs with rfl | rfl | rfl)
    | (rcases hs with rfl | rfl)
    | subst s
  all_goals first
    | exact ⟨by assumption⟩
    | solve_by_elim (maxDepth := 4) [inferredSpace_valid]
    | exact hinput.2
    | assumption

end GLang.RuntimeValue
