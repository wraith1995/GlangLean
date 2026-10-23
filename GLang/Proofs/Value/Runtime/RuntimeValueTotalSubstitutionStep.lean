import GLang.Proofs.Value.Binding.ValueSubstitutionValidity
import GLang.Proofs.Value.Runtime.RuntimeValueQueryFinite
import GLang.Proofs.Value.Runtime.RuntimeValueTotalSubstitutionQueries
import GLang.Proofs.Value.Presentation.PaperValueSubstitutionStep

namespace GLang.RuntimeValue.TotalSubstitution
open PaperValueDomains

private theorem inferSpace_subst {x : VName} {u : ValExpr} {ε : ValCtx}
    {τx τ : ValTy} {e : ValExpr} (sd : ValSubstData x u ε τx)
    (h : ValHasType ε e τ) (Γ Γ' : List ValTy) :
    ValExpr.inferSpaceCtx Γ' (ValExpr.subst x u e) =
      ValSpace.subst x u (ValExpr.inferSpaceCtx Γ e) := by
  rw [ValExpr.inferSpaceCtx_eq_spaceOf h,
    ValExpr.inferSpaceCtx_eq_spaceOf (h.subst sd)]
  cases τ <;> rfl

/-- A typed operand retains its inferred space observation even at function
kind, where no array-space observation is needed. -/
theorem operandResult {w w' : World} {x : VName} {u e : ValExpr}
    {ε : ValCtx} {τ : ValTy} (ht : ValHasType ε e τ)
    (h : ExprSubstitutionResult w w' x u e τ) :
    ∃ t, Nonempty (ValHasType ε e t) ∧ ExprSubstitutionResult w w' x u e t :=
  ⟨τ,⟨ht⟩,h⟩

/-- All numerical constructors, with function-typed operands allowed. -/
theorem numeric_substitution_result {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    {x : VName} {u : ValExpr} {τx : ValTy} (sd : ValSubstData x u ε τx)
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (w w' : World) (hΓ : w.types = w'.types)
    (hf : ValueQueryDependencies.Finite (.expr w.types e))
    (hf' : ValueQueryDependencies.Finite (.expr w'.types (ValExpr.subst x u e)))
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      SubstSpaceAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) x u q)
    (hi : ∀ a ∈ primitiveOperands e, ∃ t,
      Nonempty (ValHasType ε a t) ∧ ExprSubstitutionResult w w' x u a t) :
    ExprSubstitutionResult w w' x u e (.space s) := by
  have hie : ∀ a ∈ primitiveOperands e,
      denotValB_semS directOracle w.env w.types w.values a =
      denotValB_semS directOracle w'.env w'.types w'.values (ValExpr.subst x u a) := by
    intro a hm; obtain ⟨t,hat,h⟩ := hi a hm; exact h.1
  have hit : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      SubstSpaceAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) x u t := by
    intro a hm t hat
    obtain ⟨t',⟨hat'⟩,h⟩ := hi a hm
    have heq := hat'.unique hat
    cases heq
    exact h.2.2 t rfl
  have his : ∀ a ∈ primitiveOperands e,
      SubstSpaceAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) x u (ValExpr.inferSpaceCtx w.types a) := by
    intro a hm
    obtain ⟨t,⟨hat⟩,h⟩ := hi a hm
    rw [ValExpr.inferSpaceCtx_eq_spaceOf hat]
    cases t with
    | space s => exact h.2.2 s rfl
    | piTy _ _ => trivial
  have hsub : ∀ a ∈ primitiveOperands e,
      ValExpr.inferSpaceCtx w'.types (ValExpr.subst x u a) =
        ValSpace.subst x u (ValExpr.inferSpaceCtx w.types a) := by
    intro a hm
    obtain ⟨t,⟨hat⟩,_⟩ := hi a hm
    exact inferSpace_subst sd hat w.types w'.types
  have ho := original_primitive_subst_output ht hp w w' x u hf hf' hsub ha hit hie
  refine ⟨?_, ho.dof, ?_⟩
  · apply arrayPrimitive_eval_subst directOracle e w w' x u hp hΓ
    · intro a hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact inferSpace_subst sd ht w.types w'.types
      · obtain ⟨t,⟨hat⟩,_⟩ := hi a hm
        exact inferSpace_subst sd hat w.types w'.types
    · exact original_primitive_subst_queries ht hp w w' x u hf hf' hsub ha hit his hie
    · exact hie
  · intro t heq; cases heq; exact ho

theorem numeric_substitution_result_closed {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    {x : VName} {u : ValExpr} {τx : ValTy} (sd : ValSubstData x u ε τx)
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (hv : ValCtxValid ε) (ρ ρ' : ValEnvSem)
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      SubstSpaceAgreement (directOracle ρ [] [])
        (directOracle ρ' [] []) x u q)
    (hi : ∀ a ∈ primitiveOperands e, ∃ t,
      Nonempty (ValHasType ε a t) ∧ ExprSubstitutionResult ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ x u a t) :
    ExprSubstitutionResult ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ x u e (.space s) := by
  exact numeric_substitution_result sd ht hp ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ rfl
    (RuntimeValue.validExpr_queryFinite hv ht).1
    (RuntimeValue.validExpr_queryFinite (hv.subst sd) (ht.subst sd)).1 ha hi

end GLang.RuntimeValue.TotalSubstitution
