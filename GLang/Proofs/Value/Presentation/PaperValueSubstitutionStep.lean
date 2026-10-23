import GLang.Proofs.Value.Binding.ValueSubstitutionValidity
import GLang.Proofs.Value.Runtime.RuntimeValueEmbedding
import GLang.Proofs.Value.Runtime.RuntimeValueQueryFinite
import GLang.Proofs.Value.Presentation.PaperValueRawReshape
import GLang.Proofs.Value.Presentation.PaperValueSubstitutionQueries
import GLang.Proofs.Value.Presentation.PaperValueSubstitutionInference

namespace GLang.PaperValueDomains

/-- Simultaneous type conclusion used by the original mutual induction.
Base spaces retain every queried leaf, not merely their total dimension. -/
def TypeSubstitutionResult (w w' : World) (x : VName) (u : ValExpr) (τ : ValTy) : Prop :=
  RawTypePresentation directOracle τ (ValTy.subst x u τ) w w' ∧
    ∀ s, τ = .space s → SubstSpaceAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) x u s

def ExprSubstitutionResult (w w' : World) (x : VName) (u : ValExpr)
    (e : ValExpr) (τ : ValTy) : Prop :=
  (denotValB_semS directOracle w.env w.types w.values e =
    denotValB_semS directOracle w'.env w'.types w'.values (ValExpr.subst x u e)) ∧
      TypeSubstitutionResult w w' x u τ

/-- Numerical operand IHs in a syntax-indexed form suitable for the finite
query/evaluator lemmas. -/
def OperandSubstitutionResult (w w' : World) (x : VName) (u : ValExpr) (e : ValExpr) : Prop :=
  (denotValB_semS directOracle w.env w.types w.values e =
    denotValB_semS directOracle w'.env w'.types w'.values (ValExpr.subst x u e)) ∧
  SubstSpaceAgreement (directOracle w.env w.types w.values)
    (directOracle w'.env w'.types w'.values) x u (ValExpr.inferSpaceCtx w.types e)

theorem ExprSubstitutionResult.operand {w w' : World} {x : VName} {u e : ValExpr}
    {ε : ValCtx} {s : ValSpace} (ht : ValHasType ε e (.space s))
    (h : ExprSubstitutionResult w w' x u e (.space s)) :
    OperandSubstitutionResult w w' x u e := by
  exact ⟨h.1, by rw [ValExpr.inferSpaceCtx_eq_of_typed ht]; exact h.2.2 s rfl⟩

/-- All primitive cases of the original named-substitution induction, including
FFS-dependent inferred result types and their genuine oracle rank calls. -/
theorem original_numeric_substitution_result {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    {x : VName} {u : ValExpr} {τx : ValTy} (sd : ValSubstData x u ε τx)
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (w w' : World) (hΓ : w.types = w'.types)
    (hf : ValueQueryDependencies.Finite (.expr w.types e))
    (hf' : ValueQueryDependencies.Finite (.expr w'.types (ValExpr.subst x u e)))
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      SubstSpaceAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) x u q)
    (hi : ∀ a ∈ primitiveOperands e, OperandSubstitutionResult w w' x u a) :
    ExprSubstitutionResult w w' x u e (.space s) := by
  have hie : ∀ a ∈ primitiveOperands e,
      denotValB_semS directOracle w.env w.types w.values a =
      denotValB_semS directOracle w'.env w'.types w'.values (ValExpr.subst x u a) :=
    fun a hm => (hi a hm).1
  have hit : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      SubstSpaceAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) x u t := by
    intro a hm t hat
    simpa only [ValExpr.inferSpaceCtx_eq_of_typed hat] using (hi a hm).2
  have hsub : ∀ a ∈ primitiveOperands e,
      ValExpr.inferSpaceCtx w'.types (ValExpr.subst x u a) =
        ValSpace.subst x u (ValExpr.inferSpaceCtx w.types a) := by
    intro a hm
    obtain ⟨t,⟨hat⟩⟩ := original_primitive_operand_typed ht hp a hm
    exact hat.inferSpace_subst sd w.types w'.types
  have ho := original_primitive_subst_output ht hp w w' x u hf hf' hsub ha hit hie
  refine ⟨?_, ho.dof, ?_⟩
  · apply arrayPrimitive_eval_subst directOracle e w w' x u hp hΓ
    · intro a hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ht.inferSpace_subst sd w.types w'.types
      · obtain ⟨t,⟨hat⟩⟩ := original_primitive_operand_typed ht hp a hm
        exact hat.inferSpace_subst sd w.types w'.types
    · exact original_primitive_subst_queries ht hp w w' x u hf hf' hsub ha hit hie
    · exact hie
  · intro t heq
    cases heq
    exact ho

theorem original_numeric_substitution_result_closed {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    {x : VName} {u : ValExpr} {τx : ValTy} (sd : ValSubstData x u ε τx)
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (hv : ValCtxValid ε) (ρ ρ' : ValEnvSem)
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      SubstSpaceAgreement (directOracle ρ [] [])
        (directOracle ρ' [] []) x u q)
    (hi : ∀ a ∈ primitiveOperands e, OperandSubstitutionResult ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ x u a) :
    ExprSubstitutionResult ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ x u e (.space s) := by
  exact original_numeric_substitution_result sd ht hp ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ rfl
    (RuntimeValue.validExpr_queryFinite hv.runtime ht.runtime).1
    (RuntimeValue.validExpr_queryFinite (hv.subst sd).runtime (ht.subst sd).runtime).1 ha hi

end GLang.PaperValueDomains
