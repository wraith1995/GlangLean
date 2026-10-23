import GLang.Proofs.Value.Partial.PartialValueSubstitutionSpaces
import GLang.Proofs.Value.Typing.ValuePrimitiveAnnotations

namespace GLang.PartialValueSubstitution
open PaperValueDomains

set_option maxHeartbeats 1800000 in
theorem original_primitive_subst_output {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (w w' : World) (x : VName) (u : ValExpr)
    (hf : ValueQueryDependencies.Finite (.expr w.types e))
    (hf' : ValueQueryDependencies.Finite (.expr w'.types (ValExpr.subst x u e)))
    (hsub : ∀ a ∈ primitiveOperands e,
      ValExpr.inferSpaceCtx w'.types (ValExpr.subst x u a) =
        ValSpace.subst x u (ValExpr.inferSpaceCtx w.types a))
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      SpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) x u q)
    (hi : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      SpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) x u t)
    (he : ∀ a ∈ primitiveOperands e,
      denotValB_partial PartialDirectOracle.oracle w.env w.types w.values a =
        denotValB_partial PartialDirectOracle.oracle w'.env w'.types w'.values (ValExpr.subst x u a)) :
    SpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) x u s := by
  cases ht <;> simp only [ArrayPrimitive] at hp
  all_goals try contradiction
  all_goals
    simp [primitiveAnnotationSpaces, primitiveOperands] at ha hi he hsub
  all_goals first
    | exact ha
    | trivial
    | (rename_i h; exact hi _ h)
    | (solve_by_elim (maxDepth := 4))
    | skip
  case scale => exact hi.2 _ (by assumption)
  case dsumE | tprodE | vkrn | vblk | mtm =>
    have h0 := hi.1 _ (by assumption)
    have h1 := hi.2 _ (by assumption)
    simp only [SpaceAgreement] at h0 h1 ⊢
    tauto
  case ttv_space =>
    have h0 := hi.1 _ (by assumption)
    exact h0.2
  case vtrans | pinv_tensor | inv_tensor =>
    have h0 := hi _ (by assumption)
    exact ⟨h0.2,h0.1⟩
  case pinv_raw | inv_raw => exact ⟨trivial,hi _ (by assumption)⟩
  case rrefRep =>
    have h0 := hi.2 _ (by assumption)
    exact ⟨h0.2,h0.1⟩
  case gpinv =>
    have h0 := hi.1 _ (by assumption)
    exact ⟨h0.2,h0.1⟩
  case gsvdS | gsvdU | gsvdUI | gsvdV | gsvdVI =>
    rename_i e a b s0 s1 a0 a1 b0 b1 ht0 ht1 ht2
    have h0 := hi.1 _ (by assumption)
    have hefinite : ValueQueryDependencies.Finite (.expr w.types e) :=
      hf.exprChild (by simp [ValueQueryDependencies.exprChildren])
    have hefinite' : ValueQueryDependencies.Finite (.expr w'.types (ValExpr.subst x u e)) :=
      hf'.exprChild (by simp [ValExpr.subst,ValueQueryDependencies.exprChildren])
    have hsfinite := hefinite.inferSpace
    have hsfinite' := hefinite'.inferSpace
    rw [ValExpr.inferSpaceCtx_eq_of_typed ht0] at hsfinite
    rw [hsub.1, ValExpr.inferSpaceCtx_eq_of_typed ht0] at hsfinite'
    have hq (p : ValFFSProp) := oracle_step w w' x u p (.tprod s0 s1) e
      (.ffs hsfinite hefinite) (.ffs hsfinite' hefinite') h0 he.1
    have hc := hq .cokernel
    have hk := hq .kernel
    have him := hq .image
    have hco := hq .coimage
    change _ ∧ _
    simp only [SpaceAgreement] at h0
    tauto
  case svds =>
    rename_i e s0 s1 ht0
    have h0 := hi _ (by assumption)
    have hefinite : ValueQueryDependencies.Finite (.expr w.types e) :=
      hf.exprChild (by simp [ValueQueryDependencies.exprChildren])
    have hefinite' : ValueQueryDependencies.Finite (.expr w'.types (ValExpr.subst x u e)) :=
      hf'.exprChild (by simp [ValExpr.subst,ValueQueryDependencies.exprChildren])
    have hsfinite := hefinite.inferSpace
    have hsfinite' := hefinite'.inferSpace
    rw [ValExpr.inferSpaceCtx_eq_of_typed ht0] at hsfinite
    rw [hsub, ValExpr.inferSpaceCtx_eq_of_typed ht0] at hsfinite'
    have hq (p : ValFFSProp) := oracle_step w w' x u p (.tprod s0 s1) e
      (.ffs hsfinite hefinite) (.ffs hsfinite' hefinite') h0 he
    exact ⟨hq .cokernel,hq .image⟩
  case vsum =>
    rename_i s0 es hs0 hdet hbody hs
    cases es with
    | nil => simp only [hdet rfl,SpaceAgreement]
    | cons a es => exact hi a (by simp) s (hbody a (by simp))

theorem original_primitive_subst_queries {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (w w' : World) (x : VName) (u : ValExpr)
    (hf : ValueQueryDependencies.Finite (.expr w.types e))
    (hf' : ValueQueryDependencies.Finite (.expr w'.types (ValExpr.subst x u e)))
    (hsub : ∀ a ∈ primitiveOperands e,
      ValExpr.inferSpaceCtx w'.types (ValExpr.subst x u a) =
        ValSpace.subst x u (ValExpr.inferSpaceCtx w.types a))
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      SpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) x u q)
    (hi : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      SpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) x u t)
    (he : ∀ a ∈ primitiveOperands e,
      denotValB_partial PartialDirectOracle.oracle w.env w.types w.values a =
        denotValB_partial PartialDirectOracle.oracle w'.env w'.types w'.values (ValExpr.subst x u a)) :
    ∀ q ∈ primitiveQuerySpaces w.types e,
      SpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) x u q := by
  have hout := original_primitive_subst_output ht hp w w' x u hf hf' hsub ha hi he
  have hInf : ∀ a ∈ primitiveOperands e,
      SpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) x u (ValExpr.inferSpaceCtx w.types a) := by
    intro a ha
    obtain ⟨t,⟨ht⟩⟩ := original_primitive_operand_typed ht hp a ha
    rw [ValExpr.inferSpaceCtx_eq_of_typed ht]
    exact hi a ha t ht
  intro q hq
  simp only [primitiveQuerySpaces,List.mem_cons] at hq
  rcases hq with rfl | hq
  · simpa only [ValExpr.inferSpaceCtx_eq_of_typed ht] using hout
  cases ht <;> simp_all [primitiveInputSpaces,primitiveOperands,primitiveAnnotationSpaces]
  all_goals aesop

end GLang.PartialValueSubstitution
