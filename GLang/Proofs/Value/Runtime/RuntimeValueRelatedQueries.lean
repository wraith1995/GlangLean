import GLang.Proofs.Value.Runtime.RuntimeValueTypedQueries
import GLang.Proofs.Value.Partial.PartialValuePrimitiveLocality
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectAssembly
import GLang.Proofs.Value.Typing.ValuePrimitiveAnnotations

namespace GLang.RuntimeValue
open PartialValueDomains
open PaperValueDomains

private theorem partialOracle_eq_of_query_step (w w' : World) (p : ValFFSProp)
    (s : ValSpace) (e : ValExpr)
    (hf : ValueQueryDependencies.Finite (.expr w.types e))
    (hf' : ValueQueryDependencies.Finite (.expr w'.types e))
    (hi : ValExpr.inferSpaceCtx w.types e = s)
    (hi' : ValExpr.inferSpaceCtx w'.types e = s)
    (hs : PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
      (PartialDirectOracle.oracle w'.env w'.types w'.values) s)
    (he : denotValB_partial PartialDirectOracle.oracle w.env w.types w.values e =
      denotValB_partial PartialDirectOracle.oracle w'.env w'.types w'.values e) :
    PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
      (PartialDirectOracle.oracle w'.env w'.types w'.values) (.ffs p s e) := by
  change PartialDirectOracle.oracle _ _ _ p s e = PartialDirectOracle.oracle _ _ _ p s e
  have hshape := (PartialSpaceAgreement.observations _ _ s hs).1
  have hsfinite := hf.inferSpace
  have hsfinite' := hf'.inferSpace
  rw [hi] at hsfinite
  rw [hi'] at hsfinite'
  rw [PartialDirectLocality.oracle_eq _ _ _ _ _ _ (.ffs hsfinite hf),
    PartialDirectLocality.oracle_eq _ _ _ _ _ _ (.ffs hsfinite' hf'),hshape,he]

set_option maxHeartbeats 1800000 in
theorem partial_original_primitive_related_output {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (w w' : World)
    (hf : ValueQueryDependencies.Finite (.expr w.types e))
    (hf' : ValueQueryDependencies.Finite (.expr w'.types e))
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) q)
    (hi : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) t)
    (he : ∀ a ∈ primitiveOperands e,
      denotValB_partial PartialDirectOracle.oracle w.env w.types w.values a =
        denotValB_partial PartialDirectOracle.oracle w'.env w'.types w'.values a) :
    PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) s := by
  cases ht <;> simp only [ArrayPrimitive] at hp
  all_goals try contradiction
  all_goals
    simp [primitiveAnnotationSpaces, primitiveOperands] at ha hi he
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
    simp only [PartialSpaceAgreement] at h0 h1 ⊢
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
    have hq : ∀ p, PartialSpaceAgreement
        (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) (.ffs p (.tprod s0 s1) e) := by
      intro p
      apply partialOracle_eq_of_query_step w w' p
      · exact hf.exprChild (by simp [ValueQueryDependencies.exprChildren])
      · exact hf'.exprChild (by simp [ValueQueryDependencies.exprChildren])
      · exact ValExpr.inferSpaceCtx_eq_of_typed (by assumption)
      · exact ValExpr.inferSpaceCtx_eq_of_typed (by assumption)
      · exact h0
      · exact he.1
    have hc := hq .cokernel
    have hk := hq .kernel
    have him := hq .image
    have hco := hq .coimage
    change _ ∧ _
    simp only [PartialSpaceAgreement] at h0
    tauto
  case svds =>
    rename_i e s0 s1 ht0
    have h0 := hi _ (by assumption)
    have hq : ∀ p, PartialSpaceAgreement
        (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) (.ffs p (.tprod s0 s1) e) := by
      intro p
      apply partialOracle_eq_of_query_step w w' p
      · exact hf.exprChild (by simp [ValueQueryDependencies.exprChildren])
      · exact hf'.exprChild (by simp [ValueQueryDependencies.exprChildren])
      · exact ValExpr.inferSpaceCtx_eq_of_typed (by assumption)
      · exact ValExpr.inferSpaceCtx_eq_of_typed (by assumption)
      · exact h0
      · exact he
    exact ⟨hq .cokernel,hq .image⟩
  case vsum =>
    rename_i s0 es hs0 hdet hbody hs
    cases es with
    | nil => simp only [hdet rfl,PartialSpaceAgreement]
    | cons a es => exact hi a (by simp) s (hbody a (by simp))

theorem partial_original_primitive_related_queries {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (hb : ∀ a ∈ primitiveOperands e, ∃ t, Nonempty (ValHasType ε a (.space t)))
    (w w' : World)
    (hf : ValueQueryDependencies.Finite (.expr w.types e))
    (hf' : ValueQueryDependencies.Finite (.expr w'.types e))
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) q)
    (hi : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) t)
    (he : ∀ a ∈ primitiveOperands e,
      denotValB_partial PartialDirectOracle.oracle w.env w.types w.values a =
        denotValB_partial PartialDirectOracle.oracle w'.env w'.types w'.values a) :
    ∀ q ∈ partialPrimitiveQuerySpaces w.types e,
      PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) q := by
  have hout := partial_original_primitive_related_output ht hp w w' hf hf' ha hi he
  have hInf : ∀ a ∈ primitiveOperands e,
      PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
        (PartialDirectOracle.oracle w'.env w'.types w'.values) (ValExpr.inferSpaceCtx w.types a) := by
    intro a ha
    obtain ⟨t,⟨ht⟩⟩ := hb a ha
    rw [ValExpr.inferSpaceCtx_eq_of_typed ht]
    exact hi a ha t ht
  intro q hq
  simp only [partialPrimitiveQuerySpaces,List.mem_append,List.mem_map] at hq
  rcases hq with hq | ⟨a,ha,rfl⟩
  · simp only [primitiveQuerySpaces,List.mem_cons] at hq
    rcases hq with rfl | hq
    · simpa only [ValExpr.inferSpaceCtx_eq_of_typed ht] using hout
    cases ht <;> simp_all [primitiveInputSpaces,primitiveOperands,primitiveAnnotationSpaces]
    all_goals aesop
  · exact hInf a ha

end GLang.RuntimeValue
