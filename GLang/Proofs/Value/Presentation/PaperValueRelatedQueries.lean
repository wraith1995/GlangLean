import GLang.Proofs.Value.Presentation.PaperValueDependentOracle
import GLang.Proofs.Value.Presentation.PaperValueSubstitutionQueries

namespace GLang.PaperValueDomains

private theorem directOracle_eq_of_query_step (w w' : World) (p : ValFFSProp)
    (s : ValSpace) (e : ValExpr) (hΓ : w.types = w'.types)
    (hs : SpaceOracleAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) s)
    (he : denotValB_semS directOracle w.env w.types w.values e =
      denotValB_semS directOracle w'.env w'.types w'.values e) :
    SpaceOracleAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) (.ffs p s e) := by
  change directOracle _ _ _ p s e = directOracle _ _ _ p s e
  have hshape := (leafAgreement_shapes _ _ s hs).1
  exact directOracle_eq_of_same_query w w' p s e hΓ hshape he

set_option maxHeartbeats 1800000 in
theorem original_primitive_related_output {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (w w' : World) (hΓ : w.types = w'.types)
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      SpaceOracleAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) q)
    (hi : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      SpaceOracleAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) t)
    (he : ∀ a ∈ primitiveOperands e,
      denotValB_semS directOracle w.env w.types w.values a =
        denotValB_semS directOracle w'.env w'.types w'.values a) :
    SpaceOracleAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) s := by
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
    simp only [SpaceOracleAgreement] at h0 h1 ⊢
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
    have h0 := hi.1 _ (by assumption)
    have hc := directOracle_eq_of_query_step w w' .cokernel _ _ hΓ h0 he.1
    have hk := directOracle_eq_of_query_step w w' .kernel _ _ hΓ h0 he.1
    have him := directOracle_eq_of_query_step w w' .image _ _ hΓ h0 he.1
    have hco := directOracle_eq_of_query_step w w' .coimage _ _ hΓ h0 he.1
    change _ ∧ _
    simp only [SpaceOracleAgreement] at h0
    tauto
  case svds =>
    have h0 := hi _ (by assumption)
    exact ⟨directOracle_eq_of_query_step w w' .cokernel _ _ hΓ h0 he,
      directOracle_eq_of_query_step w w' .image _ _ hΓ h0 he⟩
  case vsum =>
    rename_i s0 es hs0 hdet hbody hs
    cases es with
    | nil => simp only [hdet rfl,SpaceOracleAgreement]
    | cons a es => exact hi a (by simp) s (hbody a (by simp))

theorem original_primitive_related_queries {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (w w' : World) (hΓ : w.types = w'.types)
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      SpaceOracleAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) q)
    (hi : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      SpaceOracleAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) t)
    (he : ∀ a ∈ primitiveOperands e,
      denotValB_semS directOracle w.env w.types w.values a =
        denotValB_semS directOracle w'.env w'.types w'.values a) :
    ∀ q ∈ primitiveQuerySpaces w.types e,
      SpaceOracleAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) q := by
  have hout := original_primitive_related_output ht hp w w' hΓ ha hi he
  have hInf : ∀ a ∈ primitiveOperands e,
      SpaceOracleAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) (ValExpr.inferSpaceCtx w.types a) := by
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

end GLang.PaperValueDomains
