import GLang.Proofs.Value.Partial.PartialValueTypeCoherence
import GLang.Proofs.Value.Presentation.PaperValuePrimitiveLocality

/-! Compositionality of numerical partial evaluation using only its finite
space footprint and equal immediate operand results, including failure. -/
namespace GLang.PartialValueDomains
open PaperValueDomains

def partialPrimitiveQuerySpaces (Γ : List ValTy) (e : ValExpr) : List ValSpace :=
  primitiveQuerySpaces Γ e ++ (primitiveOperands e).map (ValExpr.inferSpaceCtx Γ)

private theorem dimensions_congr (q q' : PartialFFSOracle) (ss : List ValSpace)
    (h : ∀ s ∈ ss, s.dofPartial q = s.dofPartial q') :
    PartialValueEval.dimensions q ss = PartialValueEval.dimensions q' ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [PartialValueEval.dimensions,h s List.mem_cons_self,
      ih (fun t ht => h t (List.mem_cons_of_mem s ht))]

private theorem guard_congr (q q' : PartialFFSOracle) (ss : List ValSpace)
    (f g : FFSOracle → Except DimError ValValSem)
    (h : ∀ s ∈ ss, s.dofPartial q = s.dofPartial q')
    (hn : f (PartialValueEval.numbers q) = g (PartialValueEval.numbers q')) :
    PartialValueEval.withDimensions q ss f = PartialValueEval.withDimensions q' ss g := by
  simp only [PartialValueEval.withDimensions,dimensions_congr q q' ss h,hn]

private theorem spaceDof {q q' : FFSOracle} {s : ValSpace}
    (h : SpaceOracleAgreement q q' s) : ValSpace.dof q s = ValSpace.dof q' s :=
  (leafAgreement_shapes q q' s h).2

set_option maxHeartbeats 1600000 in
/-- Numerical compositionality using only the primitive's finite query
footprint. Equal child results include matching failure; no latent callback
identity and no all-query oracle equality is assumed. -/
theorem partial_arrayPrimitive_eval_congr_oracles (orc orc' : PartialFFSOracleSem)
    (e : ValExpr) (w w' : World)
    (hp : ArrayPrimitive e) (hG : w.types = w'.types)
    (hs : ∀ s ∈ partialPrimitiveQuerySpaces w.types e,
      PartialSpaceAgreement (orc w.env w.types w.values)
        (orc' w'.env w'.types w'.values) s)
    (hi : ∀ a ∈ primitiveOperands e,
      denotValB_partial orc w.env w.types w.values a =
        denotValB_partial orc' w'.env w'.types w'.values a) :
    denotValB_partial orc w.env w.types w.values e =
      denotValB_partial orc' w'.env w'.types w'.values e := by
  simp only [hG] at hs hi ⊢
  have hsNum : ∀ s ∈ primitiveQuerySpaces w'.types e,
      SpaceOracleAgreement (PartialValueEval.numbers (orc w.env w'.types w.values))
        (PartialValueEval.numbers (orc' w'.env w'.types w'.values)) s := by
    intro s hm
    exact PartialSpaceAgreement.numbers _ _ s (hs s (by simp only [partialPrimitiveQuerySpaces,List.mem_append]; exact Or.inl hm))
  have hout := spaceDof (hsNum (ValExpr.inferSpaceCtx w'.types e) (by simp [primitiveQuerySpaces]))
  have hin : ∀ s ∈ primitiveInputSpaces w'.types e,
      SpaceOracleAgreement (PartialValueEval.numbers (orc w.env w'.types w.values))
        (PartialValueEval.numbers (orc' w'.env w'.types w'.values)) s := by
    intro s hm
    exact hsNum s (List.mem_cons_of_mem _ hm)
  cases e <;> simp only [ArrayPrimitive] at hp
  all_goals try contradiction
  all_goals
    simp only [denotValB_partial]
    apply guard_congr
    · intro s hsGuard
      exact (PartialSpaceAgreement.observations _ _ s
        (hs s (by simp [partialPrimitiveQuerySpaces,primitiveQuerySpaces,primitiveInputSpaces,primitiveOperands] at hsGuard ⊢; tauto))).2
  all_goals
    simp [primitiveInputSpaces] at hin
    simp [primitiveOperands] at hi
  case vsum s es =>
    have hd := spaceDof hin
    have hm : ((es.take (ValSpace.dof (PartialValueEval.numbers (orc' w'.env w'.types w'.values)) s)).attach.map
        (fun a => denotValB_partial orc w.env w'.types w.values a.1)) =
        ((es.take (ValSpace.dof (PartialValueEval.numbers (orc' w'.env w'.types w'.values)) s)).attach.map
        (fun a => denotValB_partial orc' w'.env w'.types w'.values a.1)) := by
      apply List.map_congr_left
      intro a ha
      exact hi a (List.mem_of_mem_take a.property)
    simp only [hG, hout]
    rw [hd]
    simp only [hm]
  case rlit => simp only [hG, hout]
  case zero => simp only [hG, hout]
  case vadd => simp only [hG, hi, spaceDof hin]
  case delta => simp only [hG, hout, spaceDof hin]
  case idelta => simp only [hG, hout, spaceDof hin]
  case scale => simp only [hG, hout, hi, ValueShape.scale, spaceDof hin]
  case dsumE => simp only [hG, hout, hi, ValueShape.pair,
    spaceDof hin.1, spaceDof hin.2]
  case tprodE => simp only [hG, hout, hi, ValueShape.pair,
    spaceDof hin.1, spaceDof hin.2]
  case vtrans a =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case pinv a =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case inv a =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case svds a =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gpinv a b c =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gsvdS a b c =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gsvdU a b c =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gsvdUI a b c =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gsvdV a b c =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gsvdVI a b c =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case rrefRep a b =>
    have hd := spaceDof hin
    simp only [hG, hout, hi]
    cases he : ValExpr.inferSpaceCtx w'.types b with
    | tprod s t =>
      simp only [he, SpaceOracleAgreement] at hin
      simp only [ValueShape.tensor]
      rw [spaceDof hin.1, spaceDof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case ttv s a b =>
    have hc := spaceDof hin.1
    have ha := hin.2.1
    have hb := spaceDof hin.2.2
    have hd := spaceDof ha
    simp only [hG, hout, hi, ValueShape.ttv, ValueShape.pair, hc, hd, hb]
    cases he : ValExpr.inferSpaceCtx w'.types a with
    | tprod u v =>
      simp only [he, SpaceOracleAgreement] at ha
      simp only [ValSpace.dof_tprod]
      rw [spaceDof ha.1, spaceDof ha.2, hb, hc]
    | empty | real | dsum | ffs =>
      simp only [he] at hd
      simp only [hd, hb, hc]
  case mtm i j s t a b =>
    have hc := spaceDof hin.1
    have ha := hin.2.1
    have hb := hin.2.2
    simp only [hG, hout, hi, ValueShape.mtm, ValueShape.matrices, hc]
    cases he : ValExpr.inferSpaceCtx w'.types a <;>
      cases hf : ValExpr.inferSpaceCtx w'.types b <;>
      simp only [ValueShape.tensor, false_and, and_false, if_false]
    all_goals try rfl
    simp only [he, SpaceOracleAgreement] at ha
    simp only [hf, SpaceOracleAgreement] at hb
    rw [spaceDof ha.1, spaceDof ha.2, spaceDof hb.1, spaceDof hb.2, hc]
  case vkrn a b =>
    have ha := hin.1
    have hb := hin.2
    simp only [hG, hout, hi, ValueShape.matrices]
    cases he : ValExpr.inferSpaceCtx w'.types a <;>
      cases hf : ValExpr.inferSpaceCtx w'.types b <;>
      simp only [ValueShape.tensor, false_and, and_false, if_false]
    all_goals try rfl
    simp only [he, SpaceOracleAgreement] at ha
    simp only [hf, SpaceOracleAgreement] at hb
    rw [spaceDof ha.1, spaceDof ha.2, spaceDof hb.1, spaceDof hb.2]
  case vblk a b =>
    have ha := hin.1
    have hb := hin.2
    simp only [hG, hout, hi, ValueShape.matrices]
    cases he : ValExpr.inferSpaceCtx w'.types a <;>
      cases hf : ValExpr.inferSpaceCtx w'.types b <;>
      simp only [ValueShape.tensor, false_and, and_false, if_false]
    all_goals try rfl
    simp only [he, SpaceOracleAgreement] at ha
    simp only [hf, SpaceOracleAgreement] at hb
    rw [spaceDof ha.1, spaceDof ha.2, spaceDof hb.1, spaceDof hb.2]

theorem partial_arrayPrimitive_eval_congr_local (orc : PartialFFSOracleSem)
    (e : ValExpr) (w w' : World)
    (hp : ArrayPrimitive e) (hG : w.types = w'.types)
    (hs : ∀ s ∈ partialPrimitiveQuerySpaces w.types e,
      PartialSpaceAgreement (orc w.env w.types w.values)
        (orc w'.env w'.types w'.values) s)
    (hi : ∀ a ∈ primitiveOperands e,
      denotValB_partial orc w.env w.types w.values a =
        denotValB_partial orc w'.env w'.types w'.values a) :
    denotValB_partial orc w.env w.types w.values e =
      denotValB_partial orc w'.env w'.types w'.values e :=
  partial_arrayPrimitive_eval_congr_oracles orc orc e w w' hp hG hs hi

end GLang.PartialValueDomains
