import GLang.Proofs.Value.Presentation.PaperValuePrimitiveLocality

/-! One numerical step commutes with named substitution once its proper child
computations and finite oracle leaves do. This compares different syntax and
retains every shape guard and error. -/
namespace GLang.PaperValueDomains

def SubstSpaceAgreement (q q' : FFSOracle) (x : VName) (u : ValExpr) : ValSpace → Prop
  | .empty | .real => True
  | .dsum s t | .tprod s t =>
      SubstSpaceAgreement q q' x u s ∧ SubstSpaceAgreement q q' x u t
  | .ffs p s e => q p s e = q' p (ValSpace.subst x u s) (ValExpr.subst x u e)

theorem SubstSpaceAgreement.dof {q q' : FFSOracle} {x : VName} {u : ValExpr}
    {s : ValSpace} (h : SubstSpaceAgreement q q' x u s) :
    ValSpace.dof q s = ValSpace.dof q' (ValSpace.subst x u s) := by
  cases s with
  | empty | real => simp [ValSpace.subst]
  | dsum s t | tprod s t =>
      simp only [ValSpace.subst, ValSpace.dof_dsum, ValSpace.dof_tprod]
      rw [SubstSpaceAgreement.dof h.1, SubstSpaceAgreement.dof h.2]
  | ffs p s e => simpa [ValSpace.subst, ValSpace.dof, ValSpace.shpOf, SubstSpaceAgreement] using h
termination_by sizeOf s

set_option maxHeartbeats 1800000 in
theorem arrayPrimitive_eval_subst (orc : FFSOracleSem)
    (e : ValExpr) (w w' : World) (x : VName) (u : ValExpr)
    (hp : ArrayPrimitive e) (hG : w.types = w'.types)
    (hInf : ∀ a ∈ e :: primitiveOperands e,
      ValExpr.inferSpaceCtx w'.types (ValExpr.subst x u a) =
        ValSpace.subst x u (ValExpr.inferSpaceCtx w.types a))
    (hs : ∀ s ∈ primitiveQuerySpaces w.types e,
      SubstSpaceAgreement (orc w.env w.types w.values)
        (orc w'.env w'.types w'.values) x u s)
    (hi : ∀ a ∈ primitiveOperands e,
      denotValB_semS orc w.env w.types w.values a =
        denotValB_semS orc w'.env w'.types w'.values (ValExpr.subst x u a)) :
    denotValB_semS orc w.env w.types w.values e =
      denotValB_semS orc w'.env w'.types w'.values (ValExpr.subst x u e) := by
  simp only [← hG] at hs hi hInf ⊢
  have hout := SubstSpaceAgreement.dof (hs (ValExpr.inferSpaceCtx w.types e) (by simp [primitiveQuerySpaces]))
  have hin : ∀ s ∈ primitiveInputSpaces w.types e,
      SubstSpaceAgreement (orc w.env w.types w.values)
        (orc w'.env w.types w'.values) x u s := by
    intro s hm
    exact hs s (List.mem_cons_of_mem _ hm)
  cases e <;> simp only [ArrayPrimitive] at hp
  all_goals
    simp [primitiveInputSpaces] at hin
    simp [primitiveOperands] at hi
    simp [primitiveOperands] at hInf
    simp only [ValExpr.subst] at hInf
  case vsum s es =>
    have hd := SubstSpaceAgreement.dof hin
    have hm : (es.take (ValSpace.dof (orc w'.env w.types w'.values)
        (ValSpace.subst x u s))).map (fun a => denotValB_semS orc w.env w.types w.values a) =
        (es.take (ValSpace.dof (orc w'.env w.types w'.values)
        (ValSpace.subst x u s))).map (fun a => denotValB_semS orc w'.env w.types w'.values (ValExpr.subst x u a)) := by
      apply List.map_congr_left
      intro a ha
      exact hi a (List.mem_of_mem_take ha)
    simp only [ValExpr.subst, denotValB_semS.eq_16, hInf.1, hout, hd,
      ValExpr.substList_eq_map, List.length_map, List.map_take, List.attach_map_val,
      List.map_map, Function.comp_def, hm]
    simpa only [← ValExpr.substList_eq_map, hInf.1, hd, hm]
  case rlit => simp [denotValB_semS, ValExpr.subst, ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx]
  case zero => simp only [denotValB_semS, ValExpr.subst, hInf, hout]
  case vadd => simp only [denotValB_semS, ValExpr.subst, hInf, hi, SubstSpaceAgreement.dof hin]
  case delta => simp only [denotValB_semS, ValExpr.subst, hInf, hout, SubstSpaceAgreement.dof hin]
  case idelta => simp only [denotValB_semS, ValExpr.subst, hInf, hout, SubstSpaceAgreement.dof hin]
  case scale => simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi, ValueShape.scale, SubstSpaceAgreement.dof hin]
  case dsumE => simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi, ValueShape.pair,
    SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
  case tprodE => simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi, ValueShape.pair,
    SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
  case vtrans a =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case pinv a =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case inv a =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case svds a =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gpinv a b c =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gsvdS a b c =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gsvdU a b c =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gsvdUI a b c =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gsvdV a b c =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case gsvdVI a b c =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case rrefRep a b =>
    have hd := SubstSpaceAgreement.dof hin
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi]
    cases he : ValExpr.inferSpaceCtx w.types b with
    | tprod s t =>
      simp only [he, SubstSpaceAgreement] at hin
      simp only [ValSpace.subst, ValueShape.tensor]
      rw [SubstSpaceAgreement.dof hin.1, SubstSpaceAgreement.dof hin.2]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [ValSpace.subst, ValueShape.tensor, if_false] <;> first | rw [hd] | rfl
  case ttv s a b =>
    have hc := SubstSpaceAgreement.dof hin.1
    have ha := hin.2.1
    have hb := SubstSpaceAgreement.dof hin.2.2
    have hd := SubstSpaceAgreement.dof ha
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi, ValueShape.ttv, ValueShape.pair, hc, hd, hb]
    cases he : ValExpr.inferSpaceCtx w.types a with
    | tprod u v =>
      simp only [he, SubstSpaceAgreement] at ha
      simp only [ValSpace.subst, ValSpace.dof_tprod]
      rw [SubstSpaceAgreement.dof ha.1, SubstSpaceAgreement.dof ha.2, hb, hc]
      simp only [hInf, he, ValSpace.subst, ValSpace.dof_tprod]
    | empty | real | dsum | ffs =>
      simp only [he, ValSpace.subst] at hd
      simp only [hInf, he, ValSpace.subst, hd, hb, hc]
  case mtm i j s t a b =>
    have hc := SubstSpaceAgreement.dof hin.1
    have ha := hin.2.1
    have hb := hin.2.2
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi, ValueShape.mtm, ValueShape.matrices, hc]
    cases he : ValExpr.inferSpaceCtx w.types a <;>
      cases hf : ValExpr.inferSpaceCtx w.types b <;>
      simp only [hInf, he, hf, ValSpace.subst, ValueShape.tensor, false_and, and_false, if_false]
    all_goals try rfl
    simp only [he, SubstSpaceAgreement] at ha
    simp only [hf, SubstSpaceAgreement] at hb
    rw [SubstSpaceAgreement.dof ha.1, SubstSpaceAgreement.dof ha.2, SubstSpaceAgreement.dof hb.1, SubstSpaceAgreement.dof hb.2, hc]
  case vkrn a b =>
    have ha := hin.1
    have hb := hin.2
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi, ValueShape.matrices]
    cases he : ValExpr.inferSpaceCtx w.types a <;>
      cases hf : ValExpr.inferSpaceCtx w.types b <;>
      simp only [hInf, he, hf, ValSpace.subst, ValueShape.tensor, false_and, and_false, if_false]
    all_goals try rfl
    simp only [he, SubstSpaceAgreement] at ha
    simp only [hf, SubstSpaceAgreement] at hb
    rw [SubstSpaceAgreement.dof ha.1, SubstSpaceAgreement.dof ha.2, SubstSpaceAgreement.dof hb.1, SubstSpaceAgreement.dof hb.2]
  case vblk a b =>
    have ha := hin.1
    have hb := hin.2
    simp only [denotValB_semS, ValExpr.subst, hInf, hout, hi, ValueShape.matrices]
    cases he : ValExpr.inferSpaceCtx w.types a <;>
      cases hf : ValExpr.inferSpaceCtx w.types b <;>
      simp only [hInf, he, hf, ValSpace.subst, ValueShape.tensor, false_and, and_false, if_false]
    all_goals try rfl
    simp only [he, SubstSpaceAgreement] at ha
    simp only [hf, SubstSpaceAgreement] at hb
    rw [SubstSpaceAgreement.dof ha.1, SubstSpaceAgreement.dof ha.2, SubstSpaceAgreement.dof hb.1, SubstSpaceAgreement.dof hb.2]

end GLang.PaperValueDomains
