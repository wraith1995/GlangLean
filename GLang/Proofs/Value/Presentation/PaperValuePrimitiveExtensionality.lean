import GLang.Proofs.Value.Presentation.PaperValueExtensionality

/-! Compositional relational step for every finite-array primitive of the live
value evaluator. -/
namespace GLang.PaperValueDomains

/-- Immediate numerical operands; type annotations and oracle witnesses are
handled separately by oracle compatibility. -/
def primitiveOperands : ValExpr → List ValExpr
  | .scale a b | .vadd _ a b | .dsumE a b | .tprodE a b
  | .ttv _ a b | .mtm _ _ _ _ a b | .vkrn a b | .vblk a b | .rrefRep a b => [a,b]
  | .vtrans a | .pinv a | .inv a | .svds a => [a]
  | .gpinv a b c | .gsvdS a b c | .gsvdU a b c | .gsvdUI a b c
  | .gsvdV a b c | .gsvdVI a b c => [a,b,c]
  | .vsum _ es => es
  | _ => []

/-- Exactly the array-building numerical clauses, excluding variables,
application, lambdas, and type-changing reshape. -/
def ArrayPrimitive : ValExpr → Prop
  | .var _ _ | .bvar _ | .appV _ _ | .vlam _ _ _ | .reshap _ _ _ => False
  | _ => True

/-- One full evaluator step, including every shape guard and numerical routine,
is invariant once its immediate operand results and current oracle observations
are invariant. No assumptions on latent callback identity are required. -/
theorem arrayPrimitive_eval_congr (orc : FFSOracleSem)
    (e : ValExpr) (w w' : World)
    (hp : ArrayPrimitive e) (hG : w.types = w'.types)
    (hq : orc w.env w.types w.values = orc w'.env w'.types w'.values)
    (hi : ∀ a ∈ primitiveOperands e,
      denotValB_semS orc w.env w.types w.values a =
        denotValB_semS orc w'.env w'.types w'.values a) :
    denotValB_semS orc w.env w.types w.values e =
      denotValB_semS orc w'.env w'.types w'.values e := by
  simp only [hG] at hq hi ⊢
  cases e <;> simp only [ArrayPrimitive] at hp
  case vsum s es =>
    simp only [primitiveOperands] at hi
    have hm : ((es.take (ValSpace.dof (orc w'.env w'.types w'.values) s)).attach.map
        (fun a => denotValB_semS orc w.env w'.types w.values a.1)) =
        ((es.take (ValSpace.dof (orc w'.env w'.types w'.values) s)).attach.map
        (fun a => denotValB_semS orc w'.env w'.types w'.values a.1)) := by
      apply List.map_congr_left
      intro a ha
      exact hi a (List.mem_of_mem_take a.property)
    simp only [denotValB_semS.eq_16]
    rw [hq]
    simp only [hm]
  all_goals
    simp only [primitiveOperands, List.mem_cons,
      forall_eq_or_imp] at hi
    simp only [denotValB_semS, hi]
    try rw [hq]

/-- At array types the error-sensitive runtime relation entails equality of
whole evaluator results, so it supplies the operand hypotheses above. -/
theorem base_results_eq {orc : FFSOracleSem} {s : ValSpace} {w w' : World}
    {r r' : Except DimError ValValSem}
    (h : PartialRel (RuntimeRelated orc (.space s) w w') r r') : r = r' := by
  cases r with
  | error e => cases r' <;> simp_all [PartialRel]
  | ok v =>
    cases r' with
    | error e => exact h.elim
    | ok v' =>
      cases v <;> cases v' <;> simp only [PartialRel, RuntimeRelated] at h
      exact congrArg (fun a => Except.ok (ValValSem.array a)) h.1

/-- Relational operand induction hypotheses supply the numerical congruence
step, without requiring equality of function-valued environment entries. -/
theorem arrayPrimitive_eval_congr_of_related (orc : FFSOracleSem)
    (e : ValExpr) (w w' : World)
    (hp : ArrayPrimitive e) (hG : w.types = w'.types)
    (hq : orc w.env w.types w.values = orc w'.env w'.types w'.values)
    (hi : ∀ a ∈ primitiveOperands e, ∃ s,
      PartialRel (RuntimeRelated orc (.space s) w w')
        (denotValB_semS orc w.env w.types w.values a)
        (denotValB_semS orc w'.env w'.types w'.values a)) :
    denotValB_semS orc w.env w.types w.values e =
      denotValB_semS orc w'.env w'.types w'.values e :=
  arrayPrimitive_eval_congr orc e w w' hp hG hq fun a ha =>
    let ⟨_, h⟩ := hi a ha
    base_results_eq h

end GLang.PaperValueDomains
