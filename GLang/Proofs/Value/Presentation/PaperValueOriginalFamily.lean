import GLang.Proofs.Value.Typing.ValueResultAnnotations
import GLang.Proofs.Value.Presentation.PaperValueRawFamilyBinders
import GLang.Proofs.Value.Presentation.PaperValueApplicationSubstitution
import GLang.Proofs.Value.Presentation.PaperValueRawReshapeCoherence
import GLang.Proofs.Value.Presentation.PaperValueMatchedClosure
import GLang.Proofs.Value.Presentation.PaperValueRelatedQueries
import GLang.Proofs.Value.Presentation.PaperValueTypedCorrespondence
import GLang.Proofs.Value.Presentation.PaperValueDependentReshape

/-! Full dependent correspondence for the original value judgments, using
pairwise related families and syntax-local declaration coherence. -/
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace GLang.PaperValueDomains
open ValueDependency

/-- Simultaneous value and result-type induction conclusions. -/
def OriginalRawRelatedResult (e : ValExpr) (t : ValTy) (ρ ρ' : ValEnvSem) : Prop :=
  PartialRel (RuntimeRelated directOracle t ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (denotValB_semS directOracle ρ [] [] e)
    (denotValB_semS directOracle ρ' [] [] e) ∧
  RawTypeCoherent directOracle t ⟨ρ, [], []⟩ ⟨ρ', [], []⟩

private theorem original_numeric_result {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e) (ρ ρ' : ValEnvSem)
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      SpaceOracleAgreement (directOracle ρ [] []) (directOracle ρ' [] []) q)
    (hi : ∀ a ∈ primitiveOperands e, ∃ t : ValSpace,
      Nonempty (ValHasType ε a (.space t)) ∧ OriginalRawRelatedResult a (.space t) ρ ρ') :
    OriginalRawRelatedResult e (.space s) ρ ρ' := by
  have hei : ∀ a ∈ primitiveOperands e,
      denotValB_semS directOracle ρ [] [] a = denotValB_semS directOracle ρ' [] [] a := by
    intro a hm; obtain ⟨t, _, hr⟩ := hi a hm
    exact base_results_eq hr.1
  have hti : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      SpaceOracleAgreement (directOracle ρ [] []) (directOracle ρ' [] []) t := by
    intro a hm t hat
    obtain ⟨t', ⟨hat'⟩, hr⟩ := hi a hm
    have hEq := hat'.unique hat
    cases hEq
    exact hr.2
  exact ⟨original_numeric_step ht hp ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ rfl
      (original_primitive_related_queries ht hp _ _ rfl ha hti hei)
      (fun a hm => by obtain ⟨t, _, hr⟩ := hi a hm; exact ⟨t, hr.1⟩),
    original_primitive_related_output ht hp _ _ rfl ha hti hei⟩

mutual
 theorem originalSpace_family {ε : ValCtx} {s : ValSpace} (h : ValSValid ε s)
    {I : Type} (ρs : I → ValEnvSem)
    (hctx : ∀ i j, RawMatchedContextRelated directOracle ε (ρs i) (ρs j) (spaceAnnotations s))
    (i j : I) : SpaceOracleAgreement (directOracle (ρs i) [] []) (directOracle (ρs j) [] []) s :=
  let ρ := ρs i
  let ρ' := ρs j
  match h with
  | .real => by trivial
  | .empty => by trivial
  | .dsum h0 h1 => by
    exact ⟨originalSpace_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j,
      originalSpace_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j⟩
  | .tprod h0 h1 => by
    exact ⟨originalSpace_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j,
      originalSpace_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j⟩
  | .ffs h0 h1 he => by
    exact original_ffs_oracle_step ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ _ _ _ _ rfl
      (originalSpace_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j)
      (originalSpace_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j)
      (originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j).1
 termination_by structural h

 theorem originalType_family {ε : ValCtx} {t : ValTy} {k : ValKind} (h : ValTValid ε t k)
    {I : Type} (ρs : I → ValEnvSem)
    (hctx : ∀ i j, RawMatchedContextRelated directOracle ε (ρs i) (ρs j) (typeAnnotations t))
    (i j : I) : RawTypeCoherent directOracle t ⟨ρs i, [], []⟩ ⟨ρs j, [], []⟩ :=
  match h with
  | .space hs => originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
  | @ValTValid.piTy ε d c k0 k1 L hd hb => by
    obtain ⟨hvalid⟩ := (hctx i j).valid
    let pick : Bool → I := fun b => if b then j else i
    exact raw_family_pi_step ε d c L hd (validType_lc hvalid hd)
      (fun x hx {J} ρ hc p q => originalType_family (hb x hx) ρ hc p q)
      (fun b => ρs (pick b)) (fun p q => hctx (pick p) (pick q))
      (fun p q => originalType_family hd ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) (pick p) (pick q))
 termination_by structural h

 theorem originalExpr_family {ε : ValCtx} {e : ValExpr} {t : ValTy} (h : ValHasType ε e t)
    {I : Type} (ρs : I → ValEnvSem)
    (hctx : ∀ i j, RawMatchedContextRelated directOracle ε (ρs i) (ρs j) (exprAnnotations e))
    (i j : I) : OriginalRawRelatedResult e t (ρs i) (ρs j) :=
  let ρ := ρs i
  let ρ' := ρs j
  match h with
  | .var hl => by
    exact ⟨eval_var_related directOracle _ ρ ρ' (hctx i j).values _ _ hl,
      (hctx i j).coherent _ _ List.mem_cons_self hl⟩
  | .zero hs => by
    have cs0 := originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.zero hs) (by trivial) ρ ρ'
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs0
    · simp [primitiveOperands]
  | @ValHasType.rlit ε r => by
    apply original_numeric_result (ε := ε) (.rlit r) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · simp [primitiveOperands]
  | .scale h0 h1 => by
    have r0 := originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.scale h0 h1) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .vadd h0 h1 hs => by
    have r0 := originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have cs := originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.vadd h0 h1 hs) (by trivial) ρ ρ'
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .dsumE h0 h1 => by
    have r0 := originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.dsumE h0 h1) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .tprodE h0 h1 => by
    have r0 := originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.tprodE h0 h1) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .delta hs => by
    have cs0 := originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.delta hs) (by trivial) ρ ρ'
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs0
    · simp [primitiveOperands]
  | .idelta hs => by
    have cs0 := originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.idelta hs) (by trivial) ρ ρ'
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs0
    · simp [primitiveOperands]
  | .ttv_space hs h0 h1 => by
    have cs0 := originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r0 := originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.ttv_space hs h0 h1) (by trivial) ρ ρ'
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs0
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .ttv_real hs h0 h1 hn => by
    have cs0 := originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r0 := originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.ttv_real hs h0 h1 hn) (by trivial) ρ ρ'
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs0
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .mtm hs ht h0 h1 => by
    have cs0 := originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have cs1 := originalSpace_family ht ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r0 := originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.mtm hs ht h0 h1) (by trivial) ρ ρ'
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact ⟨cs0, cs1⟩
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .vkrn h0 h1 => by
    have r0 := originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.vkrn h0 h1) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .vblk h0 h1 => by
    have r0 := originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.vblk h0 h1) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .vtrans he => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.vtrans he) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .gsvdS he ha hb => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.gsvdS he ha hb) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .gsvdU he ha hb => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.gsvdU he ha hb) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .gsvdUI he ha hb => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.gsvdUI he ha hb) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .gsvdV he ha hb => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.gsvdV he ha hb) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .gsvdVI he ha hb => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.gsvdVI he ha hb) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .gpinv he ha hb => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.gpinv he ha hb) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .pinv_tensor he => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.pinv_tensor he) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .inv_tensor he => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.inv_tensor he) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .svds he => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.svds he) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .pinv_raw he hn => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.pinv_raw he hn) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .inv_raw he hn => by
    have r0 := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.inv_raw he hn) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .rrefRep h0 h1 => by
    have r0 := originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.rrefRep h0 h1) (by trivial) ρ ρ'
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .vsum hs hb ht hdet => by
    have cs := originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply original_numeric_result (.vsum hs hb ht hdet) (by trivial) ρ ρ'
    · simpa only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
        forall_false, forall_const, and_true] using cs
    · intro a ha
      exact ⟨_, ⟨hb a ha⟩, originalExpr_family (hb a ha) ρs (fun u v => (hctx u v).mono (by
        intro q hq
        simp only [exprAnnotations, List.mem_append]
        exact Or.inr (listAnnotations_mem ha hq))) i j⟩
  | @ValHasType.vlam ε d c k0 k1 body L ht hb => by
    have htcoh := fun u v => originalType_family ht ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) u v
    have hd : ValTValid ε d k0 := by cases ht with | piTy _ hd _ => exact hd
    obtain ⟨hvalid⟩ := (hctx i j).valid
    let pick : Bool → I := fun b => if b then j else i
    exact ⟨raw_family_lambda_step ε d c body L hd (validType_lc hvalid hd)
      (fun x hx {J} ρ hc p q => (originalExpr_family (hb x hx) ρ hc p q).1)
      (fun b => ρs (pick b)) (fun p q => hctx (pick p) (pick q))
      (fun p q => (htcoh (pick p) (pick q)).1), htcoh i j⟩
  | .appV hf ha hout ht => by
    have rf := fun u v => originalExpr_family hf ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) u v
    have ra := fun u v => originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) u v
    have rt := originalType_family ht ρs (fun u v => (hctx u v).mono ((ValHasType.appV hf ha hout ht).resultAnnotations (hctx u v).valid.some)) i j
    obtain ⟨hvalid⟩ := (hctx i j).valid
    have hbeta := ValTy.applyCodomain_eq_instantiate
      (validType_lc hvalid (hf.regular hvalid).2) (validExpr_lc hvalid ha).1
    cases hout
    rw [hbeta] at rt ⊢
    exact ⟨original_application_family hf ha (hf.regular hvalid).2 (validContext_lc hvalid) hvalid ρs
      (fun u v => (rf u v).1) (fun u v => (ra u v).1) (fun u v => (rf u v).2) i j, rt⟩
  | .reshap he hs ht => by
    have re := originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have rs := fun u v => originalType_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) u v
    have rt := fun u v => originalType_family ht ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) u v
    exact ⟨eval_reshape_related_of_rawFamily _ _ directOracle (fun u => (⟨ρs u, [], []⟩ : World))
      rs rt i j _ _ re.1, rt i j⟩
 termination_by structural h
end

/-- Full original type coherence derived from formation-valid contexts and
pairwise runtime-related declared values. No declaration-coherence premise. -/
theorem originalType_coherent_family {ε : ValCtx} {t : ValTy} {k : ValKind}
    (h : ValTValid ε t k) (hvalid : ValCtxValid ε) {I : Type}
    (ρ : I → ValEnvSem) (hvalues : ∀ i j, EnvironmentsRelated directOracle ε (ρ i) (ρ j)) :
    ∀ i j, RawTypeCoherent directOracle t ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩ :=
  rawTypeCoherent_of_matched_family_step directOracle ε ρ hvalid hvalues
    (fun t k ht hc i j => originalType_family ht ρ hc i j) t k h

/-- Context formation and the runtime entry relation supply every syntax-local
coherence input internally. -/
theorem rawMatchedContext_of_valid_family (ε : ValCtx) (hvalid : ValCtxValid ε)
    {I : Type} (ρ : I → ValEnvSem)
    (hvalues : ∀ i j, EnvironmentsRelated directOracle ε (ρ i) (ρ j))
    (xs : List (VName × ValTy)) :
    ∀ i j, RawMatchedContextRelated directOracle ε (ρ i) (ρ j) xs := by
  intro i j
  refine ⟨⟨hvalid⟩, hvalues i j, ?_⟩
  intro x a _ hl
  exact originalType_coherent_family (hvalid x a hl).2 hvalid ρ hvalues i j

/-- Complete mutual conclusion for every original value typing derivation,
including dependent higher-order functions, application, reshape, FFS, and errors. -/
theorem originalExpr_result_family {ε : ValCtx} {e : ValExpr} {t : ValTy}
    (h : ValHasType ε e t) (hvalid : ValCtxValid ε) {I : Type}
    (ρ : I → ValEnvSem) (hvalues : ∀ i j, EnvironmentsRelated directOracle ε (ρ i) (ρ j)) :
    ∀ i j, OriginalRawRelatedResult e t (ρ i) (ρ j) :=
  originalExpr_family h ρ (rawMatchedContext_of_valid_family ε hvalid ρ hvalues _)

/-- Error-sensitive denotation respects every pairwise supported family of
originally typed environments. This is the full value-language fundamental theorem. -/
theorem originalExpr_related_family {ε : ValCtx} {e : ValExpr} {t : ValTy}
    (h : ValHasType ε e t) (hvalid : ValCtxValid ε) {I : Type}
    (ρ : I → ValEnvSem) (hvalues : ∀ i j, EnvironmentsRelated directOracle ε (ρ i) (ρ j)) :
    ∀ i j, PartialRel (RuntimeRelated directOracle t ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩)
      (denotValB_semS directOracle (ρ i) [] [] e)
      (denotValB_semS directOracle (ρ j) [] [] e) :=
  fun i j => (originalExpr_result_family h hvalid ρ hvalues i j).1

/-- Every original valid space has identical current-oracle observations
across a supported family; no arbitrary-query oracle assumption is required. -/
theorem originalSpace_coherent_family {ε : ValCtx} {s : ValSpace}
    (h : ValSValid ε s) (hvalid : ValCtxValid ε) {I : Type}
    (ρ : I → ValEnvSem) (hvalues : ∀ i j, EnvironmentsRelated directOracle ε (ρ i) (ρ j)) :
    ∀ i j, SpaceOracleAgreement (directOracle (ρ i) [] []) (directOracle (ρ j) [] []) s :=
  originalSpace_family h ρ (rawMatchedContext_of_valid_family ε hvalid ρ hvalues _)

end GLang.PaperValueDomains
