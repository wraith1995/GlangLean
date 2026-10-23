import GLang.Proofs.Value.Runtime.RuntimeValueEmbedding
import GLang.Proofs.Value.Typing.ValueResultAnnotations
import GLang.Proofs.Value.Partial.PartialValueApplication
import GLang.Proofs.Value.Partial.PartialValueReshape
import GLang.Proofs.Value.Partial.PartialValueRelatedQueries
import GLang.Proofs.Value.Partial.PartialValuePrimitiveSized
import GLang.Proofs.Value.Presentation.PaperValueMatchedClosure

/-! Full dependent correspondence for the original value judgments, using
pairwise related families and syntax-local declaration coherence. -/
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace GLang.PartialValueDomains
open PaperValueDomains
open ValueDependency

private theorem partial_base_results_eq {s : ValSpace} {w w' : World}
    {r r' : Except DimError ValValSem}
    (h : PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle (.space s) w w') r r') : r = r' := by
  cases r <;> cases r' <;> simp only [PartialRel] at h
  · rename_i e e'; cases e; cases e'; rfl
  · rename_i v v'
    cases v <;> cases v' <;> try exact False.elim h
    simp only [WorldRuntimeRelated,PartialRuntimeRelated] at h
    cases hT : PartialWorldType PartialDirectOracle.oracle w (.space s) <;>
      cases hU : PartialWorldType PartialDirectOracle.oracle w' (.space s) <;>
      simp only [hT,hU,PartialRelated] at h
    exact congrArg (fun a => Except.ok (ValValSem.array a)) h.1

private theorem partial_ffs_oracle_step (w w' : World) (p : ValFFSProp)
    (s t : ValSpace) (e : ValExpr)
    (hf : ValueQueryDependencies.Finite (.space w.types (.ffs p (.tprod s t) e)))
    (hf' : ValueQueryDependencies.Finite (.space w'.types (.ffs p (.tprod s t) e)))
    (hs : PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
      (PartialDirectOracle.oracle w'.env w'.types w'.values) s)
    (ht : PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
      (PartialDirectOracle.oracle w'.env w'.types w'.values) t)
    (he : PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle (.space (.tprod s t)) w w')
      (denotValB_partial PartialDirectOracle.oracle w.env w.types w.values e)
      (denotValB_partial PartialDirectOracle.oracle w'.env w'.types w'.values e)) :
    PartialSpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
      (PartialDirectOracle.oracle w'.env w'.types w'.values) (.ffs p (.tprod s t) e) := by
  have hshape := (PartialSpaceAgreement.observations _ _ (.tprod s t) ⟨hs,ht⟩).1
  have heq := partial_base_results_eq he
  change PartialDirectOracle.oracle _ _ _ _ _ _ = PartialDirectOracle.oracle _ _ _ _ _ _
  rw [PartialDirectLocality.oracle_eq _ _ _ _ _ _ hf,PartialDirectLocality.oracle_eq _ _ _ _ _ _ hf',hshape,heq]

/-- Simultaneous value and result-type induction conclusions. -/
def partial_OriginalRawRelatedResult (e : ValExpr) (t : ValTy) (ρ ρ' : ValEnvSem) : Prop :=
  PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle t ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (denotValB_partial PartialDirectOracle.oracle ρ [] [] e)
    (denotValB_partial PartialDirectOracle.oracle ρ' [] [] e) ∧
  PartialRawTypeCoherent PartialDirectOracle.oracle t ⟨ρ, [], []⟩ ⟨ρ', [], []⟩

private theorem partial_original_numeric_result {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e) (ρ ρ' : ValEnvSem)
    (hv : ValCtxValid ε)
    (ha : ∀ q ∈ primitiveAnnotationSpaces e,
      PartialSpaceAgreement (PartialDirectOracle.oracle ρ [] []) (PartialDirectOracle.oracle ρ' [] []) q)
    (hi : ∀ a ∈ primitiveOperands e, ∃ t : ValSpace,
      Nonempty (ValHasType ε a (.space t)) ∧ partial_OriginalRawRelatedResult a (.space t) ρ ρ') :
    partial_OriginalRawRelatedResult e (.space s) ρ ρ' := by
  have hei : ∀ a ∈ primitiveOperands e,
      denotValB_partial PartialDirectOracle.oracle ρ [] [] a = denotValB_partial PartialDirectOracle.oracle ρ' [] [] a := by
    intro a hm; obtain ⟨t, _, hr⟩ := hi a hm
    exact partial_base_results_eq hr.1
  have hti : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      PartialSpaceAgreement (PartialDirectOracle.oracle ρ [] []) (PartialDirectOracle.oracle ρ' [] []) t := by
    intro a hm t hat
    obtain ⟨t', ⟨hat'⟩, hr⟩ := hi a hm
    have hEq := hat'.unique hat
    cases hEq
    exact hr.2
  have hf := (RuntimeValue.validExpr_queryFinite hv.runtime ht.runtime).1
  refine ⟨?_,partial_original_primitive_related_output ht hp _ _ hf hf ha hti hei⟩
  apply partial_arrayPrimitive_related_of_eval_eq PartialDirectOracle.oracle ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ e s hp
  · rw [ValExpr.inferSpaceCtx_eq_of_typed ht]
  · rw [ValExpr.inferSpaceCtx_eq_of_typed ht]
  exact partial_arrayPrimitive_eval_congr_local PartialDirectOracle.oracle e ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ hp rfl
    (partial_original_primitive_related_queries ht hp _ _ hf hf ha hti hei) hei

mutual
 theorem partial_originalSpace_family {ε : ValCtx} {s : ValSpace} (h : ValSValid ε s)
    {I : Type} (ρs : I → ValEnvSem)
    (hctx : ∀ i j, RawMatchedContextRelated PartialDirectOracle.oracle ε (ρs i) (ρs j) (spaceAnnotations s))
    (i j : I) : PartialSpaceAgreement (PartialDirectOracle.oracle (ρs i) [] []) (PartialDirectOracle.oracle (ρs j) [] []) s :=
  let ρ := ρs i
  let ρ' := ρs j
  match h with
  | .real => by trivial
  | .empty => by trivial
  | .dsum h0 h1 => by
    exact ⟨partial_originalSpace_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j,
      partial_originalSpace_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j⟩
  | .tprod h0 h1 => by
    exact ⟨partial_originalSpace_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j,
      partial_originalSpace_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j⟩
  | @ValSValid.ffs ε p s0 s1 e h0 h1 he => by
    have hf := RuntimeValue.validSpace_queryFinite (hctx i j).valid.some.runtime (GLang.ValSValid.ffs (p := p) h0 h1 he).runtime
    exact partial_ffs_oracle_step ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ _ _ _ _ hf hf
      (partial_originalSpace_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j)
      (partial_originalSpace_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j)
      (partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j).1
 termination_by structural h

 theorem partial_originalType_family {ε : ValCtx} {t : ValTy} {k : ValKind} (h : ValTValid ε t k)
    {I : Type} (ρs : I → ValEnvSem)
    (hctx : ∀ i j, RawMatchedContextRelated PartialDirectOracle.oracle ε (ρs i) (ρs j) (typeAnnotations t))
    (i j : I) : PartialRawTypeCoherent PartialDirectOracle.oracle t ⟨ρs i, [], []⟩ ⟨ρs j, [], []⟩ :=
  match h with
  | .space hs => partial_originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
  | @ValTValid.piTy ε d c k0 k1 L hd hb => by
    obtain ⟨hvalid⟩ := (hctx i j).valid
    let pick : Bool → I := fun b => if b then j else i
    exact partial_family_pi_step ε d c L hd (validType_lc hvalid hd)
      (fun x hx {J} ρ hc p q => partial_originalType_family (hb x hx) ρ hc p q)
      (fun b => ρs (pick b)) (fun p q => hctx (pick p) (pick q))
      (fun p q => partial_originalType_family hd ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) (pick p) (pick q))
 termination_by structural h

 theorem partial_originalExpr_family {ε : ValCtx} {e : ValExpr} {t : ValTy} (h : ValHasType ε e t)
    {I : Type} (ρs : I → ValEnvSem)
    (hctx : ∀ i j, RawMatchedContextRelated PartialDirectOracle.oracle ε (ρs i) (ρs j) (exprAnnotations e))
    (i j : I) : partial_OriginalRawRelatedResult e t (ρs i) (ρs j) :=
  let ρ := ρs i
  let ρ' := ρs j
  match h with
  | .var hl => by
    exact ⟨by simpa only [denotValB_partial,PartialRel] using (hctx i j).values _ _ hl,
      (hctx i j).coherent _ _ List.mem_cons_self hl⟩
  | .zero hs => by
    have cs0 := partial_originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.zero hs) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs0
    · simp [primitiveOperands]
  | @ValHasType.rlit ε r => by
    apply partial_original_numeric_result (ε := ε) (.rlit r) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · simp [primitiveOperands]
  | .scale h0 h1 => by
    have r0 := partial_originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.scale h0 h1) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .vadd h0 h1 hs => by
    have r0 := partial_originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have cs := partial_originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.vadd h0 h1 hs) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .dsumE h0 h1 => by
    have r0 := partial_originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.dsumE h0 h1) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .tprodE h0 h1 => by
    have r0 := partial_originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.tprodE h0 h1) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .delta hs => by
    have cs0 := partial_originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.delta hs) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs0
    · simp [primitiveOperands]
  | .idelta hs => by
    have cs0 := partial_originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.idelta hs) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs0
    · simp [primitiveOperands]
  | .ttv_space hs h0 h1 => by
    have cs0 := partial_originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r0 := partial_originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.ttv_space hs h0 h1) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs0
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .ttv_real hs h0 h1 hn => by
    have cs0 := partial_originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r0 := partial_originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.ttv_real hs h0 h1 hn) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact cs0
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .mtm hs ht h0 h1 => by
    have cs0 := partial_originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have cs1 := partial_originalSpace_family ht ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r0 := partial_originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.mtm hs ht h0 h1) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      exact ⟨cs0, cs1⟩
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .vkrn h0 h1 => by
    have r0 := partial_originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.vkrn h0 h1) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .vblk h0 h1 => by
    have r0 := partial_originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.vblk h0 h1) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .vtrans he => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.vtrans he) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .gsvdS he ha hb => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := partial_originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.gsvdS he ha hb) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .gsvdU he ha hb => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := partial_originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.gsvdU he ha hb) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .gsvdUI he ha hb => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := partial_originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.gsvdUI he ha hb) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .gsvdV he ha hb => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := partial_originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.gsvdV he ha hb) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .gsvdVI he ha hb => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := partial_originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.gsvdVI he ha hb) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .gpinv he ha hb => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r2 := partial_originalExpr_family hb ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.gpinv he ha hb) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, ⟨he⟩, r0⟩
      · exact ⟨_, ⟨ha⟩, r1⟩
      · exact ⟨_, ⟨hb⟩, r2⟩
  | .pinv_tensor he => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.pinv_tensor he) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .inv_tensor he => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.inv_tensor he) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .svds he => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.svds he) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .pinv_raw he hn => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.pinv_raw he hn) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .inv_raw he hn => by
    have r0 := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.inv_raw he hn) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact ⟨_, ⟨he⟩, r0⟩
  | .rrefRep h0 h1 => by
    have r0 := partial_originalExpr_family h0 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have r1 := partial_originalExpr_family h1 ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.rrefRep h0 h1) (by trivial) ρ ρ' (hctx i j).valid.some
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, ⟨h0⟩, r0⟩
      · exact ⟨_, ⟨h1⟩, r1⟩
  | .vsum hs hb ht hdet => by
    have cs := partial_originalSpace_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    apply partial_original_numeric_result (.vsum hs hb ht hdet) (by trivial) ρ ρ' (hctx i j).valid.some
    · simpa only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
        forall_false, forall_const, and_true] using cs
    · intro a ha
      exact ⟨_, ⟨hb a ha⟩, partial_originalExpr_family (hb a ha) ρs (fun u v => (hctx u v).mono (by
        intro q hq
        simp only [exprAnnotations, List.mem_append]
        exact Or.inr (listAnnotations_mem ha hq))) i j⟩
  | @ValHasType.vlam ε d c k0 k1 body L ht hb => by
    have htcoh := fun u v => partial_originalType_family ht ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) u v
    have hd : ValTValid ε d k0 := by cases ht with | piTy _ hd _ => exact hd
    obtain ⟨hvalid⟩ := (hctx i j).valid
    let pick : Bool → I := fun b => if b then j else i
    exact ⟨partial_family_lambda_step ε d c body L hd (validType_lc hvalid hd)
      (fun x hx {J} ρ hc p q => (partial_originalExpr_family (hb x hx) ρ hc p q).1)
      (fun b => ρs (pick b)) (fun p q => hctx (pick p) (pick q))
      (fun p q => (htcoh (pick p) (pick q)).1), htcoh i j⟩
  | .appV hf ha hout ht => by
    have rf := fun u v => partial_originalExpr_family hf ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) u v
    have ra := fun u v => partial_originalExpr_family ha ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) u v
    have rt := fun u v => partial_originalType_family ht ρs (fun u v => (hctx u v).mono ((ValHasType.appV hf ha hout ht).resultAnnotations (hctx u v).valid.some)) u v
    obtain ⟨hvalid⟩ := (hctx i j).valid
    have hbeta := ValTy.applyCodomain_eq_instantiate
      (validType_lc hvalid (hf.regular hvalid).2) (validExpr_lc hvalid ha).1
    cases hout
    rw [hbeta] at rt ⊢
    exact ⟨partial_original_application_family hf ha (hf.regular hvalid).2 (validContext_lc hvalid) hvalid ρs
      (fun u v => (rf u v).1) (fun u v => (ra u v).1) (fun u v => (rf u v).2)
      (fun u v => rt u v) i j, rt i j⟩
  | .reshap he hs ht => by
    have re := partial_originalExpr_family he ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) i j
    have rs := fun u v => partial_originalType_family hs ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) u v
    have rt := fun u v => partial_originalType_family ht ρs (fun u v => (hctx u v).mono (by intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) u v
    exact ⟨partial_eval_reshape_related_of_rawFamily _ _ PartialDirectOracle.oracle (fun u => (⟨ρs u, [], []⟩ : World))
      rs rt i j _ _ (ValExpr.inferTypeCtx_eq_of_typed he)
      (ValExpr.inferTypeCtx_eq_of_typed he) re.1, rt i j⟩
 termination_by structural h
end

/-- Full original type coherence derived from formation-valid contexts and
pairwise runtime-related declared values. No declaration-coherence premise. -/
theorem partial_originalType_coherent_family {ε : ValCtx} {t : ValTy} {k : ValKind}
    (h : ValTValid ε t k) (hvalid : ValCtxValid ε) {I : Type}
    (ρ : I → ValEnvSem) (hvalues : ∀ i j, PartialEnvironmentsRelated PartialDirectOracle.oracle ε (ρ i) (ρ j)) :
    ∀ i j, PartialRawTypeCoherent PartialDirectOracle.oracle t ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩ :=
  rawTypeCoherent_of_matched_family_step PartialDirectOracle.oracle ε ρ hvalid hvalues
    (fun t k ht hc i j => partial_originalType_family ht ρ hc i j) t k h

/-- Context formation and the runtime entry relation supply every syntax-local
coherence input internally. -/
theorem partial_rawMatchedContext_of_valid_family (ε : ValCtx) (hvalid : ValCtxValid ε)
    {I : Type} (ρ : I → ValEnvSem)
    (hvalues : ∀ i j, PartialEnvironmentsRelated PartialDirectOracle.oracle ε (ρ i) (ρ j))
    (xs : List (VName × ValTy)) :
    ∀ i j, RawMatchedContextRelated PartialDirectOracle.oracle ε (ρ i) (ρ j) xs := by
  intro i j
  refine ⟨⟨hvalid⟩, hvalues i j, ?_⟩
  intro x a _ hl
  exact partial_originalType_coherent_family (hvalid x a hl).2 hvalid ρ hvalues i j

/-- Complete mutual conclusion for every original value typing derivation,
including dependent higher-order functions, application, reshape, FFS, and errors. -/
theorem partial_originalExpr_result_family {ε : ValCtx} {e : ValExpr} {t : ValTy}
    (h : ValHasType ε e t) (hvalid : ValCtxValid ε) {I : Type}
    (ρ : I → ValEnvSem) (hvalues : ∀ i j, PartialEnvironmentsRelated PartialDirectOracle.oracle ε (ρ i) (ρ j)) :
    ∀ i j, partial_OriginalRawRelatedResult e t (ρ i) (ρ j) :=
  partial_originalExpr_family h ρ (partial_rawMatchedContext_of_valid_family ε hvalid ρ hvalues _)

/-- Error-sensitive denotation respects every pairwise supported family of
originally typed environments. This is the full value-language fundamental theorem. -/
theorem partial_originalExpr_related_family {ε : ValCtx} {e : ValExpr} {t : ValTy}
    (h : ValHasType ε e t) (hvalid : ValCtxValid ε) {I : Type}
    (ρ : I → ValEnvSem) (hvalues : ∀ i j, PartialEnvironmentsRelated PartialDirectOracle.oracle ε (ρ i) (ρ j)) :
    ∀ i j, PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle t ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩)
      (denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] e)
      (denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] e) :=
  fun i j => (partial_originalExpr_result_family h hvalid ρ hvalues i j).1

/-- Every original valid space has identical current-oracle observations
across a supported family; no arbitrary-query oracle assumption is required. -/
theorem partial_originalSpace_coherent_family {ε : ValCtx} {s : ValSpace}
    (h : ValSValid ε s) (hvalid : ValCtxValid ε) {I : Type}
    (ρ : I → ValEnvSem) (hvalues : ∀ i j, PartialEnvironmentsRelated PartialDirectOracle.oracle ε (ρ i) (ρ j)) :
    ∀ i j, PartialSpaceAgreement (PartialDirectOracle.oracle (ρ i) [] []) (PartialDirectOracle.oracle (ρ j) [] []) s :=
  partial_originalSpace_family h ρ (partial_rawMatchedContext_of_valid_family ε hvalid ρ hvalues _)

end GLang.PartialValueDomains
