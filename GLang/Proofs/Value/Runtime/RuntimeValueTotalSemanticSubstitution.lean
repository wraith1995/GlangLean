import GLang.Proofs.Value.Runtime.RuntimeValueTotalSubstitutionStep
import GLang.Proofs.Value.Runtime.RuntimeValueTotalNamedSubstContext
import GLang.Proofs.Value.Presentation.PaperValueRawReshape
import GLang.Proofs.Value.Typing.ValueRealizeLc

namespace GLang.RuntimeValue.TotalSubstitution
open PaperValueDomains ValSoundOfDenot

private theorem updates_comm (ρ : ValEnvSem) (x y : VName) (v z : ValValSem)
    (h : y ≠ x) : (ρ.update y z).update x v = (ρ.update x v).update y z := by
  funext a
  by_cases hx : a = x <;> by_cases hy : a = y <;> simp_all [ValEnvSem.update]

private theorem fresh_substTy {x y : VName} {u : ValExpr} {τ : ValTy}
    (hτ : y ∉ ValTy.fv τ) (hu : y ∉ ValExpr.fv u) : y ∉ ValTy.fv (ValTy.subst x u τ) := by
  intro h
  rcases Finset.mem_union.mp (ValTy.fv_subst_mem h) with h | h
  · exact hτ h
  · exact hu h

private theorem fresh_substExpr {x y : VName} {u e : ValExpr}
    (he : y ∉ ValExpr.fv e) (hu : y ∉ ValExpr.fv u) : y ∉ ValExpr.fv (ValExpr.subst x u e) := by
  intro h
  rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h | h
  · exact he h
  · exact hu h

private structure FreshBinder (ε : ValCtx) (x : VName) (u : ValExpr)
    (L : Finset VName) (d c : ValTy) (body : ValExpr) where
  y : VName
  outside : y ∉ L
  different : y ≠ x
  key : y ∉ ε
  support : y ∉ ε.fvSupport
  arg : y ∉ ValExpr.fv u
  domain : y ∉ ValTy.fv d
  codomain : y ∉ ValTy.fv c
  body : y ∉ ValExpr.fv body

private noncomputable def freshBinder (ε : ValCtx) (x : VName) (u : ValExpr)
    (L : Finset VName) (d c : ValTy) (body : ValExpr) : FreshBinder ε x u L d c body := by
  let avoid := L ∪ ε.keys ∪ ε.fvSupport ∪ {x} ∪ ValExpr.fv u ∪ ValTy.fv d ∪ ValTy.fv c ∪ ValExpr.fv body
  let y := freshFor avoid
  have hy := freshFor_notMem avoid
  change y ∉ avoid at hy
  simp only [avoid, Finset.mem_union, Finset.mem_singleton, not_or] at hy
  rcases hy with ⟨⟨⟨⟨⟨⟨⟨hL,hK⟩,hS⟩,hX⟩,hU⟩,hD⟩,hC⟩,hB⟩
  exact ⟨y,hL,hX,(fun hm => hK (Finmap.mem_keys.mpr hm)),hS,hU,hD,hC,hB⟩

private theorem typeBinderStep {ε : ValCtx} {x : VName} {u : ValExpr} {τx : ValTy}
    {ρ : ValEnvSem} {v : ValValSem} {d c : ValTy} {kd : ValKind}
    (L : Finset VName) (hd : ValTValid ε d kd) (hctx : NamedSubstCtx x u ε τx ρ v)
    (ihd : TypeSubstitutionResult ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩ x u d)
    (ihc : ∀ y, y ∉ L → ∀ ρ' v', NamedSubstCtx x u (Finmap.insert y d ε) τx ρ' v' →
      TypeSubstitutionResult ⟨ρ'.update x v',[],[]⟩ ⟨ρ',[],[]⟩ x u (ValTy.openVar y d c)) :
    TypeSubstitutionResult ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩ x u (.piTy d c) := by
  let f := freshBinder ε x u L d c (.rlit 0)
  have hdlc := originalType_lc hd hctx.lc
  refine ⟨?_, by intro s hs; cases hs⟩
  apply rawPresentation_pi_open (ρ.update x v) ρ f.y d c (ValTy.subst x u d) (ValTy.subst x u c)
    ihd.1 hdlc (lc_subst_joint.2.1 hdlc x u hctx.sd.lc)
    f.domain (fresh_substTy f.domain f.arg) f.codomain (fresh_substTy f.codomain f.arg)
  intro z
  have hc := ihc f.y f.outside (ρ.update f.y z) v
    (hctx.extend f.y d z hd f.different f.key f.support f.arg f.domain hdlc ihd.1 ihd.2)
  simpa only [ValTy.subst_openVar f.different hctx.sd.lc, updates_comm ρ x f.y v z f.different]
    using hc.1

private theorem lambdaBinderStep {ε : ValCtx} {x : VName} {u : ValExpr} {τx : ValTy}
    {ρ : ValEnvSem} {v : ValValSem} {d c : ValTy} {body : ValExpr} {kd : ValKind}
    (L : Finset VName) (hd : ValTValid ε d kd) (hctx : NamedSubstCtx x u ε τx ρ v)
    (ihd : TypeSubstitutionResult ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩ x u d)
    (ihb : ∀ y, y ∉ L → ∀ ρ' v', NamedSubstCtx x u (Finmap.insert y d ε) τx ρ' v' →
      ExprSubstitutionResult ⟨ρ'.update x v',[],[]⟩ ⟨ρ',[],[]⟩ x u
        (ValExpr.openVar y d body) (ValTy.openVar y d c)) :
    denotValB_semS directOracle (ρ.update x v) [] [] (.vlam d c body) =
      denotValB_semS directOracle ρ [] [] (ValExpr.subst x u (.vlam d c body)) := by
  let f := freshBinder ε x u L d c body
  have hdlc := originalType_lc hd hctx.lc
  apply presentation_eval_vlam_open (ρ.update x v) ρ f.y d c (ValTy.subst x u d)
    (ValTy.subst x u c) body (ValExpr.subst x u body)
    (ValTy.SameShape_subst x u d).symm (ihd.1.toPresentation directOracle _ _ _ _)
    hdlc (lc_subst_joint.2.1 hdlc x u hctx.sd.lc)
    f.domain (fresh_substTy f.domain f.arg) f.body (fresh_substExpr f.body f.arg)
  intro z
  have hb := ihb f.y f.outside (ρ.update f.y z) v
    (hctx.extend f.y d z hd f.different f.key f.support f.arg f.domain hdlc ihd.1 ihd.2)
  simpa only [ValExpr.subst_openVar f.different hctx.sd.lc, updates_comm ρ x f.y v z f.different]
    using hb.1

mutual
 theorem namedSpaceSubstitution {ε : ValCtx} {s : ValSpace} (h : ValSValid ε s)
    {x : VName} {u : ValExpr} {τx : ValTy} {ρ : ValEnvSem} {v : ValValSem}
    (hctx : NamedSubstCtx x u ε τx ρ v) :
    SubstSpaceAgreement (directOracle (ρ.update x v) [] []) (directOracle ρ [] []) x u s :=
  match h with
  | .real => by trivial
  | .empty => by trivial
  | .dsum h0 h1 => ⟨namedSpaceSubstitution h0 hctx, namedSpaceSubstitution h1 hctx⟩
  | .tprod h0 h1 => ⟨namedSpaceSubstitution h0 hctx, namedSpaceSubstitution h1 hctx⟩
  | .ffs h0 h1 he => by
    exact directOracle_eq_of_substitution_step ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩ x u _ _ _
      (RuntimeValue.validSpace_queryFinite hctx.valid.some (.ffs h0 h1 he))
      (by simpa only [ValSpace.subst] using RuntimeValue.validSpace_queryFinite (hctx.valid.some.subst hctx.sd) ((ValSValid.ffs h0 h1 he).subst hctx.sd))
      ⟨namedSpaceSubstitution h0 hctx, namedSpaceSubstitution h1 hctx⟩
      (namedExprSubstitution he hctx).1
 termination_by structural h

 theorem namedTypeSubstitution {ε : ValCtx} {τ : ValTy} {k : ValKind} (h : ValTValid ε τ k)
    {x : VName} {u : ValExpr} {τx : ValTy} {ρ : ValEnvSem} {v : ValValSem}
    (hctx : NamedSubstCtx x u ε τx ρ v) :
    TypeSubstitutionResult ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩ x u τ :=
  match h with
  | .space hs => by
    have hs' := namedSpaceSubstitution hs hctx
    exact ⟨hs'.dof, fun s h => by cases h; exact hs'⟩
  | .piTy L hd hb => by
    exact typeBinderStep L hd hctx (namedTypeSubstitution hd hctx)
      (fun y hy ρ' v' hc => namedTypeSubstitution (hb y hy) hc)
 termination_by structural h

 theorem namedExprSubstitution {ε : ValCtx} {e : ValExpr} {τ : ValTy} (h : ValHasType ε e τ)
    {x : VName} {u : ValExpr} {τx : ValTy} {ρ : ValEnvSem} {v : ValValSem}
    (hctx : NamedSubstCtx x u ε τx ρ v) :
    ExprSubstitutionResult ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩ x u e τ :=
  match h with
  | @ValHasType.var _ y τ hy => by
    refine ⟨?_, hctx.declarations y τ hy, ?_⟩
    · by_cases heq : y = x
      · subst y
        simpa only [ValExpr.subst, if_pos rfl, denotValB_semS, ValEnvSem.update_same]
          using hctx.argEval.symm
      · simp [ValExpr.subst, heq, denotValB_semS]
    · intro s heq
      subst τ
      exact hctx.baseDeclarations y s hy
  | .vlam L (.piTy Lty hd hc) hb => by
    exact ⟨lambdaBinderStep L hd hctx (namedTypeSubstitution hd hctx)
        (fun y hy ρ' v' hctx' => namedExprSubstitution (hb y hy) hctx'),
      typeBinderStep Lty hd hctx (namedTypeSubstitution hd hctx)
        (fun y hy ρ' v' hctx' => namedTypeSubstitution (hc y hy) hctx')⟩
  | .appV hf ha hsub hout => by
    have ihf := namedExprSubstitution hf hctx
    have iha := namedExprSubstitution ha hctx
    refine ⟨?_, namedTypeSubstitution hout hctx⟩
    apply presentation_eval_appV directOracle ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩
      _ _ _ _ _ _ ihf.1 iha.1
    · rw [ValExpr.inferTypeCtx_eq_of_typed hf, ValExpr.inferTypeCtx_eq_of_typed (hf.subst hctx.sd)]
      exact (ValTy.SameShape_subst x u _).symm
    · simpa only [ValExpr.inferTypeCtx_eq_of_typed hf,
        ValExpr.inferTypeCtx_eq_of_typed (hf.subst hctx.sd), ValTy.subst, ValTy.domain]
        using (ihf.2.1.1.toPresentation directOracle _ _ _ _)
  | .reshap he hs ht => by
    have ihe := namedExprSubstitution he hctx
    have ihs := namedTypeSubstitution hs hctx
    have iht := namedTypeSubstitution ht hctx
    exact ⟨rawPresentation_eval_reshape directOracle ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩
      _ _ _ _ _ _ iht.1 ihs.1 ihe.1, iht⟩
  | .zero hs => by
    have ihs := namedSpaceSubstitution hs hctx
    apply numeric_substitution_result_closed hctx.sd (.zero hs) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · intro q hq
      simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst q
      exact ihs
    · simp [primitiveOperands]
  | .rlit r => by
    apply numeric_substitution_result_closed hctx.sd (.rlit r) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · simp [primitiveOperands]
  | @ValHasType.scale ε e0 e1 τ h0 h1 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    cases τ with
    | space s =>
      apply numeric_substitution_result_closed hctx.sd (.scale h0 h1) (by trivial)
        hctx.valid.some (ρ.update x v) ρ
      · simp [primitiveAnnotationSpaces]
      · intro a ha
        simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact operandResult h0 ih0
        · exact operandResult h1 ih1
    | piTy d c =>
      refine ⟨?_, ih1.2⟩
      have h0' := h0.subst hctx.sd
      have h1' := h1.subst hctx.sd
      simp only [ValTy.subst] at h0' h1'
      simp only [ValExpr.subst, denotValB_semS,
        ValExpr.inferSpaceCtx_eq_spaceOf h0, ValExpr.inferSpaceCtx_eq_spaceOf h1,
        ValExpr.inferSpaceCtx_eq_spaceOf h0', ValExpr.inferSpaceCtx_eq_spaceOf h1',
        ValExpr.inferSpaceCtx, ValTy.spaceOf, ih0.1, ih1.1,
        PartialValueEval.withDimensions, PartialValueEval.dimensions,
        ValSpace.dofPartial, ValSpace.shpOfPartial, ValueShape.scale, ValSpace.dof, ValSpace.shpOf]
  | .vadd h0 h1 hs => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    apply numeric_substitution_result_closed hctx.sd (.vadd h0 h1 hs) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · intro q hq
      simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst q
      exact namedSpaceSubstitution hs hctx
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
  | .dsumE h0 h1 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    apply numeric_substitution_result_closed hctx.sd (.dsumE h0 h1) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
  | .tprodE h0 h1 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    apply numeric_substitution_result_closed hctx.sd (.tprodE h0 h1) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
  | .delta hs => by
    have ihs := namedSpaceSubstitution hs hctx
    apply numeric_substitution_result_closed hctx.sd (.delta hs) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · intro q hq
      simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst q
      exact ihs
    · simp [primitiveOperands]
  | .idelta hs => by
    have ihs := namedSpaceSubstitution hs hctx
    apply numeric_substitution_result_closed hctx.sd (.idelta hs) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · intro q hq
      simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst q
      exact ihs
    · simp [primitiveOperands]
  | .ttv_space hs h0 h1 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    have ihs := namedSpaceSubstitution hs hctx
    apply numeric_substitution_result_closed hctx.sd (.ttv_space hs h0 h1) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · intro q hq
      simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst q
      exact ihs
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
  | .ttv_real hs h0 h1 hn => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    have ihs := namedSpaceSubstitution hs hctx
    apply numeric_substitution_result_closed hctx.sd (.ttv_real hs h0 h1 hn) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · intro q hq
      simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst q
      exact ihs
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
  | .mtm hs ht h0 h1 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    have ihs := namedSpaceSubstitution hs hctx
    have iht := namedSpaceSubstitution ht hctx
    apply numeric_substitution_result_closed hctx.sd (.mtm hs ht h0 h1) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · intro q hq
      simp only [primitiveAnnotationSpaces, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ihs
      · exact iht
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
  | .vkrn h0 h1 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    apply numeric_substitution_result_closed hctx.sd (.vkrn h0 h1) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
  | .vblk h0 h1 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    apply numeric_substitution_result_closed hctx.sd (.vblk h0 h1) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
  | .rrefRep h0 h1 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    apply numeric_substitution_result_closed hctx.sd (.rrefRep h0 h1) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
  | .vtrans h0 => by
    have ih0 := namedExprSubstitution h0 hctx
    apply numeric_substitution_result_closed hctx.sd (.vtrans h0) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact operandResult h0 ih0
  | .pinv_tensor h0 => by
    have ih0 := namedExprSubstitution h0 hctx
    apply numeric_substitution_result_closed hctx.sd (.pinv_tensor h0) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact operandResult h0 ih0
  | .inv_tensor h0 => by
    have ih0 := namedExprSubstitution h0 hctx
    apply numeric_substitution_result_closed hctx.sd (.inv_tensor h0) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact operandResult h0 ih0
  | .svds h0 => by
    have ih0 := namedExprSubstitution h0 hctx
    apply numeric_substitution_result_closed hctx.sd (.svds h0) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact operandResult h0 ih0
  | .pinv_raw h0 hn => by
    have ih0 := namedExprSubstitution h0 hctx
    apply numeric_substitution_result_closed hctx.sd (.pinv_raw h0 hn) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact operandResult h0 ih0
  | .inv_raw h0 hn => by
    have ih0 := namedExprSubstitution h0 hctx
    apply numeric_substitution_result_closed hctx.sd (.inv_raw h0 hn) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst a
      exact operandResult h0 ih0
  | .gsvdS h0 h1 h2 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    have ih2 := namedExprSubstitution h2 hctx
    apply numeric_substitution_result_closed hctx.sd (.gsvdS h0 h1 h2) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
      · exact operandResult h2 ih2
  | .gsvdU h0 h1 h2 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    have ih2 := namedExprSubstitution h2 hctx
    apply numeric_substitution_result_closed hctx.sd (.gsvdU h0 h1 h2) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
      · exact operandResult h2 ih2
  | .gsvdUI h0 h1 h2 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    have ih2 := namedExprSubstitution h2 hctx
    apply numeric_substitution_result_closed hctx.sd (.gsvdUI h0 h1 h2) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
      · exact operandResult h2 ih2
  | .gsvdV h0 h1 h2 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    have ih2 := namedExprSubstitution h2 hctx
    apply numeric_substitution_result_closed hctx.sd (.gsvdV h0 h1 h2) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
      · exact operandResult h2 ih2
  | .gsvdVI h0 h1 h2 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    have ih2 := namedExprSubstitution h2 hctx
    apply numeric_substitution_result_closed hctx.sd (.gsvdVI h0 h1 h2) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
      · exact operandResult h2 ih2
  | .gpinv h0 h1 h2 => by
    have ih0 := namedExprSubstitution h0 hctx
    have ih1 := namedExprSubstitution h1 hctx
    have ih2 := namedExprSubstitution h2 hctx
    apply numeric_substitution_result_closed hctx.sd (.gpinv h0 h1 h2) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · simp [primitiveAnnotationSpaces]
    · intro a ha
      simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact operandResult h0 ih0
      · exact operandResult h1 ih1
      · exact operandResult h2 ih2
  | .vsum hs hb ht hdet => by
    have ihs := namedSpaceSubstitution hs hctx
    have ihb := fun a ha => namedExprSubstitution (hb a ha) hctx
    apply numeric_substitution_result_closed hctx.sd (.vsum hs hb ht hdet) (by trivial)
      hctx.valid.some (ρ.update x v) ρ
    · intro q hq
      simp only [primitiveAnnotationSpaces, List.mem_singleton] at hq
      subst q
      exact ihs
    · intro a ha
      exact operandResult (hb a ha) (ihb a ha)
 termination_by structural h
end

/-- Actual dependent type instantiation for the current oracle. A typed
argument that evaluates to `v` may be stored as the raw bound value or
substituted syntactically throughout the codomain. Every raw fibre agrees. -/
theorem original_type_instantiation {ε : ValCtx} {d c : ValTy} {k : ValKind}
    {u : ValExpr} (hpi : ValTValid ε (.piTy d c) k)
    (hu : ValHasType ε u d) (hc : ContextLocallyClosed ε) (hv : ValCtxValid ε)
    (ρ : ValEnvSem) (v : ValValSem)
    (he : denotValB_semS directOracle ρ [] [] u = .ok v) :
    RawTypePresentation directOracle c (ValTy.instantiate u c)
      ⟨ρ,[d],[v]⟩ ⟨ρ,[],[]⟩ := by
  cases hpi with
  | piTy L hd hb =>
    let f := freshBinder ε "unused" u L d c (.rlit 0)
    have hulc := (originalExpr_lc hu hc).1
    have hdlc := originalType_lc hd hc
    have hctx := NamedSubstCtx.of_fresh hu hulc hc hv hd hdlc f.key f.support f.domain he
    have ht := namedTypeSubstitution (hb f.y f.outside) hctx
    let W : DirectOracleReshape.OpenPushWorld directOracle :=
      ⟨ρ,f.y,d,v,[],[],rfl,hdlc,f.domain,by simp⟩
    have hopen := rawPresentation_openPush c W f.codomain
    have hsub : RawTypePresentation directOracle (ValTy.openVar f.y d c)
        (ValTy.subst f.y u (ValTy.openVar f.y d c)) W.namedWorld ⟨ρ,[],[]⟩ := ht.1
    have hres := (hopen.symm directOracle _ _ _ _).trans directOracle _ _ _ _ _ _ hsub
    simpa only [W,DirectOracleReshape.OpenPushWorld.pushedWorld,
      DirectOracleReshape.OpenPushWorld.pushedRho,DirectOracleReshape.OpenPushWorld.pushedG,
      DirectOracleReshape.OpenPushWorld.pushedD,List.nil_append,ValTy.instantiate,ValTy.openVar,
      ← ValTy.subst_intro f.y u d c f.codomain 0] using hres

def CodomainLaw (orc : FFSOracleSem) : Prop :=
  ∀ {ε : ValCtx} {d c : ValTy} {k : ValKind} {u : ValExpr},
    ValCtxValid ε → ValTValid ε (.piTy d c) k → ValHasType ε u d →
    ∀ (ρ : ValEnvSem) (v : ValValSem), denotValB_semS orc ρ [] [] u = .ok v →
    RawTypePresentation orc c (ValTy.applyCodomain u c) ⟨ρ,[d],[v]⟩ ⟨ρ,[],[]⟩

theorem codomainLaw : CodomainLaw directOracle := by
  intro ε d c k u hv hp hu ρ v he
  rw [ValTy.applyCodomain_eq_instantiate (validType_lc hv hp)
    (validExpr_lc hv hu).1]
  exact original_type_instantiation hp hu (validContext_lc hv) hv ρ v he

end GLang.RuntimeValue.TotalSubstitution
