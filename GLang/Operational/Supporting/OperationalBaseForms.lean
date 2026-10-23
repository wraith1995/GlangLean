import GLang.Operational.Supporting.OperationalValueForms

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace GLang.RuntimeValue
open V2

abbrev BaseForm (Ψ : EvalCtx) (b : Basis) (v : ValExpr) : Prop :=
  EvalCtxValidPlus Ψ → ∀ s, Basis.tof b = .space s →
    typeForm (ValExpr.inferType v) = .space (sourceSpaceForm s)

abbrev CobForm (Ψ : EvalCtx) (b : Basis) (v : ValExpr) : Prop :=
  EvalCtxValidPlus Ψ → typeForm (ValExpr.inferType v) =
    .space (.tprod (sourceSpaceForm (Basis.sof b)) (sourceSpaceForm (Basis.sof b)))

set_option maxHeartbeats 1000000 in
theorem operational_base_forms :
    (∀ {Ψ b v b'}, Basis.EvalBB Ψ b v b' → CobForm Ψ b v) ∧
    (∀ {Ψ e b v}, ValExpr.OpStep Ψ e b v → BaseForm Ψ b v) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  all_goals
    exact h.rec
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun _ _ _ _ => True)
      (motive_3 := fun Ψ b v _ _ => CobForm Ψ b v)
      (motive_4 := fun Ψ _ b v _ => BaseForm Ψ b v)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      -- bInv
      (by
        intro _ b₀ b₁ leev h ih hc
        obtain ⟨s0,s1,hinf,h0,h1⟩ := typeForm_tensor (ih hc)
        simp only [ValExpr.inferType,hinf,typeForm,spaceForm,h0,h1,Basis.EvalBB.sof_eq h])
      -- bTrans
      (by
        intro _ b₀ b₁ b₂ env₀ env₁ sv h₀ h₁ hsv ih_h₀ ih_h₁ ih_hsv hc
        have form_hsv := eval_forms.1 hsv
        obtain ⟨s0,s1,hi,h0,h1⟩ := typeForm_tensor (ih_h₁ hc)
        have hs := eval_forms.1 hsv
        simpa only [ValExpr.inferType,ValExpr.reshapBase,hi,typeForm,spaceForm,hs,h1,
          Basis.EvalBB.sof_eq h₀])
      -- bTprod
      (by
        intro _ b₀ b₁ b₀' b₁' env₀ env₁ h₀ h₁ ih_h₀ ih_h₁ hc
        obtain ⟨a,b,hi,h0,h1⟩ := typeForm_tensor (ih_h₀ hc)
        obtain ⟨c,d,hj,h2,h3⟩ := typeForm_tensor (ih_h₁ hc)
        simp only [ValExpr.inferType,hi,hj,typeForm,spaceForm,h0,h1,h2,h3,Basis.sof,sourceSpaceForm])
      -- bDsum
      (by
        intro _ b₀ b₁ b₀' b₁' env₀ env₁ h₀ h₁ ih_h₀ ih_h₁ hc
        obtain ⟨a,b,hi,h0,h1⟩ := typeForm_tensor (ih_h₀ hc)
        obtain ⟨c,d,hj,h2,h3⟩ := typeForm_tensor (ih_h₁ hc)
        simp only [ValExpr.inferType,hi,hj,typeForm,spaceForm,h0,h1,h2,h3,Basis.sof,sourceSpaceForm])
      -- bDualStd
      (by
        intro _ b₀ leev htof hb₁ ih_hb₁ hc
        obtain ⟨a,b,hi,h0,h1⟩ := typeForm_tensor (ih_hb₁ hc)
        simp only [ValExpr.inferType,hi,typeForm,spaceForm,h0,h1,Basis.sof,sourceSpaceForm])
      -- bImage
      (by
        intro _ b₀ b₀' leev hcoker h ih_h hc
        obtain ⟨s0,s1,e,hsof⟩ := hcoker
        simpa [Basis.sof,hsof,sourceSpaceForm] using ih_h hc)
      -- bImageSvds
      (by
        intro _Ψ b₀ b₁ e leev s₀ s₁ svb hs₀ hs₁ _hb₀ _hb₁ he hsvb _ih_he _ih_hsvb hc
        have form_hsvb := eval_forms.1 hsvb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- bProjKC
      (by
        intro _ s₀ s₁ e s b₀ b₁ b₀' env₁ env₂ env₃ sv₀ sv₁ sv sv' sv₀' hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₀' hcob hembd hproj ih_sv₀ ih_sv₁ ih_sv ih_sv' ih_sv₀' ih_cob ih_embd ih_proj hc
        have form_hsv := eval_forms.1 hsv
        have form_hsv₀ := eval_forms.1 hsv₀
        have form_hsv₁ := eval_forms.1 hsv₁
        have form_hsv' := eval_forms.1 hsv'
        have form_hsv₀' := eval_forms.1 hsv₀'
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- bProjIC
      (by
        intro _ s₀ s₁ e s b₀ b₁ b₁' env₁ env₂ env₃ sv₀ sv₁ sv sv' sv₁' hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₁' hcob hembd hproj ih_sv₀ ih_sv₁ ih_sv ih_sv' ih_sv₁' ih_cob ih_embd ih_proj hc
        have form_hsv := eval_forms.1 hsv
        have form_hsv₀ := eval_forms.1 hsv₀
        have form_hsv₁ := eval_forms.1 hsv₁
        have form_hsv' := eval_forms.1 hsv'
        have form_hsv₁' := eval_forms.1 hsv₁'
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- bTermsRref
      (by
        intro _Ψ b b' e es env₀ env₁ sv hbb hch hsv _ih_bb _ih_ch _ih_sv hc
        have form_hsv := eval_forms.1 hsv
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- bRefl
      (by
        intro _Ψ b sv htof hsv _ih_hsv hc
        have form_hsv := eval_forms.1 hsv
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- bProjKCCod
      (by
        intro _ s₀ s₁ e s b₀ b₁ b₁' env₁ env₃ sv₀ sv sv' hs hsofb₀ hsofb₁ hsofb₁' hsv₀ hsv hsv' hembd hproj ih_sv₀ ih_sv ih_sv' ih_embd ih_proj hc
        have form_hsv := eval_forms.1 hsv
        have form_hsv₀ := eval_forms.1 hsv₀
        have form_hsv' := eval_forms.1 hsv'
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- bProjICDom
      (by
        intro _ s₀ s₁ e s b₀ b₁ b₀' env₁ env₃ sv₁ sv sv' hs hsofb₀ hsofb₁ hsofb₀' hsv₁ hsv hsv' hembd hproj ih_sv₁ ih_sv ih_sv' ih_embd ih_proj hc
        have form_hsv := eval_forms.1 hsv
        have form_hsv₁ := eval_forms.1 hsv₁
        have form_hsv' := eval_forms.1 hsv'
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oVar
      (by
        intro _ x b v hlk hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        have ht := eval_forms.2 (hc x b v hlk).2.1
        simpa only [hb,sourceTypeForm] using ht)
      -- oCob
      (by
        intro _ e b₀ b₁ v env₀ sv htof₀ htof₁ _he hbb hes ih_he ih_bb ih_es hc s hb
        have form_hes := eval_forms.1 hes
        have hso := V2.sof_of_tof_eq_space hb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oScale
      (by
        intro _ e₀ e₁ b v₀ v₁ he₀ he₁ ih₀ ih₁ hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        exact ih₁ hc s hb)
      -- oAdd
      (by
        intro _Ψ e₀ e₁ b sv v₀ v₁ htof hsv he₀ he₁ _ih_hsv _ih₀ _ih₁ hc s hb
        have form_hsv := eval_forms.1 hsv
        have hso := V2.sof_of_tof_eq_space hb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oDsumE
      (by
        intro _ e₀ e₁ b₀ b₁ v₀ v₁ _he₀ _he₁ htof₀ htof₁ ih₀ ih₁ hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        have hh0 := ih₀ hc _ htof₀
        have hh1 := ih₁ hc _ htof₁
        obtain ⟨a,hi,h0⟩ := typeForm_array hh0
        obtain ⟨b,hj,h1⟩ := typeForm_array hh1
        simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb
        subst s
        simp [ValExpr.inferType,hi,hj,ValTy.spaceOf,typeForm,spaceForm,h0,h1,sourceSpaceForm,Basis.sof])
      -- oTprodE
      (by
        intro _ e₀ e₁ b₀ b₁ v₀ v₁ _he₀ _he₁ htof₀ htof₁ ih₀ ih₁ hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        have hh0 := ih₀ hc _ htof₀
        have hh1 := ih₁ hc _ htof₁
        obtain ⟨a,hi,h0⟩ := typeForm_array hh0
        obtain ⟨b,hj,h1⟩ := typeForm_array hh1
        simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb
        subst s
        simp [ValExpr.inferType,hi,hj,ValTy.spaceOf,typeForm,spaceForm,h0,h1,sourceSpaceForm,Basis.sof])
      -- oPinvTStd
      (by
        intro _Ψ b₀ b₁ e v he _hb₀ _hb₁ ih_he hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        obtain ⟨a,b,hi,h0,h1⟩ := typeForm_tensor (ih_he hc _ rfl)
        simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb
        subst s
        simp_all [ValExpr.inferType,hi,typeForm,spaceForm,sourceSpaceForm,Basis.sof])
      -- oPinvTGpinv
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ he hi₀ hi₁ ih_he _ih_hi₀ _ih_hi₁ hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        obtain ⟨a,b,hi,h0,h1⟩ := typeForm_tensor (ih_he hc _ rfl)
        simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb
        subst s
        simp_all [ValExpr.inferType,hi,typeForm,spaceForm,sourceSpaceForm,Basis.sof])
      -- oPinvDStd
      (by
        intro _Ψ b₀ b₁ e v sv₁ he hsofb₀ _hb₀ _hb₁ hsv₁ ih_he _ih_hsv₁ hc s hb
        have form_hsv₁ := eval_forms.1 hsv₁
        have hso := V2.sof_of_tof_eq_space hb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oPinvDGpinv
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ sv₁ he hsofb₀ _hb₀ hi₀ hi₁ hsv₁ ih_he _ih_hi₀ _ih_hi₁ _ih_hsv₁ hc s hb
        have form_hsv₁ := eval_forms.1 hsv₁
        have hso := V2.sof_of_tof_eq_space hb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oInnerStd
      (by
        intro _Ψ b₀ s sv _hb₀ hsv hsofb₀ _ih_hsv hc s hb
        have form_hsv := eval_forms.1 hsv
        have hso := V2.sof_of_tof_eq_space hb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oEmbedKer
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he _ih_hi₀ _ih_hi₁ ih_he hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        obtain ⟨a,b,hi,h0,h1⟩ := typeForm_tensor (ih_he hc _ rfl)
        simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb
        subst s
        simp_all [ValExpr.inferType,hi,typeForm,spaceForm,sourceSpaceForm,Basis.sof])
      -- oEmbedCoker
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he _ih_hi₀ _ih_hi₁ ih_he hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        obtain ⟨a,b,hi,h0,h1⟩ := typeForm_tensor (ih_he hc _ rfl)
        simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb
        subst s
        simp_all [ValExpr.inferType,hi,typeForm,spaceForm,sourceSpaceForm,Basis.sof])
      -- oEmbedImg
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he _ih_hi₀ _ih_hi₁ ih_he hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        obtain ⟨a,b,hi,h0,h1⟩ := typeForm_tensor (ih_he hc _ rfl)
        simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb
        subst s
        simp_all [ValExpr.inferType,hi,typeForm,spaceForm,sourceSpaceForm,Basis.sof])
      -- oEmbedCoimg
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he _ih_hi₀ _ih_hi₁ ih_he hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        obtain ⟨a,b,hi,h0,h1⟩ := typeForm_tensor (ih_he hc _ rfl)
        simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb
        subst s
        simp_all [ValExpr.inferType,hi,typeForm,spaceForm,sourceSpaceForm,Basis.sof])
      -- oAppL
      (by
        intro _Ψ b₀ b₁ n₀ n₁ env₀ env₁ sv₀ sv₁ h₀ hsv₀ h₁ hsv₁ _htof₁ _ih_h₀ _ih_hsv₀ _ih_h₁ _ih_hsv₁ hc s hb
        have form_hsv₀ := eval_forms.1 hsv₀
        have form_hsv₁ := eval_forms.1 hsv₁
        have hso := V2.sof_of_tof_eq_space hb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oAppI
      (by
        intro _Ψ b₀ n₀ n₁ env₀ env₁ sv h₀ hsv h₁ _ih_h₀ _ih_hsv _ih_h₁ hc s hb
        have form_hsv := eval_forms.1 hsv
        have hso := V2.sof_of_tof_eq_space hb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oNllam
      (by
        intro _Ψ b₀ b₁ τ₀ τ₁ e τv₀ τv₁ env hb₀ hb₁ h₀ L he h₁ ih_h₀ ih_he ih_h₁ hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        simp only [Basis.tof] at hb
        cases hb)
      -- oAppNVal
      (by
        intro _Ψ b₀ b₁ n₀ n₁ env₀ env₁ τ_out h₀ h₁ hout _ih_h₀ _ih_h₁ _ih_hout hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        simpa only [ValExpr.inferType,hb,sourceTypeForm] using eval_forms.2 hout)
      -- oFrameReanchor
      (by
        intro _Ψ b₀ b₀' b₁ n₀ leev env₁ τv₀ τv₀' τv₁' h₀ htof hfn hdom L hx hcod _ih_h₀ _ih_hfn _ih_hdom _ih_hx _ih_hcod hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        simp only [Basis.tof] at hb
        cases hb)
      -- oFrameEta
      (by
        intro _Ψ b₀ b₁ n₀ τv₀ τv₁ env h₀ L he h₁ _ih_h₀ _ih_he _ih_h₁ hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        simp only [Basis.tof] at hb
        cases hb)
      -- oReshape
      (by
        intro Ψ0 e b v τv_src τv_tgt he hsrc htgt ih_he _ih_hsrc _ih_htgt hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        simpa only [ValExpr.inferType,hb,sourceTypeForm] using eval_forms.2 htgt)
      -- oLlamAssemble
      (by
        intro _Ψ b' b e sv' sv env htof' hsv' hsv L hfam _ih_hsv' _ih_hsv _ih_hfam hc s hb
        have form_hsv := eval_forms.1 hsv
        have form_hsv' := eval_forms.1 hsv'
        have hso := V2.sof_of_tof_eq_space hb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oLlamAssembleReal
      (by
        intro _Ψ b' e sv' env htof' hsv' L hfam _ih_hsv' _ih_hfam hc s hb
        have form_hsv' := eval_forms.1 hsv'
        have hso := V2.sof_of_tof_eq_space hb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oZero
      (by
        intro _Ψ b sv htof hsv _ih_hsv hc s hb
        have form_hsv := eval_forms.1 hsv
        have hso := V2.sof_of_tof_eq_space hb
        first
          | (simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb; subst s)
          | skip
        simp_all [ValExpr.inferType,ValExpr.reshapBase,ValExpr.sumAt,typeForm,spaceForm,
          sourceSpaceForm,sourceTypeForm,Basis.sof,Basis.tof])
      -- oRlit
      (by
        intro _Ψ r hc s hb
        have hso := V2.sof_of_tof_eq_space hb
        simp only [Basis.tof,Basis.sof,Ty.space.injEq] at hb
        subst s
        rfl)

set_option maxHeartbeats 2000000 in
/-- A change of basis always has space-basis endpoints. -/
theorem cob_endpoints_space {Ψ b v b'} (h : Basis.EvalBB Ψ b v b') :
    Basis.tof b = .space (Basis.sof b) ∧ Basis.tof b' = .space (Basis.sof b') := by
  refine h.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ b _ b' _ =>
      Basis.tof b = .space (Basis.sof b) ∧ Basis.tof b' = .space (Basis.sof b'))
    (motive_4 := fun _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros <;> first | trivial | simp_all [Basis.tof,Basis.std]

end GLang.RuntimeValue
