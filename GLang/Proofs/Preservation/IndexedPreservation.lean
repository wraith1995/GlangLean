import GLang.Proofs.Preservation.IndexedPreservationHelpers

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace GLang.RuntimeValue

abbrev SpacePreservation (Ψ : EvalCtx) (sv : ValSpace) : Prop :=
  ∀ Γv, EvalContext Ψ Γv → Nonempty (ValSValid Γv sv)
abbrev TypePreservation (Ψ : EvalCtx) (tv : ValTy) : Prop :=
  ∀ Γv, EvalContext Ψ Γv → Nonempty (ValTValid Γv tv tv.structuralKind)
abbrev ExprPreservation (Ψ : EvalCtx) (v : ValExpr) : Prop :=
  ∀ Γv, EvalContext Ψ Γv → ExprTyped Γv v

/-- Indexed typing of the literal operational result, proved simultaneously
with all type, space, and coordinate-conversion expressions. -/
theorem preservation_mutual :
    (∀ {Ψ s sv}, ValSpace.EvalS Ψ s sv → SpacePreservation Ψ sv) ∧
    (∀ {Ψ t tv}, ValTy.EvalT Ψ t tv → TypePreservation Ψ tv) ∧
    (∀ {Ψ b v b'}, Basis.EvalBB Ψ b v b' → ExprPreservation Ψ v) ∧
    (∀ {Ψ e b v}, ValExpr.OpStep Ψ e b v → ExprPreservation Ψ v) := by
  refine ⟨fun h => ?_,fun h => ?_,fun h => ?_,fun h => ?_⟩
  all_goals
    exact h.rec
      (motive_1 := fun Ψ _ sv _ => SpacePreservation Ψ sv)
      (motive_2 := fun Ψ _ tv _ => TypePreservation Ψ tv)
      (motive_3 := fun Ψ _ v _ _ => ExprPreservation Ψ v)
      (motive_4 := fun Ψ _ _ v _ => ExprPreservation Ψ v)
      -- eReal
      (by
        intro _Ψ Γv hc
        exact ⟨.real⟩)
      -- eEmpty
      (by
        intro _Ψ Γv hc
        exact ⟨.empty⟩)
      -- eDual
      (by
        intro _ _ _ _ ih Γv hc
        exact ih Γv hc)
      -- eKer
      (by
        intro _ s₀ s₁ e b leev svb he hb hcompat hsvb ih_he ih_svb Γv hc
        obtain ⟨a,b,hsvbEq⟩ := evalS_tprod_inv (hb ▸ hsvb)
        subst svb
        obtain ⟨ha,hb⟩ := valSValid_tprod_inv (ih_svb Γv hc).some
        exact ⟨.ffs ha hb ((ih_he Γv hc).reshap (.space (.tprod ha hb)) (.space (.tprod ha hb)))⟩)
      -- eCoker
      (by
        intro _ s₀ s₁ e b leev svb he hb hcompat hsvb ih_he ih_svb Γv hc
        obtain ⟨a,b,hsvbEq⟩ := evalS_tprod_inv (hb ▸ hsvb)
        subst svb
        obtain ⟨ha,hb⟩ := valSValid_tprod_inv (ih_svb Γv hc).some
        exact ⟨.ffs ha hb ((ih_he Γv hc).reshap (.space (.tprod ha hb)) (.space (.tprod ha hb)))⟩)
      -- eImg
      (by
        intro _ s₀ s₁ e b leev svb he hb hcompat hsvb ih_he ih_svb Γv hc
        obtain ⟨a,b,hsvbEq⟩ := evalS_tprod_inv (hb ▸ hsvb)
        subst svb
        obtain ⟨ha,hb⟩ := valSValid_tprod_inv (ih_svb Γv hc).some
        exact ⟨.ffs ha hb ((ih_he Γv hc).reshap (.space (.tprod ha hb)) (.space (.tprod ha hb)))⟩)
      -- eCoimg
      (by
        intro _ s₀ s₁ e b leev svb he hb hcompat hsvb ih_he ih_svb Γv hc
        obtain ⟨a,b,hsvbEq⟩ := evalS_tprod_inv (hb ▸ hsvb)
        subst svb
        obtain ⟨ha,hb⟩ := valSValid_tprod_inv (ih_svb Γv hc).some
        exact ⟨.ffs ha hb ((ih_he Γv hc).reshap (.space (.tprod ha hb)) (.space (.tprod ha hb)))⟩)
      -- eTprod
      (by
        intro _ _ _ _ _ _ _ ih₀ ih₁ Γv hc
        exact ⟨.tprod (ih₀ Γv hc).some (ih₁ Γv hc).some⟩)
      -- eDsum
      (by
        intro _ _ _ _ _ _ _ ih₀ ih₁ Γv hc
        exact ⟨.dsum (ih₀ Γv hc).some (ih₁ Γv hc).some⟩)
      -- eTspace
      (by
        intro _ s sv h ih_s Γv hc
        exact ⟨.space (ih_s Γv hc).some⟩)
      -- eTpiTy
      (by
        intro _Ψ b₀ τ₀ τ₁ τv₀ τv₁ h₀ hb L h₁ ih₀ ih₁ Γv hc
        exact ⟨typed_pi hc (hb ▸ h₀) (ih₀ Γv hc).some L ih₁⟩)
      -- bInv
      (by
        intro _ b₀ b₁ leev h ih Γv hc
        obtain ⟨a,b,⟨hv⟩⟩ := typed_cob_matrix hc h (ih Γv hc)
        exact .of_type (.inv_tensor hv))
      -- bTrans
      (by
        intro _ b₀ b₁ b₂ env₀ env₁ sv h₀ h₁ hsv ih_h₀ ih_h₁ ih_hsv Γv hc
        obtain ⟨a,b,⟨hv1⟩⟩ := typed_cob_matrix hc h₁ (ih_h₁ Γv hc)
        have hs := (ih_hsv Γv hc).some
        exact .of_type (.mtm hs hs hv1 ((ih_h₀ Γv hc).base (.tprod hs hs))))
      -- bTprod
      (by
        intro _ b₀ b₁ b₀' b₁' env₀ env₁ h₀ h₁ ih_h₀ ih_h₁ Γv hc
        obtain ⟨a,b,⟨hv0⟩⟩ := typed_cob_matrix hc h₀ (ih_h₀ Γv hc)
        obtain ⟨c,d,⟨hv1⟩⟩ := typed_cob_matrix hc h₁ (ih_h₁ Γv hc)
        exact .of_type (.vkrn hv0 hv1))
      -- bDsum
      (by
        intro _ b₀ b₁ b₀' b₁' env₀ env₁ h₀ h₁ ih_h₀ ih_h₁ Γv hc
        obtain ⟨a,b,⟨hv0⟩⟩ := typed_cob_matrix hc h₀ (ih_h₀ Γv hc)
        obtain ⟨c,d,⟨hv1⟩⟩ := typed_cob_matrix hc h₁ (ih_h₁ Γv hc)
        exact .of_type (.vblk hv0 hv1))
      -- bDualStd
      (by
        intro _ b₀ leev htof hb₁ ih_hb₁ Γv hc
        obtain ⟨a,b,⟨hv⟩⟩ := typed_cob_matrix hc hb₁ (ih_hb₁ Γv hc)
        exact .of_type (.vtrans (.inv_tensor hv)))
      -- bImage
      (by
        intro _ b₀ b₀' leev hcoker h ih_h Γv hc
        exact ih_h Γv hc)
      -- bImageSvds
      (by
        intro _Ψ b₀ b₁ e leev s₀ s₁ svb hs₀ hs₁ _hb₀ _hb₁ he hsvb ih_he ih_hsvb Γv hc
        obtain ⟨a,b,hab⟩ := evalS_tprod_inv hsvb
        subst svb
        obtain ⟨ha,hb⟩ := valSValid_tprod_inv (ih_hsvb Γv hc).some
        have hv := typed_imageCoords (ih_he Γv hc) ha hb
        have hs := (hv.regular hc.valid.some).2
        apply ExprTyped.of_type
        have hi := ValExpr.inferSpaceCtx_eq_of_typed (Gamma := []) hv
        simpa only [hi,ValExpr.reshapBase] using ValHasType.reshap hv hs hs)
      -- bProjKC
      (by
        intro _ s₀ s₁ e s b₀ b₁ b₀' env₁ env₂ env₃ sv₀ sv₁ sv sv' sv₀' hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₀' hcob hembd hproj ih_sv₀ ih_sv₁ ih_sv ih_sv' ih_sv₀' ih_cob ih_embd ih_proj Γv hc
        have ha := (ih_sv₀ Γv hc).some
        have ha' := (ih_sv₀' Γv hc).some
        have hs := (ih_sv Γv hc).some
        have hs' := (ih_sv' Γv hc).some
        exact .of_type (.mtm ha' ha'
          ((ih_proj Γv hc).reshap (.space (.tprod ha' hs')) (.space (.tprod ha' hs')))
          (.mtm ha ha ((ih_cob Γv hc).base (.tprod ha ha'))
            ((ih_embd Γv hc).reshap (.space (.tprod hs ha)) (.space (.tprod hs ha))))))
      -- bProjIC
      (by
        intro _ s₀ s₁ e s b₀ b₁ b₁' env₁ env₂ env₃ sv₀ sv₁ sv sv' sv₁' hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₁' hcob hembd hproj ih_sv₀ ih_sv₁ ih_sv ih_sv' ih_sv₁' ih_cob ih_embd ih_proj Γv hc
        have ha := (ih_sv₁ Γv hc).some
        have ha' := (ih_sv₁' Γv hc).some
        have hs := (ih_sv Γv hc).some
        have hs' := (ih_sv' Γv hc).some
        exact .of_type (.mtm ha' ha'
          ((ih_proj Γv hc).reshap (.space (.tprod ha' hs')) (.space (.tprod ha' hs')))
          (.mtm ha ha ((ih_cob Γv hc).base (.tprod ha ha'))
            ((ih_embd Γv hc).reshap (.space (.tprod hs ha)) (.space (.tprod hs ha))))))
      -- bTermsRref
      (by
        intro _Ψ b b' e es env₀ env₁ sv hbb hch hsv ih_bb ih_ch ih_sv Γv hc
        have hs := (ih_sv Γv hc).some
        obtain ⟨a,⟨hv0⟩⟩ := typed_array hc hch (ih_ch Γv hc)
          (Basis.tof_dsumChain (cob_endpoints_space hbb).2 _)
        exact .of_type (.reshap (.rrefRep hv0 ((ih_bb Γv hc).base (.tprod hs hs)))
          (.space (.tprod hs hs)) (.space (.tprod hs hs))))
      -- bRefl
      (by
        intro _Ψ b sv htof hsv ih_hsv Γv hc
        have hs := (ih_hsv Γv hc).some
        exact .of_type (.reshap (.idelta hs) (.space (.tprod hs hs)) (.space (.tprod hs hs))))
      -- bProjKCCod
      (by
        intro _ s₀ s₁ e s b₀ b₁ b₁' env₁ env₃ sv₀ sv sv' hs hsofb₀ hsofb₁ hsofb₁' hsv₀ hsv hsv' hembd hproj ih_sv₀ ih_sv ih_sv' ih_embd ih_proj Γv hc
        have ha := (ih_sv₀ Γv hc).some
        have hs := (ih_sv Γv hc).some
        have hs' := (ih_sv' Γv hc).some
        exact .of_type (.mtm ha ha
          ((ih_proj Γv hc).reshap (.space (.tprod ha hs')) (.space (.tprod ha hs')))
          ((ih_embd Γv hc).reshap (.space (.tprod hs ha)) (.space (.tprod hs ha)))))
      -- bProjICDom
      (by
        intro _ s₀ s₁ e s b₀ b₁ b₀' env₁ env₃ sv₁ sv sv' hs hsofb₀ hsofb₁ hsofb₀' hsv₁ hsv hsv' hembd hproj ih_sv₁ ih_sv ih_sv' ih_embd ih_proj Γv hc
        have ha := (ih_sv₁ Γv hc).some
        have hs := (ih_sv Γv hc).some
        have hs' := (ih_sv' Γv hc).some
        exact .of_type (.mtm ha ha
          ((ih_proj Γv hc).reshap (.space (.tprod ha hs')) (.space (.tprod ha hs')))
          ((ih_embd Γv hc).reshap (.space (.tprod hs ha)) (.space (.tprod hs ha)))))
      -- oVar
      (by
        intro _ x b v hlk Γv hc
        exact hc.typed x b v hlk)
      -- oCob
      (by
        intro _ e b₀ b₁ v env₀ sv htof₀ htof₁ _he hbb hes ih_he ih_bb ih_es Γv hc
        have hs := (ih_es Γv hc).some
        exact .of_type (.ttv_space hs ((ih_bb Γv hc).base (.tprod hs hs)) ((ih_he Γv hc).base hs)))
      -- oScale
      (by
        intro _ e₀ e₁ b v₀ v₁ he₀ he₁ ih₀ ih₁ Γv hc
        exact .of_type (.scale (typed_scalar hc he₀ (ih₀ Γv hc)) (ih₁ Γv hc).some))
      -- oAdd
      (by
        intro _Ψ e₀ e₁ b sv v₀ v₁ htof hsv he₀ he₁ ih_hsv _ih₀ _ih₁ Γv hc
        obtain ⟨a,⟨h0⟩⟩ := typed_array hc he₀ (_ih₀ Γv hc) htof
        obtain ⟨b,⟨h1⟩⟩ := typed_array hc he₁ (_ih₁ Γv hc) htof
        exact .of_type (.vadd h0 h1 (ih_hsv Γv hc).some))
      -- oDsumE
      (by
        intro _ e₀ e₁ b₀ b₁ v₀ v₁ _he₀ _he₁ htof₀ htof₁ ih₀ ih₁ Γv hc
        obtain ⟨a,⟨h0⟩⟩ := typed_array hc _he₀ (ih₀ Γv hc) htof₀
        obtain ⟨b,⟨h1⟩⟩ := typed_array hc _he₁ (ih₁ Γv hc) htof₁
        exact .of_type (.dsumE h0 h1))
      -- oTprodE
      (by
        intro _ e₀ e₁ b₀ b₁ v₀ v₁ _he₀ _he₁ htof₀ htof₁ ih₀ ih₁ Γv hc
        obtain ⟨a,⟨h0⟩⟩ := typed_array hc _he₀ (ih₀ Γv hc) htof₀
        obtain ⟨b,⟨h1⟩⟩ := typed_array hc _he₁ (ih₁ Γv hc) htof₁
        exact .of_type (.tprodE h0 h1))
      -- oPinvTStd
      (by
        intro _Ψ b₀ b₁ e v he _hb₀ _hb₁ ih_he Γv hc
        obtain ⟨a,b,⟨hv⟩⟩ := typed_matrix hc he (ih_he Γv hc) rfl
        exact .of_type (.pinv_tensor hv))
      -- oPinvTGpinv
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ he hi₀ hi₁ ih_he ih_hi₀ ih_hi₁ Γv hc
        obtain ⟨a,b,⟨hv⟩⟩ := typed_matrix hc he (ih_he Γv hc) rfl
        obtain ⟨c,d,⟨h0⟩⟩ := typed_matrix hc hi₀ (ih_hi₀ Γv hc) rfl
        obtain ⟨f,g,⟨h1⟩⟩ := typed_matrix hc hi₁ (ih_hi₁ Γv hc) rfl
        exact .of_type (.gpinv hv h1 h0))
      -- oPinvDStd
      (by
        intro _Ψ b₀ b₁ e v sv₁ he hsofb₀ _hb₀ _hb₁ hsv₁ ih_he ih_hsv₁ Γv hc
        have hs := (ih_hsv₁ Γv hc).some
        exact .of_type (.pinv_tensor ((ih_he Γv hc).reshap (.space hs) (.space (.tprod hs .real)))))
      -- oPinvDGpinv
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ sv₁ he hsofb₀ _hb₀ hi₀ hi₁ hsv₁ ih_he ih_hi₀ ih_hi₁ ih_hsv₁ Γv hc
        have hs := (ih_hsv₁ Γv hc).some
        obtain ⟨a,b,⟨h0⟩⟩ := typed_matrix hc hi₀ (ih_hi₀ Γv hc) rfl
        obtain ⟨c,d,⟨h1⟩⟩ := typed_matrix hc hi₁ (ih_hi₁ Γv hc) rfl
        exact .of_type (.gpinv ((ih_he Γv hc).reshap (.space hs) (.space (.tprod hs .real))) h1 h0))
      -- oInnerStd
      (by
        intro _Ψ b₀ s sv _hb₀ hsv hsofb₀ ih_hsv Γv hc
        exact .of_type (.idelta (ih_hsv Γv hc).some))
      -- oEmbedKer
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he ih_hi₀ ih_hi₁ ih_he Γv hc
        obtain ⟨a,b,⟨hv⟩⟩ := typed_matrix hc he (ih_he Γv hc) rfl
        obtain ⟨c,d,⟨h0⟩⟩ := typed_matrix hc hi₀ (ih_hi₀ Γv hc) rfl
        obtain ⟨f,g,⟨h1⟩⟩ := typed_matrix hc hi₁ (ih_hi₁ Γv hc) rfl
        exact .of_type (.vtrans (.gsvdUI hv h0 h1)))
      -- oEmbedCoker
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he ih_hi₀ ih_hi₁ ih_he Γv hc
        obtain ⟨a,b,⟨hv⟩⟩ := typed_matrix hc he (ih_he Γv hc) rfl
        obtain ⟨c,d,⟨h0⟩⟩ := typed_matrix hc hi₀ (ih_hi₀ Γv hc) rfl
        obtain ⟨f,g,⟨h1⟩⟩ := typed_matrix hc hi₁ (ih_hi₁ Γv hc) rfl
        exact .of_type (.vtrans (.gsvdU hv h0 h1)))
      -- oEmbedImg
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he ih_hi₀ ih_hi₁ ih_he Γv hc
        obtain ⟨a,b,⟨hv⟩⟩ := typed_matrix hc he (ih_he Γv hc) rfl
        obtain ⟨c,d,⟨h0⟩⟩ := typed_matrix hc hi₀ (ih_hi₀ Γv hc) rfl
        obtain ⟨f,g,⟨h1⟩⟩ := typed_matrix hc hi₁ (ih_hi₁ Γv hc) rfl
        exact .of_type (.vtrans (.gsvdV hv h0 h1)))
      -- oEmbedCoimg
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he ih_hi₀ ih_hi₁ ih_he Γv hc
        obtain ⟨a,b,⟨hv⟩⟩ := typed_matrix hc he (ih_he Γv hc) rfl
        obtain ⟨c,d,⟨h0⟩⟩ := typed_matrix hc hi₀ (ih_hi₀ Γv hc) rfl
        obtain ⟨f,g,⟨h1⟩⟩ := typed_matrix hc hi₁ (ih_hi₁ Γv hc) rfl
        exact .of_type (.vtrans (.gsvdVI hv h0 h1)))
      -- oAppL
      (by
        intro _Ψ b₀ b₁ n₀ n₁ env₀ env₁ sv₀ sv₁ h₀ hsv₀ h₁ hsv₁ _htof₁ ih_h₀ ih_hsv₀ ih_h₁ ih_hsv₁ Γv hc
        obtain ⟨a,b,⟨h0⟩⟩ := typed_matrix hc h₀ (ih_h₀ Γv hc) rfl
        have hv := ValHasType.ttv_space (ih_hsv₀ Γv hc).some h0 (ih_h₁ Γv hc).some
        exact .of_type ((ExprTyped.of_type hv).base (ih_hsv₁ Γv hc).some))
      -- oAppI
      (by
        intro _Ψ b₀ n₀ n₁ env₀ env₁ sv h₀ hsv h₁ ih_h₀ ih_hsv ih_h₁ Γv hc
        have hs := (ih_hsv Γv hc).some
        exact .of_type (.ttv_space hs ((ih_h₀ Γv hc).reshap (.space hs) (.space (.tprod hs .real)))
          (ih_h₁ Γv hc).some))
      -- oNllam
      (by
        intro _Ψ b₀ b₁ τ₀ τ₁ e τv₀ τv₁ env hb₀ hb₁ h₀ L he h₁ ih_h₀ ih_he ih_h₁ Γv hc
        exact typed_lambda hc (hb₀ ▸ h₀) (ih_h₀ Γv hc).some L ih_he ih_h₁)
      -- oAppNVal
      (by
        intro _Ψ b₀ b₁ n₀ n₁ env₀ env₁ τ_out h₀ h₁ hout ih_h₀ ih_h₁ ih_hout Γv hc
        have hfunKind := operational_kind_of_context h₀ hc.regular
        have hargKind := operational_kind_of_context h₁ hc.regular
        have houtKind := hout.structuralKind_eq_sourceKind
        simp only [Basis.instantiate,Basis.tof_openRec,Ty.sourceKind_openRec] at houtKind
        apply ExprTyped.applyAt hc.valid.some (ih_h₀ Γv hc) (ih_h₁ Γv hc) (ih_hout Γv hc).some
        simpa only [Basis.tof,Ty.sourceKind,hargKind,houtKind] using hfunKind)
      -- oFrameReanchor
      (by
        intro _Ψ b₀ b₀' b₁ n₀ leev env₁ τv₀ τv₀' τv₁' h₀ htof hfn hdom L hx hcod ih_h₀ ih_hfn ih_hdom ih_hx ih_hcod Γv hc
        have hd := (ih_h₀ Γv hc).some
        apply ExprTyped.of_type
        refine .vlam (binderAvoid _Ψ Γv L) (typed_pi hc h₀ hd L ih_hcod) (fun y hy => ?_)
        obtain ⟨hL,hΨ,hΓ⟩ := binderAvoid_fresh hy
        have hctx := hc.extend_var hΓ (fresh_eval_key hΨ) h₀ hd
        have hF := (ih_hfn Γv hc).some.weaken (σ := τv₀) hΓ
        have hD := (ih_hdom Γv hc).some.weaken (σ := τv₀) hΓ
        have hArg := (ih_hx y hL _ hctx).reshap hD hD
        have hC := (ih_hcod y hL _ hctx).some
        have hfunKind := operational_kind_of_context hfn hc.regular
        have hdomKind := hdom.structuralKind_eq_sourceKind
        have hcallKind : (ValExpr.inferType leev).structuralKind =
            .arrow (ValExpr.inferType (.reshap (ValExpr.openVar y τv₀ env₁) τv₀' τv₀')).structuralKind
              (Basis.tof b₁).sourceKind := by
          simpa only [Basis.tof,Ty.sourceKind,ValExpr.inferType_reshap,hdomKind] using hfunKind
        have hApp := ExprTyped.applyValue hctx.valid.some (ExprTyped.of_type hF) (ExprTyped.of_type hArg) hcallKind
        have hRes := ValHasType.reshap hApp.some hC hC
        have hlF := opStep_lc hfn hc.regular.toEvalCtxLc
        have hlD := evalT_lc hdom hc.regular.toEvalCtxLc
        simpa only [ValExpr.openVar,ValExpr.applyValue,ValExpr.openRec,
          ValExpr.inferType,ValExpr.openRec_lc hlF,ValTy.openRec_lc hlD,
          ValTy.openRec_lc hlF.inferType.domain] using hRes)
      -- oFrameEta
      (by
        intro _Ψ b₀ b₁ n₀ τv₀ τv₁ env h₀ L he h₁ ih_h₀ ih_he ih_h₁ Γv hc
        exact typed_lambda hc h₀ (ih_h₀ Γv hc).some L ih_he ih_h₁)
      -- oReshape
      (by
        intro Ψ0 e b v τv_src τv_tgt he hsrc htgt ih_he ih_hsrc ih_htgt Γv hc
        have hk := hsrc.structuralKind_eq_sourceKind.trans htgt.structuralKind_eq_sourceKind.symm
        exact .of_type ((ih_he Γv hc).reshap (ih_hsrc Γv hc).some (hk.symm ▸ (ih_htgt Γv hc).some)))
      -- oLlamAssemble
      (by
        intro _Ψ b' b e sv' sv env htof' hsv' hsv L hfam ih_hsv' ih_hsv ih_hfam Γv hc
        have hs' := (ih_hsv' Γv hc).some
        have hs := (ih_hsv Γv hc).some
        obtain ⟨y,hy⟩ := Infinite.exists_notMem_finset (L ∪ _Ψ.keyNames)
        have hL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
        have hΨ : y ∉ _Ψ.keyNames := fun h => hy (Finset.mem_union_right _ h)
        have he0 : ValTy.EvalT _Ψ (Basis.tof b') (.space sv') := by rw [htof']; exact .space hsv'
        apply ExprTyped.of_type
        apply typed_sumAt hs' (.tprod hs' hs)
        intro e he
        apply Classical.choice
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
        have hctx := hc.extend_delta (fresh_eval_key hΨ) he0 hs' i.val
        exact ⟨.tprodE (.delta hs') ((ih_hfam y hL i Γv hctx).reshap (.space hs) (.space hs))⟩)
      -- oLlamAssembleReal
      (by
        intro _Ψ b' e sv' env htof' hsv' L hfam ih_hsv' ih_hfam Γv hc
        have hs' := (ih_hsv' Γv hc).some
        obtain ⟨y,hy⟩ := Infinite.exists_notMem_finset (L ∪ _Ψ.keyNames)
        have hL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
        have hΨ : y ∉ _Ψ.keyNames := fun h => hy (Finset.mem_union_right _ h)
        have he0 : ValTy.EvalT _Ψ (Basis.tof b') (.space sv') := by rw [htof']; exact .space hsv'
        apply ExprTyped.of_type
        apply typed_sumAt hs' hs'
        intro e he
        apply Classical.choice
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
        have hctx := hc.extend_delta (fresh_eval_key hΨ) he0 hs' i.val
        exact ⟨.scale ((ih_hfam y hL i Γv hctx).reshap (.space .real) (.space .real)) (.delta hs')⟩)
      -- oZero
      (by
        intro _Ψ b sv htof hsv ih_hsv Γv hc
        exact .of_type (.zero (ih_hsv Γv hc).some))
      -- oRlit
      (by
        intro _Ψ r Γv hc
        exact .of_type (.rlit r))

end GLang.RuntimeValue
