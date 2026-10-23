import GLang.Proofs.Value.Runtime.RuntimeValueInstantiation
import GLang.Proofs.Value.Runtime.RuntimeValueFormation
import GLang.Operational.Supporting.OperationalBaseForms
import GLang.Proofs.Preservation.OperationalKindPreservation
import GLang.Proofs.Progress.Supporting.ProgressStdBasis

namespace GLang.RuntimeValue

/-- Recover array typing without identifying any basis-dependent dimensions. -/
theorem typed_array (hc : EvalContext Ψ Γv) (h : ValExpr.OpStep Ψ e b v)
    (hv : ExprTyped Γv v) (hb : Basis.tof b = .space s) :
    ∃ sv, Nonempty (ValHasType Γv v (.space sv)) := by
  obtain ⟨sv,hi,_⟩ := typeForm_array (operational_base_forms.2 h hc.regular s hb)
  exact ⟨sv,⟨hv.at hi⟩⟩

theorem typed_matrix (hc : EvalContext Ψ Γv) (h : ValExpr.OpStep Ψ e b v)
    (hv : ExprTyped Γv v) (hb : Basis.tof b = .space (.tprod s0 s1)) :
    ∃ a b, Nonempty (ValHasType Γv v (.space (.tprod a b))) := by
  obtain ⟨a,b,hi,_,_⟩ := typeForm_tensor (operational_base_forms.2 h hc.regular _ hb)
  exact ⟨a,b,⟨hv.at hi⟩⟩

theorem typed_cob_matrix (hc : EvalContext Ψ Γv) (h : Basis.EvalBB Ψ b v b')
    (hv : ExprTyped Γv v) :
    ∃ a b, Nonempty (ValHasType Γv v (.space (.tprod a b))) := by
  obtain ⟨a,b,hi,_,_⟩ := typeForm_tensor (operational_base_forms.1 h hc.regular)
  exact ⟨a,b,⟨hv.at hi⟩⟩

noncomputable def typed_scalar (hc : EvalContext Ψ Γv) (h : ValExpr.OpStep Ψ e .one v)
    (hv : ExprTyped Γv v) : ValHasType Γv v (.space .real) :=
  hv.at (typeForm_real (operational_base_forms.2 h hc.regular .real rfl))

noncomputable def typed_imageCoords (hv : ExprTyped Γv v) (ha : ValSValid Γv a)
    (hb : ValSValid Γv b) :
    ValHasType Γv (.imageCoords (.tprod a b) v)
      (.space (.tprod (.ffs .cokernel (.tprod a b) (.reshapBase v (.tprod a b)))
        (.ffs .image (.tprod a b) (.reshapBase v (.tprod a b))))) := by
  let h := hv.base (.tprod ha hb)
  exact .mtm hb hb (.gsvdV h (.idelta ha) (.idelta hb))
    (.mtm ha ha h (.vtrans (.gsvdU h (.idelta ha) (.idelta hb))))

noncomputable def typed_sumAt (hi : ValSValid Γv index) (ht : ValSValid Γv target)
    (he : ∀ e ∈ es, ValHasType Γv e (.space target)) :
    ValHasType Γv (.sumAt index es target) (.space target) := by
  cases es with
  | nil => exact .reshap (.vsum (es := []) (s := .empty) hi (fun _ h => (List.not_mem_nil h).elim) .empty (fun _ => rfl)) (.space .empty) (.space ht)
  | cons e es => exact .reshap (.vsum hi he ht (by simp)) (.space ht) (.space ht)

/-- If the compiled function really has function type and its argument and
chosen result have the corresponding kinds, both compiler conversions use the
ordinary same-kind reshape helper. Coordinate representations may still differ. -/
noncomputable def applyAt_function_sameKind
    {Γv : ValCtx} {f a : ValExpr} {d c target : ValTy} {kd kc : ValKind}
    (hctx : ValCtxValid Γv)
    (hf : ValHasType Γv f (.piTy d c))
    (ha : ExprTyped Γv a)
    (hpi : ValTValid Γv (.piTy d c) (.arrow kd kc))
    (haKind : (ValExpr.inferType a).structuralKind = kd)
    (ht : ValTValid Γv target kc) :
    ValHasType Γv (.applyAt f a target) target := by
  have hfType := hf.inferType_eq_of_typed
  obtain ⟨ka,haValid⟩ := ha.some.regular hctx
  have hka : ka = kd := haValid.kind_eq_structural.trans haKind
  have haValid' : ValTValid Γv (ValExpr.inferType a) kd := hka ▸ haValid
  cases hpi with
  | piTy L hd hc =>
    have harg := ha.reshap haValid' hd
    have hresult := (ValTValid.piTy L hd hc).applyCodomain hctx harg
    have hcall := ValHasType.appV hf harg rfl hresult
    have hsource : ValExpr.inferType (.appV f (.reshap a d (ValExpr.inferType a))) =
        ValTy.applyCodomain (.reshap a d (ValExpr.inferType a)) c := by
      simp only [ValExpr.inferType_appV,hfType]
    have hsourceValid := hsource.symm ▸ hresult
    have hconverted := (ExprTyped.of_type hcall).reshap hsourceValid ht
    simpa only [ValExpr.applyAt,ValExpr.applyValue,hfType,ValTy.domain] using hconverted

/-- A function-shaped compiler call needs only matching argument/domain kinds.
The explicit conversion still checks dimensions and dependent function fibers. -/
noncomputable def ExprTyped.applyValue {Γv : ValCtx} {f a : ValExpr}
    (hv : ValCtxValid Γv) (hf : ExprTyped Γv f) (ha : ExprTyped Γv a)
    (hkind : (ValExpr.inferType f).structuralKind =
      .arrow (ValExpr.inferType a).structuralKind k) :
    ExprTyped Γv (.applyValue f a) := by
  cases hft : ValExpr.inferType f with
  | space s => simp [hft,ValTy.structuralKind] at hkind
  | piTy d c =>
    simp only [hft,ValTy.structuralKind,ValKind.arrow.injEq] at hkind
    have hfun := hf.at hft
    obtain ⟨_,hpi⟩ := hfun.regular hv
    obtain ⟨_,haValid⟩ := ha.some.regular hv
    cases hpi with
    | piTy L hd hc =>
      have hka := haValid.kind_eq_structural.trans
        (hkind.1.symm.trans hd.kind_eq_structural.symm)
      have harg := ha.reshap (hka ▸ haValid) hd
      have hout := (ValTValid.piTy L hd hc).applyCodomain hv harg
      have hcall := ValHasType.appV hfun harg rfl hout
      apply ExprTyped.of_type
      simpa only [ValExpr.applyValue,hft,ValTy.domain] using hcall

/-- The argument and result representations may differ, but the source frame
fixes their recursive kinds. Both compiler conversions preserve those kinds. -/
noncomputable def ExprTyped.applyAt {Γv : ValCtx} {f a : ValExpr} {target : ValTy}
    (hv : ValCtxValid Γv) (hf : ExprTyped Γv f) (ha : ExprTyped Γv a)
    (ht : ValTValid Γv target k)
    (hkind : (ValExpr.inferType f).structuralKind =
      .arrow (ValExpr.inferType a).structuralKind target.structuralKind) :
    ExprTyped Γv (.applyAt f a target) := by
  cases hft : ValExpr.inferType f with
  | space s => simp [hft,ValTy.structuralKind] at hkind
  | piTy d c =>
    simp only [hft,ValTy.structuralKind,ValKind.arrow.injEq] at hkind
    have hfun := hf.at hft
    obtain ⟨_,hpi⟩ := hfun.regular hv
    cases hpi with
    | piTy L hd hc =>
      have hpi' := ValTValid.piTy L hd hc
      have hk := hpi'.kind_eq_structural
      simp only [ValTy.structuralKind,ValKind.arrow.injEq] at hk
      have hargKind := hkind.1.symm.trans hk.1.symm
      have htKind := ht.kind_eq_structural.trans (hkind.2.symm.trans hk.2.symm)
      exact .of_type (applyAt_function_sameKind hv hfun ha hpi' hargKind (htKind ▸ ht))

noncomputable def binderAvoid (Ψ : EvalCtx) (Γv : ValCtx) (L : Finset VName) : Finset VName :=
  L ∪ Ψ.keyNames ∪ Γv.keys

theorem binderAvoid_fresh (hy : y ∉ binderAvoid Ψ Γv L) :
    y ∉ L ∧ y ∉ Ψ.keyNames ∧ y ∉ Γv := by
  simpa only [binderAvoid,Finset.mem_union,not_or,Finmap.mem_keys,and_assoc] using hy

theorem fresh_eval_key {Ψ : EvalCtx} {y : VName} {b : Basis} (hy : y ∉ Ψ.keyNames) : (y,b) ∉ Ψ := by
  intro hm
  exact hy (Finset.mem_image_of_mem Prod.fst (Finmap.mem_keys.mpr hm))

noncomputable def typed_pi (hc : EvalContext Ψ Γv)
    (he : ValTy.EvalT Ψ (Basis.tof b) d) (hd : ValTValid Γv d d.structuralKind)
    (L : Finset VName)
    (hcod : ∀ y, y ∉ L → ∀ Γv', EvalContext (Ψ.extend y b (.var y d)) Γv' →
      Nonempty (ValTValid Γv' (ValTy.openVar y d c) (ValTy.openVar y d c).structuralKind)) :
    ValTValid Γv (.piTy d c) (.arrow d.structuralKind c.structuralKind) := by
  refine .piTy (binderAvoid Ψ Γv L) hd (fun y hy => ?_)
  obtain ⟨hL,hΨ,hΓ⟩ := binderAvoid_fresh hy
  have hctx := hc.extend_var hΓ (fresh_eval_key hΨ) he hd
  have ht := (hcod y hL _ hctx).some
  simpa only [ValTy.openVar,ValTy.structuralKind_openRec] using ht

theorem typed_lambda (hc : EvalContext Ψ Γv)
    (he : ValTy.EvalT Ψ (Basis.tof b) d) (hd : ValTValid Γv d d.structuralKind)
    (L : Finset VName)
    (hbody : ∀ y, y ∉ L → ∀ Γv', EvalContext (Ψ.extend y b (.var y d)) Γv' →
      ExprTyped Γv' (ValExpr.openVar y d body))
    (hcod : ∀ y, y ∉ L → ∀ Γv', EvalContext (Ψ.extend y b (.var y d)) Γv' →
      Nonempty (ValTValid Γv' (ValTy.openVar y d c) (ValTy.openVar y d c).structuralKind)) :
    ExprTyped Γv (.vlam d c (.reshap body c c)) := by
  apply ExprTyped.of_type
  refine .vlam (binderAvoid Ψ Γv L) (typed_pi hc he hd L hcod) (fun y hy => ?_)
  obtain ⟨hL,hΨ,hΓ⟩ := binderAvoid_fresh hy
  have hctx := hc.extend_var hΓ (fresh_eval_key hΨ) he hd
  exact (hbody y hL _ hctx).reshap (hcod y hL _ hctx).some (hcod y hL _ hctx).some

end GLang.RuntimeValue
