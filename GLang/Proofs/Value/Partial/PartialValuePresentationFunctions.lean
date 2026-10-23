import GLang.Proofs.Value.Partial.PartialValueRawReshape

namespace GLang.PartialValueSubstitution
open PaperValueDomains PartialValueTransport

private theorem applyTyped_heq {A B : Type} (h : A = B) (v : ValValSem)
    (a : A) (b : B) (hab : HEq a b) : v.applyTyped a = v.applyTyped b := by
  cases h
  rw [eq_of_heq hab]

theorem RawPresentation.decode (orc : PartialFFSOracleSem) (d d' : ValTy)
    (w u : World) (h : RawPresentation orc d d' w u) (v : ValValSem) :
    HEq (PartialValueEval.decodeDomain orc w.env w.types w.values d v)
      (PartialValueEval.decodeDomain orc u.env u.types u.values d' v) := by
  have ht := h.type_heq orc d d' w u
  have hs := h.sameShape orc d d' w u
  cases d <;> cases d'
  case space.space s s' =>
    have he := eq_of_heq ht
    simp only [PartialValueEval.decodeDomain,he]
    cases denotValTyPartial orc u.env u.types u.values (.space s') <;> cases v <;> rfl
  case space.piTy => exact hs.elim
  case piTy.space => exact hs.elim
  case piTy.piTy =>
    simp only [PartialDirectOpenPush.decode_pi]
    apply bind_heq (type_eq hs) (ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hs) _ _ ht
    intro _ _ _
    exact carrierFromVal_SameShape _ _ hs v

theorem presentation_eval_appV (orc : PartialFFSOracleSem) (w u : World)
    (f a f' a' : ValExpr) (t t' : ValTy)
    (hf : denotValB_partial orc w.env w.types w.values f = denotValB_partial orc u.env u.types u.values f')
    (ha : denotValB_partial orc w.env w.types w.values a = denotValB_partial orc u.env u.types u.values a')
    (ht : RawPresentation orc t t' w u)
    (hft : RawPresentation orc (ValExpr.inferTypeCtx w.types f)
      (ValExpr.inferTypeCtx u.types f') w u)
    (hat : RawPresentation orc (ValExpr.inferTypeCtx w.types a)
      (ValExpr.inferTypeCtx u.types a') w u) :
    denotValB_partial orc w.env w.types w.values (.appV f a) =
      denotValB_partial orc u.env u.types u.values (.appV f' a') := by
  rw [PartialDirectOpenPush.app_eq, PartialDirectOpenPush.app_eq, hf, ha]
  cases hl : ValExpr.inferTypeCtx w.types f <;>
    cases hr : ValExpr.inferTypeCtx u.types f'
  case space.space => rfl
  case space.piTy | piTy.space => simp only [hl,hr,RawPresentation] at hft
  case piTy.piTy d c d' c' =>
    rw [hl,hr] at hft
    have hd := hft.1.sameShape orc d d' w u
    exact PartialValueEval.applyDomainChecked_congr _ _ _ _ _ _ _ _ _ _ hd
      (hft.1.type_heq orc d d' w u) _ _

theorem presentation_eval_reshape (orc : PartialFFSOracleSem) (w u : World)
    (e e' : ValExpr) (t s t' s' : ValTy)
    (ht : RawPresentation orc t t' w u) (hs : RawPresentation orc s s' w u)
    (hi : RawPresentation orc (ValExpr.inferTypeCtx w.types e)
      (ValExpr.inferTypeCtx u.types e') w u)
    (he : denotValB_partial orc w.env w.types w.values e = denotValB_partial orc u.env u.types u.values e') :
    denotValB_partial orc w.env w.types w.values (.reshap e t s) =
      denotValB_partial orc u.env u.types u.values (.reshap e' t' s') := by
  rw [denotValB_partial,denotValB_partial,he]
  cases denotValB_partial orc u.env u.types u.values e' with
  | error err => rfl
  | ok v =>
    cases s <;> cases s'
    case space.piTy | piTy.space => simp only [RawPresentation] at hs
    case space.space =>
      exact ht.reshape orc _ _ _ _ w.env u.env
        w.types u.types w.types u.types w.values u.values w.values u.values hs v
    case piTy.piTy =>
      simp only [PartialValueEval.reshapeInferred]
      cases hl : ValExpr.inferTypeCtx w.types e <;> cases hr : ValExpr.inferTypeCtx u.types e'
      case space.space => rfl
      case space.piTy | piTy.space => simp only [hl,hr,RawPresentation] at hi
      case piTy.piTy =>
        rw [hl,hr] at hi
        exact ht.reshape orc _ _ _ _ w.env u.env
          w.types u.types w.types u.types w.values u.values w.values u.values hi v

/-- Cofinite body equality closes a lambda comparison without changing the raw
argument stored by either evaluator. -/
theorem presentation_eval_vlam_open (ρ ρ' : ValEnvSem) (x : VName)
    (d c d' c' : ValTy) (body body' : ValExpr)
    (hp : RawPresentation PartialDirectOracle.oracle d d' ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩)
    (hd : d.lc) (hd' : d'.lc) (hxd : x ∉ d.fv) (hxd' : x ∉ d'.fv)
    (hxb : x ∉ body.fv) (hxb' : x ∉ body'.fv)
    (hb : ∀ raw, denotValB_partial PartialDirectOracle.oracle (ρ.update x raw) [] []
        (ValExpr.openVar x d body) =
      denotValB_partial PartialDirectOracle.oracle (ρ'.update x raw) [] []
        (ValExpr.openVar x d' body')) :
    denotValB_partial PartialDirectOracle.oracle ρ [] [] (.vlam d c body) =
      denotValB_partial PartialDirectOracle.oracle ρ' [] [] (.vlam d' c' body') := by
  rw [PartialDirectOpenPush.lam_eq,PartialDirectOpenPush.lam_eq]
  have hs := hp.sameShape PartialDirectOracle.oracle _ _ _ _
  have hc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hs
  apply eq_of_heq
  apply bindAcross_heq (type_eq hs) rfl _ _ (hp.type_heq PartialDirectOracle.oracle _ _ _ _)
  intro _ _ _
  apply heq_of_eq
  apply congrArg Except.ok
  apply ValValSem.fn_partial_congr _ _ hc
  intro a
  have hreify := carrierToVal_SameShape d d' hs a (hc ▸ a) (cast_heq hc a).symm
  rw [hreify]
  have hl := PartialDirectOpenPush.eval_openPush ρ x d (d'.carrierToVal (hc ▸ a))
    [] [] body rfl hd hxd (by simp [ValTyCtxFresh]) hxb
  have hr := PartialDirectOpenPush.eval_openPush ρ' x d' (d'.carrierToVal (hc ▸ a))
    [] [] body' rfl hd' hxd' (by simp [ValTyCtxFresh]) hxb'
  exact hl.symm.trans ((hb _).trans hr)

end GLang.PartialValueSubstitution
