import GLang.Proofs.Value.Partial.PartialValueRawPresentation

namespace GLang.PartialValueSubstitution
open PaperValueDomains PartialValueTransport
open PartialDirectOpenPush (reshape_pi)

private theorem applyTyped_heq {A B : Type} (h : A = B) (v : ValValSem)
    (a : A) (b : B) (hab : HEq a b) : v.applyTyped a = v.applyTyped b := by
  cases h
  rw [eq_of_heq hab]

/-- Reshape respects exact raw type presentation in its distinct source and
target contexts. Every partial type/domain/result check remains visible. -/
theorem RawPresentation.reshape (orc : PartialFFSOracleSem)
    (t s t' s' : ValTy) (ρ ρ' : ValEnvSem)
    (Γt Γt' Γs Γs' : List ValTy) (Δt Δt' Δs Δs' : List ValValSem)
    (ht : RawPresentation orc t t' ⟨ρ,Γt,Δt⟩ ⟨ρ',Γt',Δt'⟩)
    (hs : RawPresentation orc s s' ⟨ρ,Γs,Δs⟩ ⟨ρ',Γs',Δs'⟩)
    (v : ValValSem) :
    PartialValueEval.reshapeBetween orc ρ Γt Δt Γs Δs v t s =
      PartialValueEval.reshapeBetween orc ρ' Γt' Δt' Γs' Δs' v t' s' := by
  cases t <;> cases t' <;> cases s <;> cases s'
  case space.space.space.space t t' s s' =>
    change t.dofPartial _ = t'.dofPartial _ at ht
    change s.dofPartial _ = s'.dofPartial _ at hs
    cases v <;> simp only [PartialValueEval.reshapeBetween,PartialValueEval.reshapeArray,ht,hs]
  case space.space.piTy.piTy => cases v <;> simp [PartialValueEval.reshapeBetween]
  case piTy.piTy.space.space => simp [PartialValueEval.reshapeBetween]
  case piTy.piTy.piTy.piTy dt ct dt' ct' ds cs ds' cs' =>
    have hdt := ht.1.sameShape orc dt dt' _ _
    have hds := hs.1.sameShape orc ds ds' _ _
    have htc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hdt
    have hsc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hds
    simp only [reshape_pi]
    apply eq_of_heq
    apply bindAcross_heq (type_eq hdt) rfl _ _ (ht.1.type_heq orc dt dt' _ _)
    intro target target' htarget
    apply bindAcross_heq (type_eq hds) rfl _ _ (hs.1.type_heq orc ds ds' _ _)
    intro source source' _hsource
    apply heq_of_eq
    apply congrArg Except.ok
    apply ValValSem.fn_partial_congr _ _ htc
    intro a
    let b := htc ▸ a
    have hab : HEq a b := (cast_heq htc a).symm
    apply eq_of_heq
    apply bindAcross_heq htc rfl _ _ (check_heq hdt target target' htarget a b hab)
    intro arg arg' harg
    have hraw := carrierToVal_SameShape _ _ hdt arg arg' harg
    rw [hraw]
    have hdomain := RawPresentation.reshape orc ds dt ds' dt' ρ ρ'
      Γs Γs' Γt Γt' Δs Δs' Δt Δt' hs.1 ht.1 (dt'.carrierToVal arg')
    apply bindAcross_heq rfl rfl _ _ (heq_of_eq hdomain)
    intro argS argS' hargS
    have hargS' := eq_of_heq hargS
    subst argS'
    apply bindAcross_heq hsc rfl _ _ (carrierFromVal_SameShape _ _ hds argS)
    intro decoded decoded' hdecoded
    apply bindAcross_heq rfl rfl _ _ (heq_of_eq (applyTyped_heq hsc v decoded decoded' hdecoded))
    intro result result' hresult
    have hr := eq_of_heq hresult
    subst result'
    apply heq_of_eq
    exact RawPresentation.reshape orc ct cs ct' cs' ρ ρ'
      (dt::Γt) (dt'::Γt') (ds::Γs) (ds'::Γs')
      (dt'.carrierToVal arg'::Δt) (dt'.carrierToVal arg'::Δt') (argS::Δs) (argS::Δs')
      (ht.2 (dt'.carrierToVal arg')) (hs.2 argS) result
  all_goals first | exact ht.elim | exact hs.elim
termination_by sizeOf t + sizeOf s

end GLang.PartialValueSubstitution
