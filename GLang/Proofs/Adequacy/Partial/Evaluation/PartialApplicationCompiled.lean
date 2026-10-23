import GLang.Proofs.Adequacy.Partial.Source.PartialSourceReshape
import GLang.Proofs.Value.Runtime.RuntimeValueSemanticSubstitution
import GLang.Proofs.Value.Partial.PartialValueRawReshape

namespace GLang.PartialAdequacy
open PartialValueSubstitution

/-- Value typing and matching argument/domain kinds supply the dependent
substitution equality used by the compiler's result conversion. -/
theorem application_substitution {ε : ValCtx} {d c : ValTy} {f a : ValExpr}
    (hv : RuntimeValue.ValCtxValid ε)
    (hf : RuntimeValue.ValHasType ε f (.piTy d c))
    (ha : RuntimeValue.ValHasType ε a (ValExpr.inferType a))
    (hkind : (ValExpr.inferType a).structuralKind = d.structuralKind)
    (ρ : ValEnvSem) (raw : ValValSem)
    (he : denotValB_partial PartialDirectOracle.oracle ρ [] []
      (.reshap a d (ValExpr.inferType a)) = .ok raw) :
    RawPresentation PartialDirectOracle.oracle c
      (ValTy.applyCodomain (.reshap a d (ValExpr.inferType a)) c)
      ⟨ρ,[d],[raw]⟩ ⟨ρ,[],[]⟩ := by
  obtain ⟨k,hpi⟩ := hf.regular hv
  have hd : ∃ kd, Nonempty (RuntimeValue.ValTValid ε d kd) := by
    cases hpi with
    | piTy L hd hc => exact ⟨_,⟨hd⟩⟩
  have hk := (ha.regular hv).2.kind_eq_structural.trans
    (hkind.trans hd.choose_spec.some.kind_eq_structural.symm)
  let hu := RuntimeValue.ValHasType.reshap ha (hk ▸ (ha.regular hv).2) hd.choose_spec.some
  have hp := RuntimeValue.NamedSubstitution.original_type_instantiation_raw
    hpi hu (RuntimeValue.validContext_lc hv) hv ρ raw he
  rw [ValTy.applyCodomain_eq_instantiate (RuntimeValue.validType_lc hv hpi)
    (RuntimeValue.validExpr_lc hv hu).1]
  exact hp

/-- Once conversion to a target succeeds, checking that same target as both
reshape arguments produces the same value. -/
theorem reshape_self_of_inferred {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
    {e : ValExpr} {t : ValTy} {r : ValValSem}
    (h : denotValB_partial orc ρ [] [] (.reshap e t (ValExpr.inferType e)) = .ok r) :
    denotValB_partial orc ρ [] [] (.reshap e t t) = .ok r := by
  simp only [denotValB_partial, ValExpr.inferTypeCtx_nil,
    PartialValueEval.reshapeInferred_self] at h ⊢
  cases he : denotValB_partial orc ρ [] [] e with
  | error err => simp [he] at h
  | ok v =>
    simp only [he] at h ⊢
    cases t with
    | piTy d c =>
      cases hi : ValExpr.inferType e <;>
        simpa only [PartialValueEval.reshapeInferred,hi,
          PartialValueEval.reshapeBetween] using h
    | space s =>
      cases hi : ValExpr.inferType e with
      | piTy d c => simp [hi,PartialValueEval.reshapeBetween] at h
      | space source =>
        cases v with
        | fn A f => simp [hi,PartialValueEval.reshapeBetween] at h
        | array ar =>
          simp only [hi,PartialValueEval.reshapeBetween,PartialValueEval.reshapeArray] at h
          simp only [PartialValueEval.reshapeInferred,PartialValueEval.reshapeBetween,
            PartialValueEval.reshapeArray]
          split at h <;> simp_all
          split at h <;> simp_all

/-- The compiler's explicit argument and result conversions implement dependent
application. The result conversion uses substitution, not an application annotation. -/
theorem applyAt_agree
    {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {td tr : Ty} {d c out : ValTy} {f a : ValExpr}
    {Bd Br : BasisDenot} {x y : DVal} {fv : ValValSem}
    (hi : ValExpr.inferTypeCtx [] f = .piTy d c)
    (he : denotValB_partial orc ρ [] [] f = .ok fv)
    (hd : DimsAt orc σ ρ [] [] [] td d Bd)
    (ha : TermTraceAt orc σ ρ a td (ValExpr.inferTypeCtx [] a) Bd x)
    (ho : DimsAt orc σ ρ [] [] [] tr out Br)
    (callback : ∀ raw (arg : d.carrierEl), d.carrierFromVal raw = .ok arg →
      Agree orc σ ρ [] [] [] td d Bd x raw →
      DimsAt orc σ ρ [] [d] [raw] tr c Br ∧
      ResultAgree orc σ ρ [] [d] [raw] tr c Br y (fv.applyTyped arg))
    (substitution : ∀ raw,
      denotValB_partial orc ρ [] [] (.reshap a d (ValExpr.inferType a)) = .ok raw →
      RawPresentation orc c (ValTy.applyCodomain (.reshap a d (ValExpr.inferType a)) c)
        ⟨ρ,[d],[raw]⟩ ⟨ρ,[],[]⟩) :
    ResultAgree orc σ ρ [] [] [] tr out Br y
      (denotValB_partial orc ρ [] [] (.applyAt f a out)) := by
  obtain ⟨av,hav,harel⟩ := ha.result
  obtain ⟨raw,hconvert,hraw⟩ := reshape_result orc σ ρ td d _ [] [] [] [] [] Bd x av
    hd ha.dims harel
  have hu : denotValB_partial orc ρ [] [] (.reshap a d (ValExpr.inferType a)) = .ok raw := by
    simpa only [denotValB_partial, ValExpr.inferTypeCtx_nil, hav,
      PartialValueEval.reshapeInferred_self] using hconvert
  obtain ⟨arg,hdecode,_⟩ := hraw.normalize
  obtain ⟨D,hD⟩ := hd.type_ok
  obtain ⟨checked,hcheck,hchecked⟩ := Agree.checked hd hD hraw hdecode
  have hn := PartialValueDomains.carrier_roundtrip d checked
  obtain ⟨hdn,r,hr,hrel⟩ := callback (d.carrierToVal checked) checked hn hchecked
  have hdr := (callback raw arg hdecode hraw).1
  have hrelRaw := Agree.stack_transport hdn hdr hrel
  obtain ⟨result,hresult,hagree⟩ := reshape_result orc σ ρ tr out c
    [] [] [] [d] [raw] Br y r ho hdr hrelRaw
  have hsub := substitution raw hu
  have hreshape := RawPresentation.reshape orc out c out
    (ValTy.applyCodomain (.reshap a d (ValExpr.inferType a)) c)
    ρ ρ [] [] [d] [] [] [] [raw] []
    (RawPresentation.refl orc out ⟨ρ,[],[]⟩) hsub r
  rw [hreshape] at hresult
  refine ⟨result,?_,hagree⟩
  change denotValB_partial orc ρ [] []
    (.reshap (.applyValue f a) out (ValExpr.inferType (.applyValue f a))) = .ok result
  have hi' : ValExpr.inferType f = .piTy d c := by simpa only [ValExpr.inferTypeCtx_nil] using hi
  simp only [ValExpr.applyAt, ValExpr.applyValue, hi', ValTy.domain_piTy,
    denotValB_partial, ValExpr.inferTypeCtx_nil, hi', ValExpr.inferType,
    hu, he, PartialValueEval.reshapeInferred_self,
    PartialValueEval.applyDomainChecked, PartialValueEval.checkResult,
    hdecode, checkValTyPartial, hD, hcheck, Except.bind, hr, hresult]

end GLang.PartialAdequacy
