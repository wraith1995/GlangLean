import GLang.Proofs.Adequacy.Partial.Source.PartialSourceNormalization
import GLang.Proofs.Value.Partial.PartialValueCarrier

namespace GLang.PartialAdequacy

/-- Checking a source-related value preserves its representation. The result
fibres are checked at the same argument used by the callback. -/
theorem Agree.checked {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} :
    ∀ {Ds Γ Δ t tv B x v} {T : PartialValType tv} {a : tv.carrierEl},
      DimsAt orc σ ρ Ds Γ Δ t tv B →
      denotValTyPartial orc ρ Γ Δ tv = .ok T →
      Agree orc σ ρ Ds Γ Δ t tv B x v →
      tv.carrierFromVal v = .ok a →
      ∃ b, T.check a = .ok b ∧
        Agree orc σ ρ Ds Γ Δ t tv B x (tv.carrierToVal b) := by
  intro Ds Γ Δ t tv B x v T a hd hT hv ha
  generalize hn : Ty.size t + ValTy.kindSize tv = n
  induction n using Nat.strong_induction_on generalizing Ds Γ Δ t tv B x v with
  | h n ih =>
      cases t with
      | space s =>
        cases tv with
        | piTy _ _ => simp only [Agree] at hv
        | space sv =>
          cases v with
          | fn _ _ => simp only [Agree] at hv
          | array ar =>
            simp only [ValTy.carrierFromVal, Except.ok.injEq] at ha
            subst a
            simp only [Agree] at hv
            obtain ⟨n,hn,hB,hlen,hrepr⟩ := hv
            simp only [denotValTyPartial, hn, Except.ok.injEq] at hT
            subst T
            refine ⟨ar, PartialValType.check_space_ok sv n ar hlen, ?_⟩
            simp only [ValTy.carrierToVal, Agree]
            exact ⟨n,hn,hB,hlen,hrepr⟩
      | piTy d c =>
        cases tv with
        | space _ => simp only [Agree] at hv
        | piTy dv cv =>
          simp only [Agree] at hv
          obtain ⟨D,hD,f,rfl,hf⟩ := hv
          have ht := denotValTyPartial_pi_ok orc ρ Γ Δ dv cv D hD
          rw [ht] at hT
          cases hT
          simp only [ValTy.carrierFromVal, dite_true, Except.ok.injEq] at ha
          subst a
          simp only [PartialValType.check, PartialValType.piTy]
          refine ⟨_,rfl,?_⟩
          simp only [ValTy.carrierToVal, Agree]
          refine ⟨D,hD,_,rfl,?_⟩
          intro src raw arg harg hrel
          obtain ⟨norm, hnorm, hrelNorm⟩ := hrel.normalize
          have hn : norm = arg := Except.ok.inj (hnorm.symm.trans harg)
          subst norm
          simp only [DimsAt] at hd
          have hdNorm := hd.2 src (dv.carrierToVal arg) arg
            (PartialValueDomains.carrier_roundtrip dv arg) hrelNorm
          have hdRaw := hd.2 src raw arg harg hrel
          obtain ⟨out,hout,hrelOut⟩ := hf src raw arg harg hrel
          have hrelOutNorm := Agree.stack_transport hdRaw hdNorm hrelOut
          obtain ⟨outEl,hdecode,hrelDecoded⟩ := hrelOutNorm.normalize
          obtain ⟨C,hC⟩ := hdNorm.type_ok
          have hlt : Ty.size c + ValTy.kindSize cv < n := by
            simp only [Ty.size, ValTy.kindSize_piTy] at hn
            omega
          obtain ⟨checked,hchecked,hrelChecked⟩ := ih _ hlt hdNorm hC hrelOutNorm hdecode rfl
          refine ⟨cv.carrierToVal checked, ?_, Agree.stack_transport hdNorm hdRaw hrelChecked⟩
          simp only [hC, hout, Except.bind, hdecode, hchecked, Except.map]

end GLang.PartialAdequacy
