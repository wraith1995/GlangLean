import GLang.Proofs.Adequacy.Agreement

namespace GLang.PartialAdequacy

/-- Structural decoding and re-encoding preserves source agreement, including
all supported higher-order applications. No dimension is replaced by zero. -/
theorem Agree.normalize {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} :
    ∀ {Ds Γ Δ t tv B x v}, Agree orc σ ρ Ds Γ Δ t tv B x v →
      ∃ a, tv.carrierFromVal v = .ok a ∧
        Agree orc σ ρ Ds Γ Δ t tv B x (tv.carrierToVal a)
  | Ds, Γ, Δ, .space s, .space sv, B, x, .array a, h => ⟨a, rfl, h⟩
  | _, _, _, .space _, .space _, _, _, .fn _ _, h => by simp only [Agree] at h
  | _, _, _, .space _, .piTy _ _, _, _, _, h => by simp only [Agree] at h
  | _, _, _, .piTy _ _, .space _, _, _, _, h => by simp only [Agree] at h
  | Ds, Γ, Δ, .piTy d c, .piTy dv cv, B, x, v, h => by
      simp only [Agree] at h
      obtain ⟨D,hD,f,rfl,hf⟩ := h
      let a : (ValTy.piTy dv cv).carrierEl := fun arg =>
        (f arg).bind cv.carrierFromVal
      refine ⟨a, ?_, ?_⟩
      · simp [ValTy.carrierFromVal, a]
        funext arg
        cases f arg <;> rfl
      · simp only [ValTy.carrierToVal, Agree]
        refine ⟨D,hD,_,rfl,?_⟩
        intro src raw arg harg hrel
        obtain ⟨out,hout,hrelOut⟩ := hf src raw arg harg hrel
        obtain ⟨outEl,hdecode,hnorm⟩ := Agree.normalize hrelOut
        refine ⟨cv.carrierToVal outEl, ?_, hnorm⟩
        simp [a, hout, Except.bind, hdecode, Except.map]
termination_by _ _ _ t tv _ _ _ _ => Ty.size t + ValTy.kindSize tv
decreasing_by all_goals simp only [Ty.size, ValTy.kindSize_piTy]; omega

/-- A representation is independent of its local value stacks when both
worlds agree with the same source dimensions in every supported fiber. -/
theorem Agree.stack_transport {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} :
    ∀ {Ds Γs Δs Γt Δt t tv B x v},
      DimsAt orc σ ρ Ds Γs Δs t tv B →
      DimsAt orc σ ρ Ds Γt Δt t tv B →
      Agree orc σ ρ Ds Γs Δs t tv B x v →
      Agree orc σ ρ Ds Γt Δt t tv B x v
  | Ds, Γs, Δs, Γt, Δt, .space s, .space sv, B, x, .array a, hs, ht, h => by
      simp only [DimsAt] at hs ht
      simp only [Agree] at h ⊢
      have hd : sv.dofPartial (orc ρ Γs Δs) = sv.dofPartial (orc ρ Γt Δt) := by
        simp only [ValSpace.dofPartial, hs, ht]
      rwa [← hd]
  | _, _, _, _, _, .space _, .space _, _, _, .fn _ _, _, _, h => by simp only [Agree] at h
  | _, _, _, _, _, .space _, .piTy _ _, _, _, _, _, _, h => by simp only [Agree] at h
  | _, _, _, _, _, .piTy _ _, .space _, _, _, _, _, _, h => by simp only [Agree] at h
  | Ds, Γs, Δs, Γt, Δt, .piTy d c, .piTy dv cv, B, x, v, hs, ht, h => by
      simp only [DimsAt] at hs ht
      simp only [Agree] at h ⊢
      obtain ⟨_,_,f,hf,hrel⟩ := h
      obtain ⟨D,hD⟩ := ht.1.type_ok
      refine ⟨D,hD,f,hf,?_⟩
      intro src raw arg hdecode harg
      have hargs := Agree.stack_transport ht.1 hs.1 harg
      obtain ⟨out,hout,houtRel⟩ := hrel src raw arg hdecode hargs
      exact ⟨out,hout,Agree.stack_transport
        (hs.2 src raw arg hdecode hargs) (ht.2 src raw arg hdecode harg) houtRel⟩
termination_by _ _ _ _ _ t tv _ _ _ _ _ _ => Ty.size t + ValTy.kindSize tv
decreasing_by all_goals simp only [Ty.size, ValTy.kindSize_piTy]; omega

end GLang.PartialAdequacy
