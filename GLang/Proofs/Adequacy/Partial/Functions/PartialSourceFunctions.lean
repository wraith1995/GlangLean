import GLang.Proofs.Adequacy.Partial.Source.PartialSourceReification
import GLang.Proofs.Value.Partial.PartialValueCarrier

namespace GLang.PartialAdequacy

/-- The lambda body is proved at the canonical encoding that is actually
pushed by evaluation. Recursive dimension agreement transports its result
back to each original raw argument, including higher-order arguments. -/
theorem lambda_result {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}
    {d c : Ty} {dv cv : ValTy} {B : BasisDenot} {x : DVal} {body : ValExpr}
    (hd : DimsAt orc σ ρ Ds Γ Δ (.piTy d c) (.piTy dv cv) B)
    (hbody : ∀ (src : (denotTyAux σ Ds d).El) (arg : dv.carrierEl),
      Agree orc σ ρ Ds Γ Δ d dv B.domainBasis
        ((denotTyAux σ Ds d).embed src) (dv.carrierToVal arg) →
      ResultAgree orc σ ρ ((denotTyAux σ Ds d).embed src :: Ds)
        (dv :: Γ) (dv.carrierToVal arg :: Δ) c cv (B.applyEl src) (x.applyEl src)
        (denotValB_partial orc ρ (dv :: Γ) (dv.carrierToVal arg :: Δ) body)) :
    ResultAgree orc σ ρ Ds Γ Δ (.piTy d c) (.piTy dv cv) B x
      (denotValB_partial orc ρ Γ Δ (.vlam dv cv body)) := by
  simp only [DimsAt] at hd
  obtain ⟨D,hD⟩ := hd.1.type_ok
  refine ⟨.fn dv.carrierEl (fun arg =>
      denotValB_partial orc ρ (dv :: Γ) (dv.carrierToVal arg :: Δ) body),
    by simp only [denotValB_partial, hD], ?_⟩
  simp only [Agree]
  refine ⟨D,hD,_,rfl,?_⟩
  intro src raw arg hdecode harg
  obtain ⟨arg',hdecode',hnorm⟩ := harg.normalize
  have he : arg' = arg := Except.ok.inj (hdecode'.symm.trans hdecode)
  subst arg'
  obtain ⟨out,hout,hrel⟩ := hbody src arg hnorm
  exact ⟨out,hout,Agree.stack_transport
    (hd.2 src (dv.carrierToVal arg) arg (PartialValueDomains.carrier_roundtrip dv arg) hnorm)
    (hd.2 src raw arg hdecode harg) hrel⟩

end GLang.PartialAdequacy
