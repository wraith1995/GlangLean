import GLang.Proofs.Value.Partial.PartialValueApplicationRuntime
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceReshape

namespace GLang.PartialAdequacy

/-- Application between distinct realizations preserves successful source
agreement. The callback's dependent result is interpreted with the converted
argument on its local stack, before transport to the requested output type. -/
theorem applyBetween_agree
    {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}
    {td tr : Ty} {domain codomain argumentType output : ValTy}
    {Bd Br : BasisDenot} {x y : DVal} {f : ValValSem}
    {argument : Except DimError ValValSem}
    (hd : DimsAt orc σ ρ Ds Γ Δ td domain Bd)
    (hat : DimsAt orc σ ρ Ds Γ Δ td argumentType Bd)
    (ho : DimsAt orc σ ρ Ds Γ Δ tr output Br)
    (ha : ResultAgree orc σ ρ Ds Γ Δ td argumentType Bd x argument)
    (hc : ∀ a : domain.carrierEl,
      Agree orc σ ρ Ds Γ Δ td domain Bd x (domain.carrierToVal a) →
      DimsAt orc σ ρ Ds (domain :: Γ) (domain.carrierToVal a :: Δ) tr codomain Br)
    (hf : ∀ a : domain.carrierEl,
      Agree orc σ ρ Ds Γ Δ td domain Bd x (domain.carrierToVal a) →
      ResultAgree orc σ ρ Ds (domain :: Γ) (domain.carrierToVal a :: Δ)
        tr codomain Br y (f.applyTyped a)) :
    ResultAgree orc σ ρ Ds Γ Δ tr output Br y
      (PartialValueEval.applyBetween orc ρ Γ Δ domain codomain argumentType output
        (.ok f) argument) := by
  obtain ⟨v,rfl,hv⟩ := ha
  obtain ⟨arg,harg,hagree⟩ := reshape_result orc σ ρ td domain argumentType
    Ds Γ Δ Γ Δ Bd x v hd hat hv
  obtain ⟨a,hdecode,hnorm⟩ := hagree.normalize
  have hargNorm : Agree orc σ ρ Ds Γ Δ td domain Bd x (domain.carrierToVal a) := hnorm
  obtain ⟨r,hr,hragree⟩ := hf a hargNorm
  simpa only [PartialValueEval.applyBetween,harg,hdecode,hr] using
    (reshape_result orc σ ρ tr output codomain Ds Γ Δ
      (domain :: Γ) (domain.carrierToVal a :: Δ) Br y r ho (hc a hargNorm) hragree)

end GLang.PartialAdequacy
