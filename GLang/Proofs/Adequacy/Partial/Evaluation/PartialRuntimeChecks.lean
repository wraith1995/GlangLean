import GLang.Proofs.Adequacy.Partial.Source.PartialSourceChecking
import GLang.Proofs.Value.Partial.PartialValueRuntimeChecks

namespace GLang.PartialAdequacy

/-- Runtime result checks preserve successful source agreement. This includes
function results: checking their dependent fibers does not weaken adequacy. -/
theorem ResultAgree.checkRuntime
    {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}
    {t : Ty} {tv : ValTy} {B : BasisDenot} {x : DVal}
    {r : Except DimError ValValSem}
    (hd : DimsAt orc σ ρ Ds Γ Δ t tv B)
    (hr : ResultAgree orc σ ρ Ds Γ Δ t tv B x r) :
    ResultAgree orc σ ρ Ds Γ Δ t tv B x
      (PartialValueEval.checkRuntime orc ρ Γ Δ tv r) := by
  obtain ⟨v, rfl, hv⟩ := hr
  obtain ⟨a, ha, _⟩ := hv.normalize
  obtain ⟨T, hT⟩ := hd.type_ok
  obtain ⟨b, hb, hrel⟩ := hv.checked hd hT ha
  refine ⟨tv.carrierToVal b, ?_, hrel⟩
  simp only [PartialValueEval.checkRuntime, PartialValueEval.checkResult,
    ha, checkValTyPartial, hT, hb, Except.map]

/-- Checked application preserves adequacy when the callback represents the
source application on source-agreeing arguments. The argument may have been
produced with a different value-type annotation. -/
theorem applyChecked_agree
    {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}
    {td tr : Ty} {domain output : ValTy} {Bd Br : BasisDenot}
    {x y : DVal} {f : ValValSem} {argument : Except DimError ValValSem}
    (hd : DimsAt orc σ ρ Ds Γ Δ td domain Bd)
    (ho : DimsAt orc σ ρ Ds Γ Δ tr output Br)
    (ha : ResultAgree orc σ ρ Ds Γ Δ td domain Bd x argument)
    (hf : ∀ a : domain.carrierEl,
      Agree orc σ ρ Ds Γ Δ td domain Bd x (domain.carrierToVal a) →
      ResultAgree orc σ ρ Ds Γ Δ tr output Br y (f.applyTyped a)) :
    ResultAgree orc σ ρ Ds Γ Δ tr output Br y
      (PartialValueEval.applyChecked orc ρ Γ Δ domain output (.ok f) argument) := by
  obtain ⟨v, rfl, hv⟩ := ha
  obtain ⟨a, ha, _⟩ := hv.normalize
  obtain ⟨T, hT⟩ := hd.type_ok
  obtain ⟨b, hb, hrel⟩ := Agree.checked hd hT hv ha
  have harg : PartialValueEval.checkResult orc ρ Γ Δ domain (.ok v) = .ok b := by
    simp only [PartialValueEval.checkResult, ha, checkValTyPartial, hT, hb]
  simpa only [PartialValueEval.applyChecked, harg] using
    (hf b hrel).checkRuntime ho

end GLang.PartialAdequacy
