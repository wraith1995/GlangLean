import GLang.Operational.Agreement

/-! Consequences of partial source/value agreement. -/
namespace GLang.PartialAdequacy

theorem ResultAgree.isOk {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}
    {t : Ty} {tv : ValTy} {B : BasisDenot} {x : DVal} {r : Except DimError ValValSem}
    (h : ResultAgree orc σ ρ Ds Γ Δ t tv B x r) : ∃ v, r = .ok v := by
  obtain ⟨v,hv,_⟩ := h
  exact ⟨v,hv⟩

theorem ResultAgree.ne_error {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}
    {t : Ty} {tv : ValTy} {B : BasisDenot} {x : DVal} {r : Except DimError ValValSem}
    (h : ResultAgree orc σ ρ Ds Γ Δ t tv B x r) (err : DimError) : r ≠ .error err := by
  obtain ⟨v,rfl⟩ := h.isOk
  simp

/-- Agreeing values have a genuinely successful type interpretation. -/
theorem Agree.type_ok {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} :
    ∀ {Ds Γ Δ t tv B x v}, Agree orc σ ρ Ds Γ Δ t tv B x v →
      ∃ T, denotValTyPartial orc ρ Γ Δ tv = .ok T := by
  intro Ds Γ Δ t tv B x v h
  cases t <;> cases tv
  case space.piTy => simpa only [Agree] using h
  case piTy.space => simpa only [Agree] using h
  case space.space s sv =>
    cases v with
    | fn _ _ => simp only [Agree] at h
    | array a =>
      simp only [Agree] at h
      obtain ⟨n,hn,_⟩ := h
      exact ⟨PartialValType.space sv n, by simp only [denotValTyPartial, hn]⟩
  case piTy.piTy d c dv cv =>
    simp only [Agree] at h
    obtain ⟨D,hD,_⟩ := h
    exact ⟨_, denotValTyPartial_pi_ok orc ρ Γ Δ dv cv D hD⟩

/-- A source-related argument passes the evaluator's immediate domain check.
This includes higher-order arguments without replacing their callbacks. -/
theorem Agree.decode {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} :
    ∀ {Ds Γ Δ t tv B x v}, Agree orc σ ρ Ds Γ Δ t tv B x v →
      ∃ a, tv.carrierFromVal v = .ok a ∧
        PartialValueEval.decodeDomain orc ρ Γ Δ tv v = .ok a := by
  intro Ds Γ Δ t tv B x v h
  cases t <;> cases tv
  case space.piTy => simpa only [Agree] using h
  case piTy.space => simpa only [Agree] using h
  case space.space s sv =>
    cases v with
    | fn _ _ => simp only [Agree] at h
    | array a =>
      simp only [Agree] at h
      obtain ⟨n,hn,_hlen,ha,_⟩ := h
      refine ⟨a,rfl,?_⟩
      simp [PartialValueEval.decodeDomain, denotValTyPartial, hn,
        PartialValType.space, ValTy.carrierFromVal, ha]
  case piTy.piTy d c dv cv =>
    simp only [Agree] at h
    obtain ⟨D,hD,f,rfl,_⟩ := h
    have hT := denotValTyPartial_pi_ok orc ρ Γ Δ dv cv D hD
    have hd : ∃ a, (ValTy.piTy dv cv).carrierFromVal (.fn dv.carrierEl f) = .ok a := by
      simp [ValTy.carrierFromVal]
    obtain ⟨a,ha⟩ := hd
    refine ⟨a,ha,?_⟩
    simp only [PartialValueEval.decodeDomain, hT, ha]

/-- Successful source-shape agreement supplies a successful interpretation,
including the domain component of any dependent function type. -/
theorem DimsAt.type_ok {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} :
    ∀ {Ds Γ Δ t tv B}, DimsAt orc σ ρ Ds Γ Δ t tv B →
      ∃ T, denotValTyPartial orc ρ Γ Δ tv = .ok T
  | Ds, Γ, Δ, .space s, .space sv, B, h => by
      simp only [DimsAt] at h
      change sv.shpOfPartial (orc ρ Γ Δ) = .ok (srcShp σ Ds s) at h
      simp only [denotValTyPartial, ValSpace.dofPartial, h,
        bind, pure, Except.bind, Except.pure]
      exact ⟨_, rfl⟩
  | Ds, Γ, Δ, .piTy d c, .piTy dv cv, B, h => by
      simp only [DimsAt] at h
      obtain ⟨D,hD⟩ := DimsAt.type_ok h.1
      exact ⟨_,denotValTyPartial_pi_ok orc ρ Γ Δ dv cv D hD⟩
  | _,_,_,.space _,.piTy _ _,_,h => by simp only [DimsAt] at h
  | _,_,_,.piTy _ _,.space _,_,h => by simp only [DimsAt] at h
termination_by _ _ _ t tv _ _ => Ty.size t + ValTy.kindSize tv
decreasing_by all_goals simp only [Ty.size, ValTy.kindSize_piTy]; omega

end GLang.PartialAdequacy
