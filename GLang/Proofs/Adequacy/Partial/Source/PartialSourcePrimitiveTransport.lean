import GLang.Proofs.Adequacy.Partial.Source.PartialSourceArms

namespace GLang.PartialAdequacy

/-- Base representations depend only on the successful partial dimension. -/
theorem ResultAgree.space_dof_transport
    {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}
    {s : Space} {sv tv : ValSpace} {B : BasisDenot} {x : DVal}
    {r : Except DimError ValValSem}
    (hd : sv.dofPartial (orc ρ Γ Δ) = tv.dofPartial (orc ρ Γ Δ))
    (h : ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) B x r) :
    ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space tv) B x r := by
  obtain ⟨v,hv,ha⟩ := h
  refine ⟨v,hv,?_⟩
  cases v <;> simp only [Agree] at ha ⊢
  rwa [← hd]

variable {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
  {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}
open scoped TensorProduct

theorem scale_of_dof {s : Space} {sv : ValSpace} {B : BasisDenot}
    {r : ℝ} {x : (denotSpaceAux σ Ds s).carrier} {e₀ e₁ : ValExpr}
    (hinfer : (ValExpr.inferSpaceCtx Γ e₁).dofPartial (orc ρ Γ Δ) = sv.dofPartial (orc ρ Γ Δ))
    (h₀ : ResultAgree orc σ ρ Ds Γ Δ (.space .real) (.space .real)
      (.vecs HSpace.real [1]) (.hil ⟨HSpace.real, r⟩)
      (denotValB_partial orc ρ Γ Δ e₀))
    (h₁ : ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) B
      (.hil ⟨denotSpaceAux σ Ds s, x⟩) (denotValB_partial orc ρ Γ Δ e₁)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) B
      (.hil ⟨denotSpaceAux σ Ds s, r • x⟩)
      (denotValB_partial orc ρ Γ Δ (.scale e₀ e₁)) := by
  exact (scale rfl h₀ (h₁.space_dof_transport hinfer.symm)).space_dof_transport hinfer

theorem dsum_of_dof {s₀ s₁ : Space} {sv₀ sv₁ : ValSpace} {B₀ B₁ : BasisDenot}
    {x₀ : (denotSpaceAux σ Ds s₀).carrier} {x₁ : (denotSpaceAux σ Ds s₁).carrier}
    {e₀ e₁ : ValExpr}
    (hi₀ : (ValExpr.inferSpaceCtx Γ e₀).dofPartial (orc ρ Γ Δ) = sv₀.dofPartial (orc ρ Γ Δ))
    (hi₁ : (ValExpr.inferSpaceCtx Γ e₁).dofPartial (orc ρ Γ Δ) = sv₁.dofPartial (orc ρ Γ Δ))
    (h₀ : ResultAgree orc σ ρ Ds Γ Δ (.space s₀) (.space sv₀) B₀
      (.hil ⟨denotSpaceAux σ Ds s₀, x₀⟩) (denotValB_partial orc ρ Γ Δ e₀))
    (h₁ : ResultAgree orc σ ρ Ds Γ Δ (.space s₁) (.space sv₁) B₁
      (.hil ⟨denotSpaceAux σ Ds s₁, x₁⟩) (denotValB_partial orc ρ Γ Δ e₁)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space (.dsum s₀ s₁)) (.space (.dsum sv₀ sv₁))
      (.vecs (HSpace.dsum (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁))
        (HSpace.dsumOfLists _ _ (B₀.atSpace (denotSpaceAux σ Ds s₀))
          (B₁.atSpace (denotSpaceAux σ Ds s₁))))
      (.hil ⟨HSpace.dsum (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁), (x₀,x₁)⟩)
      (denotValB_partial orc ρ Γ Δ (.dsumE e₀ e₁)) := by
  have h := dsum rfl rfl (h₀.space_dof_transport hi₀.symm)
    (h₁.space_dof_transport hi₁.symm)
  apply h.space_dof_transport
  rw [ValSpace.dofPartial, ValSpace.dofPartial]
  simp only [ValSpace.shpOfPartial, hi₀, hi₁]

theorem tprod_of_dof {s₀ s₁ : Space} {sv₀ sv₁ : ValSpace} {B₀ B₁ : BasisDenot}
    {x₀ : (denotSpaceAux σ Ds s₀).carrier} {x₁ : (denotSpaceAux σ Ds s₁).carrier}
    {e₀ e₁ : ValExpr}
    (hi₀ : (ValExpr.inferSpaceCtx Γ e₀).dofPartial (orc ρ Γ Δ) = sv₀.dofPartial (orc ρ Γ Δ))
    (hi₁ : (ValExpr.inferSpaceCtx Γ e₁).dofPartial (orc ρ Γ Δ) = sv₁.dofPartial (orc ρ Γ Δ))
    (h₀ : ResultAgree orc σ ρ Ds Γ Δ (.space s₀) (.space sv₀) B₀
      (.hil ⟨denotSpaceAux σ Ds s₀, x₀⟩) (denotValB_partial orc ρ Γ Δ e₀))
    (h₁ : ResultAgree orc σ ρ Ds Γ Δ (.space s₁) (.space sv₁) B₁
      (.hil ⟨denotSpaceAux σ Ds s₁, x₁⟩) (denotValB_partial orc ρ Γ Δ e₁)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space (.tprod s₀ s₁)) (.space (.tprod sv₀ sv₁))
      (.vecs (HSpace.tprod (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁))
        (HSpace.tprodOfLists _ _ (B₀.atSpace (denotSpaceAux σ Ds s₀))
          (B₁.atSpace (denotSpaceAux σ Ds s₁))))
      (.hil ⟨HSpace.tprod (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁), (x₀ ⊗ₜ[ℝ] x₁)⟩)
      (denotValB_partial orc ρ Γ Δ (.tprodE e₀ e₁)) := by
  have h := tprod rfl rfl (h₀.space_dof_transport hi₀.symm)
    (h₁.space_dof_transport hi₁.symm)
  apply h.space_dof_transport
  rw [ValSpace.dofPartial, ValSpace.dofPartial]
  simp only [ValSpace.shpOfPartial, hi₀, hi₁]

end GLang.PartialAdequacy
