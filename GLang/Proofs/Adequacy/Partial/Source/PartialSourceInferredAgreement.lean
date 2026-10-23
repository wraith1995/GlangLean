import GLang.Proofs.Adequacy.Partial.Source.PartialSourceInferredType

namespace GLang.PartialAdequacy

/-- The array-shape companion and inferred Pi realization together recover
agreement at the complete inferred value type. -/
theorem inferType_dims
    {Δ Γ Ψ e b v tv} (h : S.Term Δ Γ Ψ e b v tv)
    {orc : PartialFFSOracleSem} {Δc Γc Γv σ ρ}
    (hc : History orc Δc Γc Ψ Γv σ ρ) (hirr : PartialDirectFv.OracleFresh orc)
    (hd : DimsAt orc σ ρ [] [] [] (Basis.tof b) tv (denotBasis σ b))
    (hm : ∀ sv, tv = .space sv →
      ValSpace.shpOfPartial (orc ρ [] []) (ValExpr.inferSpaceCtx [] v) =
        ValSpace.shpOfPartial (orc ρ [] []) sv) :
    DimsAt orc σ ρ [] [] [] (Basis.tof b) (ValExpr.inferTypeCtx [] v) (denotBasis σ b) := by
  have hs := inferType_sameShape h hc
  cases tv with
  | space sv =>
    cases hi : ValExpr.inferTypeCtx [] v with
    | piTy d c => simp only [hi,ValSoundOfDenot.ValTy.SameShape] at hs
    | space s =>
      have he := inferType_spaceOf_eq h hc s hi
      have hm' := hm sv rfl
      rw [he] at hm'
      cases ht : Basis.tof b with
      | piTy d c => simp only [ht,DimsAt] at hd
      | space src => simpa only [ht,DimsAt,hm'] using hd
  | piTy d c =>
    cases ht : Basis.tof b with
    | space src => simp only [ht,DimsAt] at hd
    | piTy sd sc => simpa only [ht] using inferType_pi_dims h hc hirr ht hd

/-- Retagging a successful trace by inference changes no runtime value. -/
theorem TermTraceAt.inferred
    {Δ Γ Ψ e b v tv} (h : S.Term Δ Γ Ψ e b v tv)
    {orc : PartialFFSOracleSem} {Δc Γc Γv σ ρ}
    (hc : History orc Δc Γc Ψ Γv σ ρ) (hirr : PartialDirectFv.OracleFresh orc)
    (hv : TermTraceAt orc σ ρ v (Basis.tof b) tv (denotBasis σ b) (denotTerm σ e))
    (hm : ∀ sv, tv = .space sv →
      ValSpace.shpOfPartial (orc ρ [] []) (ValExpr.inferSpaceCtx [] v) =
        ValSpace.shpOfPartial (orc ρ [] []) sv) :
    TermTraceAt orc σ ρ v (Basis.tof b) (ValExpr.inferTypeCtx [] v)
      (denotBasis σ b) (denotTerm σ e) := by
  have hd := inferType_dims h hc hirr hv.dims hm
  obtain ⟨r,hr,ha⟩ := hv.result
  exact ⟨⟨r,hr,Agree.representation_transport σ (inferType_sameShape h hc).symm hv.dims hd ha⟩,hd⟩

end GLang.PartialAdequacy
