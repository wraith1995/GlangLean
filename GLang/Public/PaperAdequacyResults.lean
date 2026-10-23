import GLang.Metatheory

namespace GLang.PaperAdequacyResults

noncomputable abbrev TypeAgreement (σ : DEnv) (ρ : ValEnvSem)
    (T : Ty) (Tv : ValTy) (B : BasisDenot) : Prop :=
  Adequacy.PartialDirect.AgreeDims σ ρ [] [] [] T Tv B ∧
  Adequacy.Direct.BasisAt σ [] T B

theorem typeAdequacy
    (hc : Adequacy.PartialDirect.Consistent Δ ε Ψ Γv σ ρ)
    (he : Operational.TyAt ε Ψ b Tv) :
    TypeAgreement σ ρ (Basis.tof b) Tv (denotBasis σ b) :=
  ⟨Metatheory.typeAdequacyAtBasis he Δ σ Γv hc,
    Adequacy.Direct.basisAt he.basisValid hc.history.ctxWF_nl hc.history.envWF_nl⟩

/-- Term adequacy exposes success, value agreement, and full type agreement
for the literal supplied checked evaluation. -/
theorem termAdequacy
    (hc : Adequacy.PartialDirect.Consistent Δ ε Ψ Γv σ ρ)
    (he : Operational.Term Δ ε Ψ t b v Tv) :
    ∃ w, denotValB_partial PartialDirectOracle.oracle ρ [] [] v = .ok w ∧
      PartialAdequacy.Agree PartialDirectOracle.oracle σ ρ [] [] []
        (Basis.tof b) Tv (denotBasis σ b) (denotTerm σ t) w ∧
      TypeAgreement σ ρ (Basis.tof b) Tv (denotBasis σ b) := by
  obtain ⟨⟨w, heval, hagree⟩, hshape⟩ := Metatheory.termAdequacy he σ Γv hc
  exact ⟨w, heval, hagree, hshape,
    Adequacy.Direct.basisAt he.basisValid hc.history.ctxWF_nl hc.history.envWF_nl⟩

theorem cobAdequacy
    (hc : Adequacy.PartialDirect.Consistent Δ ε Ψ Γv σ ρ)
    (he : Operational.Cob ε Ψ b₀ v b₁) :
    let V := denotSpace σ (Basis.sof b₀)
    let B₀ := (denotBasis σ b₀).atSpace V
    let B₁ := (denotBasis σ b₁).atSpace V
    ∃ a : FlatArray,
      denotValB_partial PartialDirectOracle.oracle ρ [] [] v = .ok (.array a) ∧
      B₁.length = B₀.length ∧ a.length = B₀.length * B₀.length ∧
      ∀ j : Fin B₀.length, B₀.getD j.val 0 =
        ∑ i : Fin B₀.length, a.get (j.val * B₀.length + i.val) • B₁.getD i.val 0 :=
  Metatheory.cobAdequacy he Δ σ Γv hc

theorem progressAndAdequacy
    (hc : Adequacy.PartialDirect.Consistent Δ ε Ψ Γv σ ρ)
    (ht : HasType Δ ε t (Basis.tof b)) (hb : Basis.BasisValid ε b) :
    ∃ v Tv w, Operational.Term Δ ε Ψ t b v Tv ∧ ValExpr.inferType v = Tv ∧
      denotValB_partial PartialDirectOracle.oracle ρ [] [] v = .ok w ∧
      PartialAdequacy.Agree PartialDirectOracle.oracle σ ρ [] [] []
        (Basis.tof b) Tv (denotBasis σ b) (denotTerm σ t) w ∧
      TypeAgreement σ ρ (Basis.tof b) Tv (denotBasis σ b) := by
  obtain ⟨v, Tv, he, hinfer, _⟩ := Metatheory.progress hc.context ht hb
  obtain ⟨w, heval, hagree, htype⟩ := termAdequacy hc he
  exact ⟨v, Tv, w, he, hinfer, heval, hagree, htype⟩

end GLang.PaperAdequacyResults
