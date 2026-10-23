import GLang.Metatheory
import GLang.Proofs.Basis.BasisStandardFixed

namespace GLang.PaperBasisResults

/-- Valid bases expose a kinded type, including dependent frames. -/
theorem basisTypeValid {ε : NLCtx} {b : Basis} (hb : Basis.BasisValid ε b) :
    ∃ k, Nonempty (TValid ε (Basis.tof b) k) := by
  cases b with
  | frame b₀ b₁ =>
      obtain ⟨k₀, k₁, hk⟩ := hb.frame_inv.2.2
      exact ⟨.arrow k₀ k₁, hk⟩
  | _ =>
      obtain ⟨hs⟩ := hb.sof_valid
      exact ⟨.base, ⟨.space hs⟩⟩

theorem sourceBasisSoundness {ε : NLCtx} {b : Basis}
    (hctx : InductiveCtxWF ∅ ε) (hb : Basis.BasisValid ε b) :
    (∃ k, Nonempty (TValid ε (Basis.tof b) k)) ∧
    ∀ {σ}, EnvWF σ ∅ ε →
      Adequacy.Direct.BasisAt σ [] (Basis.tof b) (denotBasis σ b) :=
  ⟨basisTypeValid hb, fun hσ => Metatheory.sourceBasisSoundness hb hctx hσ⟩

/-- Standard basis syntax and semantic soundness, including frames. -/
theorem standardBasisSoundness {ε : NLCtx} {τ : Ty} {k : Kind}
    (hctx : InductiveCtxWF ∅ ε) (hτ : TValid ε τ k) :
    Basis.BasisValid ε (Basis.std τ) ∧ Basis.tof (Basis.std τ) = τ ∧
    Basis.isStd (Basis.std τ) ∧
    (∀ {σ}, EnvWF σ ∅ ε →
      Adequacy.Direct.BasisAt σ [] τ (denotBasis σ (Basis.std τ)) ∧
      (denotBasis σ (Basis.std τ)).RecursiveOrthonormal) ∧
    ∀ {b}, Basis.BasisValid ε b → Basis.tof b = τ →
      Basis.isStd b → Basis.std τ = b := by
  refine ⟨Basis.std_valid τ hτ, Basis.tof_std τ, Basis.isStd_std τ,
    (fun hσ => Metatheory.standardBasisSoundness hτ hctx hσ), ?_⟩
  intro b hb htof hstd
  simpa only [htof] using hb.std_tof_eq hstd

end GLang.PaperBasisResults
