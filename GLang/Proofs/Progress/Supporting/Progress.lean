

import GLang.Proofs.Progress.Supporting.ProgressCobPaper

namespace GLang.V2

theorem progress
    {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty} {b : Basis}
    (htele : CtxTele Δ Γ Ψ)
    (hwfΔΓ : CtxWF' Δ Γ) (hwfΨ : EvalCtxValid Ψ) (hwflc : EvalCtxLc Ψ)
    (hanch : EvalCtxLamAnchored Ψ) (hΓΨ : TypingImplyEval Δ Γ Ψ)
    (htype : HasType Δ Γ e τ)
    (hb : Basis.BasisValid Γ b) (hsb : Basis.IsTyBasis b)
    (htof : Basis.tof b = τ) :
    ∃ v, ValExpr.OpStep Ψ e b v := by
  -- the environment is std-complete (P7 telescope lift)
  have hstd : StdComplete Ψ := stdComplete_of_ctxTele htele

  obtain ⟨v₁, hv₁⟩ := progress_std hwfΔΓ hwfΨ hwflc hanch hΓΨ hstd htype
  -- the type is valid (regularity through the basis: BasisValid carries it)
  obtain ⟨k, ⟨hTV⟩⟩ := hb.tof_tvalid
  rw [htof] at hTV

  exact basis_transport Γ Ψ e (Basis.std τ) b v₁
    (pCarrier_of hwfΨ hwflc hanch hstd)
    (varsCovered_of hΓΨ).drop_lin
    htele.storedWF
    (Basis.std_valid _ hTV) (Basis.isTyBasis_std τ)
    hb hsb
    (by rw [htof, Basis.tof_std])
    hv₁

end GLang.V2
