

import GLang.Proofs.Progress.Supporting.ProgressTele
import GLang.Proofs.Progress.Supporting.ProgressTransport

namespace GLang.V2

/-- **The Π-entry conversion** (P7a's pinned `PiEntryTransport`): a freshly
    telescoped variable stored at a frame key evaluates at the literal
    standard frame basis. Gap-1 `TransportN`: carrier facts at the PREFIX,
    the `OpStep.var` evaluation at the extended context, transported
    `.frame b₀ b₁ → Basis.std (tof (.frame b₀ b₁))` across the `ExtBy`
    step. The entry's value/fv/realization clauses are not needed beyond
    `lc` (the `ExtBy` side condition). -/
theorem pi_entry_transport : PiEntryTransport := by
  intro Γ Ψ x b₀ b₁ v hP hcov hsw hbv hty hfresh _hfvb _hev _hfvv hlcv _hanchv
  have hvar : ValExpr.OpStep (EvalCtx.extend Ψ x (.frame b₀ b₁) v)
      (.var x) (.frame b₀ b₁) v :=
    .var (by rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert])
  obtain ⟨k, ⟨hTV⟩⟩ := hbv.tof_tvalid
  exact transportN (Ty.size (Basis.tof (.frame b₀ b₁))) Γ Ψ _ (.var x)
    (.frame b₀ b₁) (Basis.std (Basis.tof (.frame b₀ b₁))) v
    hP hcov hsw (.step (.refl _) hfresh hlcv)
    hbv hty (Basis.std_valid _ hTV) (Basis.isTyBasis_std _)
    (Basis.tof_std _) le_rfl hvar

theorem stdComplete_of_ctxTele {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    (htele : CtxTele Δ Γ Ψ) : StdComplete Ψ :=
  stdComplete_of_tele pi_entry_transport htele

theorem progress_cob
    {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {b : Basis} {s : Space}
    (htele : CtxTele Δ Γ Ψ)
    (hwfΔΓ : CtxWF' Δ Γ) (hwfΨ : EvalCtxValid Ψ) (hwflc : EvalCtxLc Ψ)
    (hanch : EvalCtxLamAnchored Ψ) (hΓΨ : TypingImplyEval Δ Γ Ψ)
    (hb : Basis.BasisValid Γ b) (hsb : Basis.IsSpaceBasis b)
    (htof : Basis.tof b = .space s) :
    ∃ env, Basis.EvalBB Ψ b env (Basis.std (Basis.tof b)) :=
  progress_cob_of_transport basis_transport pi_entry_transport htele
    hwfΔΓ hwfΨ hwflc hanch hΓΨ hb hsb htof

end GLang.V2
