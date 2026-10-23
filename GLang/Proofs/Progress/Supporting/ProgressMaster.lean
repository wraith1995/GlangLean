

import GLang.Proofs.Progress.Supporting.Progress_F1
import GLang.Proofs.Progress.Supporting.Progress_F2
import GLang.Proofs.Progress.Supporting.Progress_F3
import GLang.Proofs.Progress.Supporting.Progress_F4
import GLang.Proofs.Progress.Supporting.Progress_F5
import GLang.Proofs.Progress.Supporting.Progress_F6

set_option maxHeartbeats 1000000

namespace GLang.V2

/-- **The progress master induction** — all four judgments at once, under the
    `PCarrier`/`VarsCovered` hypotheses (std-complete environment). One
    recursor application per entry point, every minor premise a bare
    `progress_arm_*` helper. -/
theorem progress_master_std :
    (∀ {Γ : NLCtx} {s : Space}, SValid Γ s → pMotiveS Γ s)
  ∧ (∀ {Γ : NLCtx} {τ : Ty} {k : Kind}, TValid Γ τ k → pMotiveT Γ τ)
  ∧ (∀ {Γ : NLCtx} {s₀ s₁ : Space}, SubType Γ s₀ s₁ → pMotiveSub Γ s₀ s₁)
  ∧ (∀ {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty},
        HasType Δ Γ e τ → pMotiveH Δ Γ e τ) := by
  refine ⟨@fun Γ s h => ?_, @fun Γ τ k h => ?_,
          @fun Γ s₀ s₁ h => ?_, @fun Δ Γ e τ h => ?_⟩
  all_goals
    exact h.rec
      (motive_1 := fun Γ' s' _ => pMotiveS Γ' s')
      (motive_2 := fun Γ' τ' _k _ => pMotiveT Γ' τ')
      (motive_3 := fun Γ' s₀' s₁' _ => pMotiveSub Γ' s₀' s₁')
      (motive_4 := fun Δ' Γ' e' τ' _ => pMotiveH Δ' Γ' e' τ')
      -- SValid (9)
      progress_arm_empty progress_arm_real progress_arm_dual progress_arm_dsum
      progress_arm_tprod progress_arm_ker progress_arm_coker progress_arm_img
      progress_arm_coimg
      -- TValid (2)
      progress_arm_space progress_arm_piTy
      -- SubType (4)
      progress_arm_sub_ker progress_arm_sub_coker progress_arm_sub_img
      progress_arm_sub_coimg
      -- HasType (19)
      progress_arm_zero progress_arm_smul progress_arm_add progress_arm_inner
      progress_arm_real_lit progress_arm_app_linear progress_arm_app_inner
      progress_arm_app_nonlinear progress_arm_var_lin progress_arm_var_nlin
      progress_arm_pinv_tensor progress_arm_pinv_dual progress_arm_promote
      progress_arm_dsumE progress_arm_tprodE progress_arm_llam_real
      progress_arm_llam_tensor progress_arm_embed progress_arm_nllam

theorem progress_std
    {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty}
    (hwfΔΓ : CtxWF' Δ Γ) (hwfΨ : EvalCtxValid Ψ) (hwflc : EvalCtxLc Ψ)
    (hanch : EvalCtxLamAnchored Ψ) (hΓΨ : TypingImplyEval Δ Γ Ψ)
    (hstd : StdComplete Ψ)
    (htype : HasType Δ Γ e τ) :
    ∃ v, ValExpr.OpStep Ψ e (Basis.std τ) v :=
  (progress_master_std.2.2.2 htype Ψ
    (pCarrier_of hwfΨ hwflc hanch hstd) (varsCovered_of hΓΨ)).1

end GLang.V2
