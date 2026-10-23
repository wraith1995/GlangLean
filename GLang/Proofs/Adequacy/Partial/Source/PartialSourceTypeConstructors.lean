import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMotives

namespace GLang.PartialAdequacy

/-- The space-valued exact-basis type arm consumes its particular sibling
space IH; it does not require an external global space theorem. -/
theorem arm_tyAt_space
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {sv : ValSpace}
    (htof : Basis.tof b = .space (Basis.sof b))
    (_hbv : Basis.BasisValid Gamma b)
    (_hs : S.Space Gamma Psi (Basis.sof b) sv)
    (ihSpace : MSpaceSubctx orc Gamma Psi (Basis.sof b) sv) :
    MTyAtSubctx orc Gamma Psi b (.space sv) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [htof]
  simpa only [DimsAt] using
    ihSpace hsub rho Delta' Gamma' sigma GammaV hle hc

/-- The dependent-frame exact-basis arm follows the same concrete frame basis
after every evaluator-context extension. -/
theorem arm_tyAt_frame
    {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    (hpush : PartialDirectOpenPush.OracleOpenPush orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {tauV0 tauV1 : ValTy}
    (hbv : Basis.BasisValid Gamma (.frame b0 b1))
    (hdom : S.TyAt Gamma Psi b0 tauV0)
    (L : Finset Name)
    (hcod : forall y, y ∉ L ->
      S.TyAt (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauV0))
        (Basis.openVar y b1) (ValTy.openVar y tauV0 tauV1))
    (hisTy : Basis.IsTyBasis (.frame b0 b1))
    (ihdom : MTyAtSubctx orc Gamma Psi b0 tauV0)
    (ihcod : forall y, y ∉ L ->
      MTyAtSubctx orc
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauV0))
        (Basis.openVar y b1) (ValTy.openVar y tauV0 tauV1)) :
    MTyAtSubctx orc Gamma Psi (.frame b0 b1)
      (.piTy tauV0 tauV1) := by
  intro Psi' hsub
  exact mTyAt_frame
    (TypedHistory.worldExtendNLAt hirr)
    (fun hc => hc.evalCtxLc)
    hpush hbv (hdom.mono hsub) L
    (fun y hy => (hcod y hy).mono (hsub.extend y b0 (.var y tauV0)))
    hisTy
    (ihdom hsub)
    (fun y hy => ihcod y hy (hsub.extend y b0 (.var y tauV0)))

end GLang.PartialAdequacy
