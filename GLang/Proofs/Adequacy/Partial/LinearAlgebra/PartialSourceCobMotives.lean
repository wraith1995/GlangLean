import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMotives
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCobProducts

namespace GLang.PartialAdequacy

/-- Claim (2) over raw consistency, stable under evaluator-context extension. -/
def MCobSubctx (orc : PartialFFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (bSrc : Basis) (env : ValExpr) (bTgt : Basis) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
      (sigma : DEnv) (GammaV : ValCtx),
      NLCtxIncl Gamma Gamma' ->
      TypedHistory orc Delta' Gamma' Psi' GammaV sigma rho ->
      CobAgree orc sigma rho bSrc bTgt env

/-- Syntactic matrix-shape information paired with raw COB adequacy. -/
def CobInferSubctx (orc : PartialFFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (env : ValExpr) (b : Basis) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
      (sigma : DEnv) (GammaV : ValCtx),
      NLCtxIncl Gamma Gamma' ->
      TypedHistory orc Delta' Gamma' Psi' GammaV sigma rho ->
      exists sa sb,
        ValExpr.inferSpaceCtx [] env = .tprod sa sb /\
        ValSpace.dofPartial (orc rho [] []) sa =
          .ok ((denotBasis sigma b).atSpace
            (denotSpace sigma (Basis.sof b))).length /\
        ValSpace.dofPartial (orc rho [] []) sb =
          .ok ((denotBasis sigma b).atSpace
            (denotSpace sigma (Basis.sof b))).length

/-- The pair produced by each `S.Cob` constructor in the direct mutual proof. -/
structure CobFactsSubctx (orc : PartialFFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (bSrc : Basis) (env : ValExpr) (bTgt : Basis) : Prop where
  agree : MCobSubctx orc Gamma Psi bSrc env bTgt
  infer : CobInferSubctx orc Gamma Psi env bSrc

end GLang.PartialAdequacy
