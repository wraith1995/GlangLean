import GLang.Proofs.Adequacy.Partial.Source.PartialSourceTypedHistory
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceType
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceRepresentation
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyCore

namespace GLang.PartialAdequacy
open Basis (BasisValid)

structure TermTraceAt (orc : PartialFFSOracleSem) (sigma : DEnv)
    (rho : ValEnvSem) (e : ValExpr) (tau : Ty) (tauv : ValTy)
    (B : BasisDenot) (source : DVal) : Prop where
  result : ResultAgree orc sigma rho [] [] [] tau tauv B source
    (denotValB_partial orc rho [] [] e)
  dims : DimsAt orc sigma rho [] [] [] tau tauv B

/-- Exact-basis type motive, strengthened only by evaluator-context
monotonicity. -/
def MTyAtSubctx (orc : PartialFFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (b : Basis) (tauv : ValTy) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    MTyAt orc (TypedHistory orc) Gamma Psi' b tauv

/-- Current term motive.  It quantifies directly over every
larger evaluator context and source context, so an opened `nllam` body can be
invoked at the freshly extended current world without storing a separate
Kripke object. -/
def MTermSubctx (orc : PartialFFSOracleSem) (Delta : LCtx)
    (Gamma : NLCtx) (Psi : EvalCtx) (e : Term) (b : Basis)
    (v : ValExpr) (tauv : ValTy) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    Graded.CtxDisj Delta Gamma ->
    forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
      (sigma : DEnv) (GammaV : ValCtx),
      RawCtxIncl Delta Gamma Delta' Gamma' ->
      TypedHistory orc Delta' Gamma' Psi' GammaV sigma rho ->
      TermTraceAt orc sigma rho v (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)

def MDofSubctx (orc : PartialFFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (v : ValExpr) (tauV : ValTy) : Prop :=
  forall {sv : ValSpace}, tauV = .space sv ->
    forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
      (sigma : DEnv) (GammaV : ValCtx),
      NLCtxIncl Gamma Gamma' ->
      TypedHistory orc Delta' Gamma' Psi' GammaV sigma rho ->
      ValSpace.shpOfPartial (orc rho [] []) (ValExpr.inferSpaceCtx [] v) =
        ValSpace.shpOfPartial (orc rho [] []) sv

/-- The exact pair needed from each term induction hypothesis. -/
structure TermFactsSubctx (orc : PartialFFSOracleSem) (Delta : LCtx)
    (Gamma : NLCtx) (Psi : EvalCtx) (e : Term) (b : Basis)
    (v : ValExpr) (tauV : ValTy) : Prop where
  trace : MTermSubctx orc Delta Gamma Psi e b v tauV
  dof : MDofSubctx orc Gamma Psi v tauV

/-- Space adequacy stable under lookup-preserving evaluator-context extension. -/
def MSpaceSubctx (orc : PartialFFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (s : Space) (sv : ValSpace) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    MSpace orc (TypedHistory orc) Gamma Psi' s sv

/-- The space projection required by the exact-basis type induction. -/
def SpaceClaimSubctx (orc : PartialFFSOracleSem) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {s : Space} {sv : ValSpace},
    S.Space Gamma Psi s sv -> MSpaceSubctx orc Gamma Psi s sv

/-- Forget evaluator-context polymorphism at the current context. -/
theorem MSpaceSubctx.current
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {sv : ValSpace}
    (h : MSpaceSubctx orc Gamma Psi s sv) :
    MSpace orc (TypedHistory orc) Gamma Psi s sv :=
  h (EvalCtx.Subctx.refl Psi)

end GLang.PartialAdequacy
