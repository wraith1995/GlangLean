import GLang.Proofs.Adequacy.Raw.RawAgreement
import GLang.Proofs.Progress.Supporting.ProgressStdBasis

/-!
# Exact-basis adequacy worlds

This module contains the consistency-independent interfaces used by the raw
adequacy redesign.  Keeping them below both `LegacyConsistent` and `Master` prevents
the dependent-function proof from creating an import cycle.

The central point is that the type claim is indexed by the syntactic basis
carried by `S.TyAt`.  It therefore asks for dimensions only at that basis's
denotation; there is no second, arbitrary basis and no representation-change
premise.
-/

namespace GLang

open Basis (BasisValid)

/-- The six environments threaded by an adequacy consistency telescope. -/
abbrev RawWorldPred :=
  LCtx -> NLCtx -> EvalCtx -> ValCtx -> DEnv -> ValEnvSem -> Prop

/-- A world predicate stores only locally closed evaluator-context entries.

This small capability keeps the consistency-independent type recursion
generic while exposing the exact fact needed to show that a realized binder
domain is locally closed. -/
def RawWorldLc (C : RawWorldPred) : Prop :=
  forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
      {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem},
    C Delta Gamma Psi GammaV sigma rho -> EvalCtxLc Psi

/-- Exact-basis type adequacy over an abstract consistency telescope. -/
def RawMTyAt (orc : FFSOracleSem) (C : RawWorldPred)
    (Gamma : NLCtx) (Psi : EvalCtx) (b : Basis) (tauv : ValTy) : Prop :=
  forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
    (sigma : DEnv) (GammaV : ValCtx),
    NLCtxIncl Gamma Gamma' -> C Delta' Gamma' Psi GammaV sigma rho ->
      RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b)

/-- Exact-raw nonlinear binder extension required by the `S.TyAt.frame` arm. -/
def RawWorldExtendNLAt (orc : FFSOracleSem) (C : RawWorldPred) : Prop :=
  forall {Delta : LCtx} {Gamma0 Gamma : NLCtx} {Psi : EvalCtx}
      {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem},
    C Delta Gamma Psi GammaV sigma rho ->
    NLCtxIncl Gamma0 Gamma ->
    forall {y : VName},
      (y ∉ Delta ∧ y ∉ Gamma ∧ forall b, (y, b) ∉ Psi) ->
    forall {b0 : Basis} {tauv0 : ValTy},
      BasisValid Gamma0 b0 ->
      Basis.IsTyBasis b0 ->
      S.TyAt Gamma0 Psi b0 tauv0 ->
    forall (x' : (denotTy sigma (Basis.tof b0)).El) (w : ValValSem),
      RawAgree orc sigma rho [] [] [] (Basis.tof b0) tauv0
          (denotBasis sigma b0)
          ((denotTy sigma (Basis.tof b0)).embed x') w ->
      RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b0) tauv0
          (denotBasis sigma b0) ->
      C Delta (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Finmap.insert y tauv0 GammaV)
        (sigma.bind y ((denotTy sigma (Basis.tof b0)).embed x'))
        (rho.update y w)

/-- Space part of the raw mutual motive.  A space realization is independent
of the enclosing basis, so its conclusion is only the source/value shape
identity. -/
def RawMSpace (orc : FFSOracleSem) (C : RawWorldPred)
    (Gamma : NLCtx) (Psi : EvalCtx) (s : Space) (sv : ValSpace) : Prop :=
  forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
    (sigma : DEnv) (GammaV : ValCtx),
    NLCtxIncl Gamma Gamma' -> C Delta' Gamma' Psi GammaV sigma rho ->
      ValSpace.shpOf (orc rho [] []) sv = srcShp sigma [] s

/-- The sibling space conclusion consumed by the exact `S.TyAt` induction. -/
def RawSpaceClaim (orc : FFSOracleSem) (C : RawWorldPred) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {s : Space} {sv : ValSpace},
    S.Space Gamma Psi s sv -> RawMSpace orc C Gamma Psi s sv

end GLang
