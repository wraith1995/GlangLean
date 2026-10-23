import GLang.Proofs.Adequacy.Compatibility

namespace GLang
namespace Adequacy

/-- Canonical higher-order value agreement.  At a dependent function it
tracks the actual runtime argument and the caller/callee basis frame. -/
noncomputable abbrev Agree := GLang.Agree

/-- Canonical agreement for an exception-carrying evaluator result. -/
abbrev ResultAgree := GLang.ResultAgree

/-- Canonical dimension agreement at an explicit basis denotation. -/
noncomputable abbrev AgreeDimsAt := GLang.AgreeDimsAt

/-- The ordinary dimension-agreement name is intentionally basis-indexed. -/
noncomputable abbrev AgreeDims := GLang.AgreeDims

/-- Canonical consistency of the source, operational, value, and denotational
environments. -/
abbrev Consistent := GLang.Consistent

/-- Recursive semantic soundness of an exact basis denotation.  At a space it
is the ordinary list-basis property; at a dependent function it covers both
the domain basis and every source-indexed codomain fiber. -/
noncomputable abbrev BasisAt := GLang.RawBasisAt

/-- The oracle package required by the completed, basis-indexed adequacy
theorem.  The oracle abstraction remains an explicit boundary. -/
abbrev OracleSpec := RawApplicationOracleSpec

namespace Agree

/-- A canonically agreeing value decodes at its recorded value type. -/
theorem toEl {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot} {x : DVal}
    {y : ValValSem}
    (h : Adequacy.Agree orc sigma rho Ds Gv Dv tau tauv B x y) :
    exists a : (denotValTyS orc rho Gv Dv tauv).El,
      ValValSem.toEl (denotValTyS orc rho Gv Dv tauv) y = .ok a :=
  GLang.Agree.toEl h

end Agree

namespace ResultAgree

/-- Adequacy produces a successful evaluator payload. -/
theorem isOk {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot} {x : DVal}
    {r : Except DimError ValValSem}
    (h : Adequacy.ResultAgree orc sigma rho Ds Gv Dv tau tauv B x r) :
    exists y, r = .ok y :=
  GLang.ResultAgree.isOk h

/-- In particular, adequacy excludes every runtime dimension error. -/
theorem ne_error {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot} {x : DVal}
    {r : Except DimError ValValSem}
    (h : Adequacy.ResultAgree orc sigma rho Ds Gv Dv tau tauv B x r)
    (err : DimError) : r ≠ .error err :=
  GLang.ResultAgree.ne_error h err

end ResultAgree

/-- Every valid syntactic basis denotes a recursively sound exact semantic
basis.  This fact is independent of the value oracle and operational
environment; only source-context and source-environment well-formedness are
needed. -/
theorem basisAt
    {sigma : DEnv} {Gamma : NLCtx} {b : Basis}
    (hvalid : Basis.BasisValid Gamma b)
    (hctx : CtxWF ∅ Gamma)
    (henv : EnvWF sigma ∅ Gamma) :
    BasisAt sigma [] (Basis.tof b) (denotBasis sigma b) :=
  rawBasisAtValidClaim_holds hvalid hctx henv

/-- Adequacy for strengthened space evaluation.  The compiled value-space
shape is exactly the source semantic shape.  FFS leaves are discharged by the
same completed direct-mutual term proof used by term adequacy. -/
theorem space (orc : FFSOracleSem) (hspec : OracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {sv : ValSpace}
    (h : S.Space Gamma Psi s sv) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      ValSpace.shpOf (orc rho [] []) sv = srcShp sigma [] s := by
  intro Delta sigma GammaV hconsistent
  let hterm : RawFullTermFactsProvider orc := by
    intro Delta0 Gamma0 Psi0 e b v tauV hS
    exact RawPublicCandidate.termFacts orc hspec hS
  have hspace : RawMSpaceSubctx orc Gamma Psi s sv :=
    (RawFullTermFactsProvider.toSpace hspec.toOracleSpec hterm) h
  exact hspace (EvalCtx.Subctx.refl Psi) rho Delta Gamma sigma GammaV
    (NLCtxIncl.refl Gamma) hconsistent

theorem termResult (orc : FFSOracleSem) (hspec : OracleSpec orc)
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (h : S.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      ResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) :=
  adequacy_term orc hspec h

/-- Canonical term adequacy.  The result agreement and its total dimension
witness are derived from the same strengthened term trace and exact realized
type, so higher-order agreement is not exposed without its reifiability
companion. -/
theorem term (orc : FFSOracleSem) (hspec : OracleSpec orc)
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (h : S.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      ResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (denotValB_semS orc rho [] [] v) /\
        AgreeDims orc sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) := by
  intro sigma GammaV hconsistent
  exact ⟨termResult orc hspec h sigma GammaV hconsistent,
    adequacy_dims orc hspec h.tyAt Delta sigma GammaV hconsistent⟩

/-- Adequacy for a strengthened change-of-basis evaluation. -/
theorem cob (orc : FFSOracleSem) (hspec : OracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (h : S.Cob Gamma Psi bSrc env bTgt) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      CobAgree orc sigma rho bSrc bTgt env :=
  adequacy_cob orc hspec h

/-- Dimension adequacy at the exact syntactic basis retained by `S.TyAt`.
The semantic basis is therefore correlated with the term/COB derivation. -/
theorem dimsAt (orc : FFSOracleSem) (hspec : OracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {tauV : ValTy}
    (h : S.TyAt Gamma Psi b tauV) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      AgreeDims orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) :=
  adequacy_dims orc hspec h

end Adequacy
end GLang
