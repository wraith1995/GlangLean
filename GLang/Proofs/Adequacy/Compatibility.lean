import GLang.Proofs.Adequacy.Raw.Conversion.RawCobDirectMutualMaster
import GLang.Proofs.Adequacy.Raw.Context.RawProviders
import GLang.Proofs.Adequacy.Raw.RawReification

/-! Specializations of mutual adequacy to the current world, with term, change-of-basis, and dimension results under `RawConsistent`. -/

namespace GLang

namespace RawPublicCandidate

theorem termFacts (orc : FFSOracleSem)
    (hspec : RawApplicationOracleSpec orc)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {e : Term}
    {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hS : S.Term Delta Gamma Psi e b v tauV) :
    RawTermDofFactsSubctx orc Delta Gamma Psi e b v tauV :=
  hS.rawDirectMutualMaster hspec

/-- Term adequacy, specialized to the current
world.  Future-world and context-inclusion premises of the raw motive are
discharged internally. -/
theorem term (orc : FFSOracleSem) (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hS : S.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho ->
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) := by
  intro sigma GammaV hc
  exact ((termFacts orc hspec hS).trace
    (EvalCtx.Subctx.refl Psi) hc.raw.ctxWF_raw.disjoint
    rho Delta Gamma sigma GammaV
    ⟨(fun _ _ hlookup => Or.inl hlookup), NLCtxIncl.refl Gamma⟩ hc).result

private theorem fullTermProvider (orc : FFSOracleSem)
    (hspec : RawApplicationOracleSpec orc) :
    RawFullTermFactsProvider orc := by
  intro Delta Gamma Psi e b v tauV hS
  exact termFacts orc hspec hS

/-- The raw dimension equality produced directly by the completed mutual
proof.  This lighter internal theorem remains available to implementation
modules that do not need the public non-vacuity package. -/
theorem rawDimsAt (orc : FFSOracleSem) (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {tauV : ValTy} (hS : S.TyAt Gamma Psi b tauV) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho ->
      RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) := by
  intro Delta sigma GammaV hc
  exact (RawFullTermFactsProvider.toTyAt hspec
    (fullTermProvider orc hspec) hS
    (EvalCtx.Subctx.refl Psi)) rho Delta Gamma sigma GammaV
    (NLCtxIncl.refl Gamma) hc

/-- Basis-indexed dimension adequacy.  In addition to
the raw recursive equality, the result proves that every source element has a
runtime representative and that a representative identifies its source. -/
theorem dimsAt (orc : FFSOracleSem) (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {tauV : ValTy} (hS : S.TyAt Gamma Psi b tauV) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho ->
      AgreeDimsAt orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) := by
  intro Delta sigma GammaV hc
  have hd := rawDimsAt orc hspec hS Delta sigma GammaV hc
  have hB : RawBasisAt sigma [] (Basis.tof b) (denotBasis sigma b) :=
    rawBasisAtValidClaim_holds hS.basisValid hc.ctxWF_nl hc.envWF_nl
  exact AgreeDimsAt.ofRaw orc hB hd

theorem cobFacts (orc : FFSOracleSem)
    (hspec : RawApplicationOracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {bSrc bTgt : Basis} {env : ValExpr}
    (hS : S.Cob Gamma Psi bSrc env bTgt) :
    RawCobFactsSubctx orc Gamma Psi bSrc env bTgt :=
  hS.rawDirectMutualMaster hspec

/-- Change-of-basis adequacy.  This theorem needs no separately supplied `RawCobAgreeProvider`: the
arbitrary-root mutual assembly constructs agreement and inference together. -/
theorem cob (orc : FFSOracleSem)
    (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (hS : S.Cob Gamma Psi bSrc env bTgt) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho ->
      CobAgree orc sigma rho bSrc bTgt env := by
  intro Delta sigma GammaV hc
  exact ((cobFacts orc hspec hS).agree (EvalCtx.Subctx.refl Psi))
    rho Delta Gamma sigma GammaV (NLCtxIncl.refl Gamma) hc

end RawPublicCandidate

/-! Global term, change-of-basis, and basis-indexed dimension adequacy. -/

/-- Public term adequacy, backed by the raw direct-mutual proof. -/
theorem adequacy_term (orc : FFSOracleSem)
    (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hS : S.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      ResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) :=
  RawPublicCandidate.term orc hspec hS

/-- Public change-of-basis adequacy, backed by the raw COB proof. -/
theorem adequacy_cob (orc : FFSOracleSem)
    (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (hS : S.Cob Gamma Psi bSrc env bTgt) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      CobAgree orc sigma rho bSrc bTgt env :=
  RawPublicCandidate.cob orc hspec hS

/-- Public exact-basis dimension adequacy. -/
theorem adequacy_dims (orc : FFSOracleSem)
    (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {tauV : ValTy}
    (hS : S.TyAt Gamma Psi b tauV) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      AgreeDims orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) :=
  RawPublicCandidate.dimsAt orc hspec hS

end GLang
