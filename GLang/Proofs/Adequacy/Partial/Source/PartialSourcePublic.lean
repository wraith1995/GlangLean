import GLang.Proofs.Adequacy.Partial.Source.PartialSourceRoots
import GLang.Operational.Supporting.Operational

/-! Public source adequacy for the actual partial evaluator. The operational
trace and the evaluated expression are the same selected output. -/
namespace GLang.Adequacy.PartialDirect

abbrev Consistent := PartialAdequacy.Consistent PartialDirectOracle.oracle
abbrev ResultAgree := PartialAdequacy.ResultAgree PartialDirectOracle.oracle
abbrev AgreeDims := PartialAdequacy.DimsAt PartialDirectOracle.oracle
abbrev CobAgree := PartialAdequacy.CobAgree PartialDirectOracle.oracle
noncomputable abbrev evalVal := denotValB_partial PartialDirectOracle.oracle

/-- The semantic telescope erases to the semantic-free checked progress input. -/
theorem contextHistory
    (h : Consistent Delta Gamma Psi GammaV sigma rho) :
    Operational.ContextHistory Delta Gamma GammaV Psi :=
  h.context

/-- Adequacy of one exact checked term result, including higher-order results. -/
theorem term
    (h : Operational.Term Delta Gamma Psi e b v tauV)
    (sigma : DEnv) (GammaV : ValCtx)
    (hc : Consistent Delta Gamma Psi GammaV sigma rho) :
    ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
      (denotBasis sigma b) (denotTerm sigma e) (evalVal rho [] [] v) ∧
    AgreeDims sigma rho [] [] [] (Basis.tof b) tauV (denotBasis sigma b) := by
  have tr := (PartialAdequacy.term_mutual h.toStrengthened).trace
    (EvalCtx.Subctx.refl Psi)
    (RawCertifiedCtxTeleProgress.ctxWFPrime hc.history.ctxTele).disjoint
    rho Delta Gamma sigma GammaV
    ⟨fun _ _ hx => Or.inl hx, NLCtxIncl.refl Gamma⟩ hc.typedHistory
  exact ⟨tr.result,tr.dims⟩

theorem space
    (h : Operational.Space Gamma Psi s sv)
    (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx)
    (hc : Consistent Delta Gamma Psi GammaV sigma rho) :
    ValSpace.shpOfPartial (PartialDirectOracle.oracle rho [] []) sv =
      .ok (srcShp sigma [] s) :=
  PartialAdequacy.space_mutual h.toStrengthened (EvalCtx.Subctx.refl Psi)
    rho Delta Gamma sigma GammaV (NLCtxIncl.refl Gamma) hc.typedHistory

/-- Exact-basis recursive dimension agreement. -/
theorem typeAt
    (h : Operational.TyAt Gamma Psi b tauV)
    (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx)
    (hc : Consistent Delta Gamma Psi GammaV sigma rho) :
    AgreeDims sigma rho [] [] [] (Basis.tof b) tauV (denotBasis sigma b) :=
  PartialAdequacy.typeAt_mutual h.toStrengthened (EvalCtx.Subctx.refl Psi)
    rho Delta Gamma sigma GammaV (NLCtxIncl.refl Gamma) hc.typedHistory

/-- Matrix agreement includes successful evaluation and complete array length. -/
theorem cob
    (h : Operational.Cob Gamma Psi bSrc env bTgt)
    (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx)
    (hc : Consistent Delta Gamma Psi GammaV sigma rho) :
    CobAgree sigma rho bSrc bTgt env :=
  (PartialAdequacy.cob_mutual h.toStrengthened).agree (EvalCtx.Subctx.refl Psi)
    rho Delta Gamma sigma GammaV (NLCtxIncl.refl Gamma) hc.typedHistory

end GLang.Adequacy.PartialDirect
