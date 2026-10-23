import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMotives
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceFFS
import GLang.Proofs.Value.Queries.ValueQueryConstructors

namespace GLang.PartialAdequacy

theorem arm_space_real {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx} :
    MSpaceSubctx orc Gamma Psi .real .real := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  exact space_real

theorem arm_space_empty {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx} :
    MSpaceSubctx orc Gamma Psi .empty .empty := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  exact space_empty

theorem arm_space_dual {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {sv : ValSpace} (ih : MSpaceSubctx orc Gamma Psi s sv) :
    MSpaceSubctx orc Gamma Psi (.dual s) sv := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  exact space_dual (ih hsub rho Delta' Gamma' sigma GammaV hle hc)

theorem arm_space_tprod {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s t : Space} {sv tv : ValSpace}
    (ihs : MSpaceSubctx orc Gamma Psi s sv) (iht : MSpaceSubctx orc Gamma Psi t tv) :
    MSpaceSubctx orc Gamma Psi (.tprod s t) (.tprod sv tv) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  exact space_tprod (ihs hsub rho Delta' Gamma' sigma GammaV hle hc)
    (iht hsub rho Delta' Gamma' sigma GammaV hle hc)

theorem arm_space_dsum {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s t : Space} {sv tv : ValSpace}
    (ihs : MSpaceSubctx orc Gamma Psi s sv) (iht : MSpaceSubctx orc Gamma Psi t tv) :
    MSpaceSubctx orc Gamma Psi (.dsum s t) (.dsum sv tv) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  exact space_dsum (ihs hsub rho Delta' Gamma' sigma GammaV hle hc)
    (iht hsub rho Delta' Gamma' sigma GammaV hle hc)

/-- All four subspace constructors use the actually evaluated compiled matrix.
The context extension is arbitrary and the witness is taken from its term IH. -/
theorem arm_space_ffs
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space}
    {e : Term} {b : Basis} {v : ValExpr} {sv : ValSpace}
    (hb : Basis.sof b = .tprod (.dual s0) s1)
    (hcompat : Basis.FFSMatrixCompatible b)
    (he : S.Term ∅ Gamma Psi e b v (.space sv))
    (ihSpace : MSpaceSubctx PartialDirectOracle.oracle Gamma Psi (Basis.sof b) sv)
    (ihTerm : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi e b v (.space sv))
    (p : ValFFSProp) :
    MSpaceSubctx PartialDirectOracle.oracle Gamma Psi (fundamentalSpace p s0 s1 e)
      (.ffs p sv (ValExpr.reshapBase v sv)) := by
  have htof := hcompat.tof_eq_space
  obtain ⟨b0,b1,rfl⟩ := hcompat
  simp only [Basis.sof, Space.tprod.injEq, Space.dual.injEq] at hb
  obtain ⟨rfl,rfl⟩ := hb
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hshape := ihSpace hsub rho Delta' Gamma' sigma GammaV hle hc
  have hctx : RawCtxIncl ∅ Gamma Delta' Gamma' := ⟨by intro x s hx; simp at hx, hle⟩
  have ht := ihTerm.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hctx hc
  obtain ⟨hb0',hb1⟩ := he.basisValid.tprod_inv
  have hb0 := hb0'.dual_inv
  have hl0 := denotBasis_atSpace_isListBasis sigma Gamma' b0
    (raw_basisValid_mono hb0 hle) hc.ctxWF_nl hc.envWF_nl
  have hl1 := denotBasis_atSpace_isListBasis sigma Gamma' b1
    (raw_basisValid_mono hb1 hle) hc.ctxWF_nl hc.envWF_nl
  have hfType := hc.typeFinite (he.mono hsub).toEvalT
  have hfExpr := hc.exprFinite (he.mono hsub).toOpStep
  apply ffs_shape hl0 hl1 (by simpa only [Basis.sof] using hshape) ?_ p
    (hfType.space_inv.ffs (hfExpr.reshapBase hfType.space_inv))
  have hr := ht.result
  rw [htof] at hr
  have hr' := reshape_space hr
  obtain ⟨out,hout,ha⟩ := hr'
  refine ⟨out,hout,?_⟩
  cases out with
  | fn A f => simp only [Agree] at ha
  | array a =>
    simp only [Agree] at ha ⊢
    simpa only [Basis.sof, denotSpace, denotSpaceAux, BasisDenot.atSpace_vecs_self,
      RawSpaceFFS.denotBasis_tprod_dual_atSpace] using ha

end GLang.PartialAdequacy
