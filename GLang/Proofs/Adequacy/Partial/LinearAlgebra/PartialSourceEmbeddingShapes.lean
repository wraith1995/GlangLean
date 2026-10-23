import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourcePinvConstructors
import GLang.Proofs.Value.Queries.ValueQueryConstructors

namespace GLang.PartialAdequacy

/-- Inferred canonical-column dimensions agree with the explicit tensor
annotation, including its successful witness reshape. -/
theorem canonical_output_shape {rho : ValEnvSem} {e g h : ValExpr}
    {a : FlatArray} {sa sb s0 s1 : ValSpace} {m n : Nat} (p : ValFFSProp)
    (he : denotValB_partial PartialDirectOracle.oracle rho [] [] e = .ok (.array a))
    (hinfer : ValExpr.inferSpaceCtx [] e = .tprod sa sb)
    (ha : sa.dofPartial (PartialDirectOracle.oracle rho [] []) = .ok m)
    (hb : sb.dofPartial (PartialDirectOracle.oracle rho [] []) = .ok n)
    (h0 : s0.dofPartial (PartialDirectOracle.oracle rho [] []) = .ok m)
    (h1 : s1.dofPartial (PartialDirectOracle.oracle rho [] []) = .ok n)
    (hlen : a.length = m*n)
    (hfe : ValueQueryDependencies.Finite (.expr [] e))
    (hfs : ValueQueryDependencies.Finite (.space [] (.tprod s0 s1))) :
    (ValExpr.inferSpaceCtx [] (.vtrans (.canonicalFSV p e g h))).shpOfPartial
      (PartialDirectOracle.oracle rho [] []) =
      (ValSpace.tprod (.ffs p (.tprod s0 s1) (ValExpr.reshapBase e (.tprod s0 s1)))
        (p.ambient s0 s1)).shpOfPartial (PartialDirectOracle.oracle rho [] []) := by
  have hs0 : (.tprod sa sb : ValSpace).shpOfPartial (PartialDirectOracle.oracle rho [] []) =
      .ok [m,n] := by simp [ValSpace.shpOfPartial,ha,hb,bind,Except.bind,pure,Except.pure]
  have hs1 : (.tprod s0 s1 : ValSpace).shpOfPartial (PartialDirectOracle.oracle rho [] []) =
      .ok [m,n] := by simp [ValSpace.shpOfPartial,h0,h1,bind,Except.bind,pure,Except.pure]
  have hr : denotValB_partial PartialDirectOracle.oracle rho [] []
      (ValExpr.reshapBase e (.tprod s0 s1)) = .ok (.array a) := by
    rw [ValExpr.reshapBase,denotValB_partial,he]
    simp [PartialValueEval.reshapeInferred,PartialValueEval.reshapeBetween,PartialValueEval.reshapeArray,
      dof_tprod_ok h0 h1,hlen]
  have q0 := PartialDirectLocality.oracle_matrix rho [] [] p (.tprod sa sb) e m n a ((hinfer ▸ hfe.inferSpace).ffs hfe) hs0 he hlen
  have q1 := PartialDirectLocality.oracle_matrix rho [] [] p (.tprod s0 s1)
    (ValExpr.reshapBase e (.tprod s0 s1)) m n a (hfs.ffs (hfe.reshapBase hfs)) hs1 hr hlen
  have hf0 : (.ffs p (.tprod sa sb) e : ValSpace).dofPartial
      (PartialDirectOracle.oracle rho [] []) =
      .ok (ffsDim p [m,n] (denotAsMatrix m n a.get).rank) := by
    simp [ValSpace.dofPartial,ValSpace.shpOfPartial,q0,bind,Except.bind,pure,Except.pure]
  have hf1 : (.ffs p (.tprod s0 s1) (ValExpr.reshapBase e (.tprod s0 s1)) : ValSpace).dofPartial
      (PartialDirectOracle.oracle rho [] []) =
      .ok (ffsDim p [m,n] (denotAsMatrix m n a.get).rank) := by
    simp [ValSpace.dofPartial,ValSpace.shpOfPartial,q1,bind,Except.bind,pure,Except.pure]
  cases p <;> simp only [ValExpr.canonicalFSV, ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient,ValSpace.shpOfPartial,hf0,hf1,ha,hb,h0,h1]

theorem embedding_dof {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {e : Term} {v g h : ValExpr} {sv0 sv1 : ValSpace} (p : ValFFSProp)
    (heTrace : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1)))
    (ihE : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    MDofSubctx PartialDirectOracle.oracle Gamma Psi
      (.vtrans (.canonicalFSV p v g h))
      (.space (.tprod (.ffs p (.tprod sv0 sv1) (ValExpr.reshapBase v (.tprod sv0 sv1)))
        (p.ambient sv0 sv1))) := by
  intro sv hsv Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hsv
  have hle' : RawCtxIncl ∅ Gamma Delta' Gamma' := ⟨by intro x t hx; simp at hx,hle⟩
  have tr := ihE.trace hsub (Graded.CtxDisj.empty Gamma) rho Delta' Gamma' sigma GammaV hle' hc
  have hs : (.tprod sv0 sv1 : ValSpace).shpOfPartial (PartialDirectOracle.oracle rho [] []) =
      .ok [Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual] using tr.dims
  obtain ⟨h0,h1⟩ := tprod_shape_factors hs
  have hi := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [hs] at hi
  obtain ⟨sa,sb,hinfer,ha,hb⟩ := infer_tprod_of_partial_shape hi
  obtain ⟨v',he,hagree⟩ := tr.result
  obtain ⟨a,n,rfl,hd,_,hlen,_⟩ := hagree.array
  have hn := Except.ok.inj (hd.symm.trans (dof_tprod_ok h0 h1))
  rw [hn] at hlen
  exact canonical_output_shape p he hinfer ha hb h0 h1 hlen
    (hc.exprFinite (heTrace.mono hsub).toOpStep)
    (hc.typeFinite (heTrace.mono hsub).toEvalT).space_inv

end GLang.PartialAdequacy
