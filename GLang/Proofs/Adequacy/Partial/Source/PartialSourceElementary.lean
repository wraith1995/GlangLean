import GLang.Proofs.Adequacy.Partial.Source.PartialSourceWellFormed
import GLang.Proofs.Adequacy.Partial.Source.PartialSourcePrimitiveTransport
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceFFS

namespace GLang.PartialAdequacy
open Basis (BasisValid)
open scoped TensorProduct

private theorem dof_eq_of_shape_eq {q : PartialFFSOracle} {s t : ValSpace}
    (h : s.shpOfPartial q = t.shpOfPartial q) : s.dofPartial q = t.dofPartial q := by
  simp only [ValSpace.dofPartial,h]

theorem arm_add
    {orc : PartialFFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e0 e1 : Term} {b : Basis} {v0 v1 : ValExpr}
    {sv sv0 sv1 : ValSpace}
    (htof : Basis.tof b = .space (Basis.sof b))
    (_ht : Nonempty (HasType Delta Gamma (.add e0 e1) (Basis.tof b)))
    (hbv : BasisValid Gamma b)
    (_hTy : S.TyAt Gamma Psi b (.space sv))
    (he0 : S.Term Delta Gamma Psi e0 b v0 (.space sv0))
    (he1 : S.Term Delta Gamma Psi e1 b v1 (.space sv1))
    (ihTy : MTyAtSubctx orc Gamma Psi b (.space sv))
    (ih0 : MTermSubctx orc Delta Gamma Psi
      e0 b v0 (.space sv0))
    (ih1 : MTermSubctx orc Delta Gamma Psi
      e1 b v1 (.space sv1)) :
    MTermSubctx orc Delta Gamma Psi (.add e0 e1) b
      (.vadd sv v0 v1) (.space sv) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have hd := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have h0 := (ih0 hsub hctx rho Delta' Gamma' sigma GammaV hle hc).result
  have h1 := (ih1 hsub hctx rho Delta' Gamma' sigma GammaV hle hc).result
  obtain ⟨x0,hx0⟩ := term_shape_at he0 htof hctx hle hc.history
  obtain ⟨x1,hx1⟩ := term_shape_at he1 htof hctx hle hc.history
  have hb := denotBasis_atSpace_isListBasis sigma Gamma' b
    (raw_basisValid_mono hbv hle.2) hc.ctxWF_nl hc.envWF_nl
  refine ⟨?_,hd⟩
  rw [htof] at h0 h1 ⊢
  have hs : sv.shpOfPartial (orc rho [] []) = .ok (srcShp sigma [] (Basis.sof b)) := by
    simpa only [htof,DimsAt] using hd
  exact add (shape_dof hs) hb.finrank_eq.symm
    (by change (denotTerm sigma e0).matchesShape _; rw [hx0]; exact DVal.matchesShape_hil_rfl _ _)
    (by change (denotTerm sigma e1).matchesShape _; rw [hx1]; exact DVal.matchesShape_hil_rfl _ _) h0 h1

theorem arm_zero
    {orc : PartialFFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {sv : ValSpace}
    (htof : Basis.tof b = .space (Basis.sof b))
    (_ht : Nonempty
      (HasType Delta Gamma (.zero (Basis.sof b)) (Basis.tof b)))
    (hbv : BasisValid Gamma b)
    (_hTy : S.TyAt Gamma Psi b (.space sv))
    (_hsv : S.Space Gamma Psi (Basis.sof b) sv)
    (ihTy : MTyAtSubctx orc Gamma Psi b (.space sv)) :
    MTermSubctx orc Delta Gamma Psi
      (.zero (Basis.sof b)) b (.zero sv) (.space sv) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have hd := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hb := denotBasis_atSpace_isListBasis sigma Gamma' b
    (raw_basisValid_mono hbv hle.2) hc.ctxWF_nl hc.envWF_nl
  refine ⟨?_,hd⟩
  rw [htof]
  have hs : sv.shpOfPartial (orc rho [] []) = .ok (srcShp sigma [] (Basis.sof b)) := by
    simpa only [htof,DimsAt] using hd
  exact zero (shape_dof hs) hb.finrank_eq.symm

theorem arm_rlit
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx} (r : ℝ)
    (_ht : Nonempty (HasType ∅ Gamma (.real r) (Basis.tof .one)))
    (_hTy : S.TyAt Gamma Psi .one (.space .real))
    (ihTy : MTyAtSubctx orc Gamma Psi .one (.space .real)) :
    MTermSubctx orc ∅ Gamma Psi
      (.real r) .one (.rlit r) (.space .real) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  refine ⟨?_,ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc⟩
  simpa only [Basis.tof,denotBasis,denotTerm,denotTermAux] using
    (real (orc := orc) (σ := sigma) (ρ := rho) (Ds := []) (Γ := []) (Δ := []) r)

theorem arm_scale
    {orc : PartialFFSOracleSem}
    {Delta0 Delta1 : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e0 e1 : Term} {b : Basis} {v0 v1 : ValExpr} {sv : ValSpace}
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (htof : Basis.tof b = .space (Basis.sof b))
    (_ht : Nonempty
      (HasType (Delta0 ∪ Delta1) Gamma (.smul e0 e1) (Basis.tof b)))
    (_hbv : BasisValid Gamma b)
    (hTy : S.TyAt Gamma Psi b (.space sv))
    (he0 : S.Term Delta0 Gamma Psi e0 .one v0 (.space .real))
    (he1 : S.Term Delta1 Gamma Psi e1 b v1 (.space sv))
    (ihTy : MTyAtSubctx orc Gamma Psi b (.space sv))
    (ih0 : MTermSubctx orc Delta0 Gamma Psi
      e0 .one v0 (.space .real))
    (ih1 : TermFactsSubctx orc Delta1 Gamma Psi
      e1 b v1 (.space sv)) :
    MTermSubctx orc (Delta0 ∪ Delta1) Gamma Psi
      (.smul e0 e1) b (.scale v0 v1) (.space sv) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have hle0 := RawCtxIncl.union_left hle
  have hle1 := RawCtxIncl.union_right hdisj hle
  have hc0 := Graded.CtxDisj.of_union_left hctx
  have hc1 := Graded.CtxDisj.of_union_right hctx
  have h0 := (ih0 hsub hc0 rho Delta' Gamma' sigma GammaV hle0 hc).result
  have h1 := (ih1.trace hsub hc1 rho Delta' Gamma' sigma GammaV hle1 hc).result
  obtain ⟨r,hr⟩ := term_shape_at he0 rfl hc0 hle0 hc.history
  obtain ⟨x,hx⟩ := term_shape_at he1 htof hc1 hle1 hc.history
  have hi := dof_eq_of_shape_eq (ih1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  refine ⟨?_,ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc⟩
  rw [htof,hx] at h1
  simp only [Basis.tof,denotBasis,hr] at h0
  have h := scale_of_dof hi h0 h1
  simp only [denotTerm] at hr hx
  rw [denotTerm, denotTermAux]
  rw [hr, hx]
  simpa only [htof,DVal.asHil,DVal.asReal,
    denotSpace,Basis.sof,denotSpaceAux,HSpace.real,dite_true] using h

theorem arm_dsumE
    {orc : PartialFFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e0 e1 : Term} {b0 b1 : Basis} {v0 v1 : ValExpr}
    {sv0 sv1 : ValSpace}
    (htof0 : Basis.tof b0 = .space (Basis.sof b0))
    (htof1 : Basis.tof b1 = .space (Basis.sof b1))
    (_ht : Nonempty
      (HasType Delta Gamma (.dsumE e0 e1)
        (Basis.tof (.dsum b0 b1))))
    (_hbv : BasisValid Gamma (.dsum b0 b1))
    (hTy : S.TyAt Gamma Psi (.dsum b0 b1)
      (.space (.dsum sv0 sv1)))
    (he0 : S.Term Delta Gamma Psi e0 b0 v0 (.space sv0))
    (he1 : S.Term Delta Gamma Psi e1 b1 v1 (.space sv1))
    (ihTy : MTyAtSubctx orc Gamma Psi (.dsum b0 b1)
      (.space (.dsum sv0 sv1)))
    (ih0 : TermFactsSubctx orc Delta Gamma Psi
      e0 b0 v0 (.space sv0))
    (ih1 : TermFactsSubctx orc Delta Gamma Psi
      e1 b1 v1 (.space sv1)) :
    MTermSubctx orc Delta Gamma Psi (.dsumE e0 e1)
      (.dsum b0 b1) (.dsumE v0 v1) (.space (.dsum sv0 sv1)) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have hle0 := hle
  have hle1 := hle
  have hc0 := hctx
  have hc1 := hctx
  have h0 := (ih0.trace hsub hc0 rho Delta' Gamma' sigma GammaV hle0 hc).result
  have h1 := (ih1.trace hsub hc1 rho Delta' Gamma' sigma GammaV hle1 hc).result
  obtain ⟨x0,hx0⟩ := term_shape_at he0 htof0 hc0 hle0 hc.history
  obtain ⟨x1,hx1⟩ := term_shape_at he1 htof1 hc1 hle1 hc.history
  have hi0 := dof_eq_of_shape_eq (ih0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have hi1 := dof_eq_of_shape_eq (ih1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  refine ⟨?_,ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc⟩
  rw [htof0,hx0] at h0
  rw [htof1,hx1] at h1
  have h := dsum_of_dof hi0 hi1 h0 h1
  simp only [denotTerm] at hx0 hx1
  rw [denotTerm, denotTermAux]
  rw [hx0, hx1]
  simpa only [Basis.tof,Basis.sof,denotBasis,
    DVal.asHil] using h

theorem arm_tprodE
    {orc : PartialFFSOracleSem}
    {Delta0 Delta1 : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e0 e1 : Term} {b0 b1 : Basis} {v0 v1 : ValExpr}
    {sv0 sv1 : ValSpace}
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (htof0 : Basis.tof b0 = .space (Basis.sof b0))
    (htof1 : Basis.tof b1 = .space (Basis.sof b1))
    (_ht : Nonempty
      (HasType (Delta0 ∪ Delta1) Gamma (.tprodE e0 e1)
        (Basis.tof (.tprod b0 b1))))
    (_hbv : BasisValid Gamma (.tprod b0 b1))
    (hTy : S.TyAt Gamma Psi (.tprod b0 b1)
      (.space (.tprod sv0 sv1)))
    (he0 : S.Term Delta0 Gamma Psi e0 b0 v0 (.space sv0))
    (he1 : S.Term Delta1 Gamma Psi e1 b1 v1 (.space sv1))
    (ihTy : MTyAtSubctx orc Gamma Psi (.tprod b0 b1)
      (.space (.tprod sv0 sv1)))
    (ih0 : TermFactsSubctx orc Delta0 Gamma Psi
      e0 b0 v0 (.space sv0))
    (ih1 : TermFactsSubctx orc Delta1 Gamma Psi
      e1 b1 v1 (.space sv1)) :
    MTermSubctx orc (Delta0 ∪ Delta1) Gamma Psi
      (.tprodE e0 e1) (.tprod b0 b1) (.tprodE v0 v1)
      (.space (.tprod sv0 sv1)) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have hle0 := RawCtxIncl.union_left hle
  have hle1 := RawCtxIncl.union_right hdisj hle
  have hc0 := Graded.CtxDisj.of_union_left hctx
  have hc1 := Graded.CtxDisj.of_union_right hctx
  have h0 := (ih0.trace hsub hc0 rho Delta' Gamma' sigma GammaV hle0 hc).result
  have h1 := (ih1.trace hsub hc1 rho Delta' Gamma' sigma GammaV hle1 hc).result
  obtain ⟨x0,hx0⟩ := term_shape_at he0 htof0 hc0 hle0 hc.history
  obtain ⟨x1,hx1⟩ := term_shape_at he1 htof1 hc1 hle1 hc.history
  have hi0 := dof_eq_of_shape_eq (ih0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have hi1 := dof_eq_of_shape_eq (ih1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  refine ⟨?_,ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc⟩
  rw [htof0,hx0] at h0
  rw [htof1,hx1] at h1
  have h := tprod_of_dof hi0 hi1 h0 h1
  simp only [denotTerm] at hx0 hx1
  rw [denotTerm, denotTermAux]
  rw [hx0, hx1]
  simpa only [Basis.tof,Basis.sof,denotBasis,
    DVal.asHil] using h

end GLang.PartialAdequacy
