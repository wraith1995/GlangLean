import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourcePinv
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMotives

namespace GLang.PartialAdequacy
open Basis (BasisValid)
open PartialValueEval

private theorem std_real_basis_eq_one
    {Gamma : NLCtx} {b : Basis} (hb : BasisValid Gamma b)
    (hstd : Basis.isStd b) (hsof : Basis.sof b = .real) : b = .one := by
  cases hb <;> simp_all [Basis.sof,Basis.isStd]

/-- Successful tensor shape observations expose both successful factors. -/
theorem tprod_shape_factors {q : PartialFFSOracle} {s t : ValSpace} {m n : Nat}
    (h : ValSpace.shpOfPartial q (.tprod s t) = .ok [m,n]) :
    s.dofPartial q = .ok m ∧ t.dofPartial q = .ok n := by
  cases hs : s.dofPartial q <;> cases ht : t.dofPartial q <;>
    simp [ValSpace.shpOfPartial,hs,ht,bind,Except.bind,pure,Except.pure] at h
  obtain ⟨rfl,rfl⟩ := h
  exact ⟨rfl,rfl⟩

theorem infer_tprod_of_partial_shape {q : PartialFFSOracle} {s : ValSpace} {m n : Nat}
    (h : s.shpOfPartial q = .ok [m,n]) :
    ∃ a b, s = .tprod a b ∧ a.dofPartial q = .ok m ∧ b.dofPartial q = .ok n := by
  have htotal := ValSpace.shpOfPartial_success q (numbers q) (numbers_ok q) s _ h
  cases s with
  | tprod a b => exact ⟨a,b,rfl,tprod_shape_factors h⟩
  | empty => simp [ValSpace.shpOf] at htotal
  | real => simp [ValSpace.shpOf] at htotal
  | dsum a b => simp [ValSpace.shpOf] at htotal
  | ffs p s e => simp [ValSpace.shpOf] at htotal

theorem arm_pinvT_std
    {orc : PartialFFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v : ValExpr}
    {sv0 sv1 : ValSpace}
    (hb0std : Basis.isStd b0) (hb1std : Basis.isStd b1)
    (_ht : Nonempty (HasType ∅ Gamma
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (_hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (_he : S.Term ∅ Gamma Psi e (.tprod (.dual b1) b0) v
      (.space (.tprod sv1 sv0)))
    (ihTy : MTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (ihE : TermFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b1) b0) v (.space (.tprod sv1 sv0))) :
    MTermSubctx orc ∅ Gamma Psi
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (.tprod (.dual b0) b1) (.pinv v)
      (.space (.tprod sv0 sv1)) := by
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : DimsAt orc sigma rho [] [] []
      (Basis.tof (.tprod (.dual b0) b1))
      (.space (.tprod sv0 sv1))
      (denotBasis sigma (.tprod (.dual b0) b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have trace := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨hb0dualv, hb1v⟩ := hbv.tprod_inv
  have hb0v := hb0dualv.dual_inv
  obtain ⟨hlb0,horth0⟩ := denotBasis_std_orthonormal_core
    (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl hb0std
  obtain ⟨hlb1,horth1⟩ := denotBasis_std_orthonormal_core
    (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl hb1std
  have hshape : ValSpace.shpOfPartial (orc rho [] []) (.tprod sv0 sv1) =
      .ok [Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual] using targetDims
  obtain ⟨hd0,hd1⟩ := tprod_shape_factors hshape
  simp only [denotSpace] at hd0 hd1
  rw [hlb0.finrank_eq] at hd0
  rw [hlb1.finrank_eq] at hd1
  have hinshape := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hinputshape : (.tprod sv1 sv0 : ValSpace).shpOfPartial (orc rho [] []) =
      .ok [((denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b1))).length,
        ((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))).length] := by
    simp [ValSpace.shpOfPartial,hd0,hd1,bind,Except.bind,pure,Except.pure]
  rw [hinputshape] at hinshape
  obtain ⟨sa,sb,hinfer,ha,hb⟩ := infer_tprod_of_partial_shape hinshape
  have harg : ResultAgree orc sigma rho [] [] []
      (.space (.tprod (.dual (Basis.sof b1)) (Basis.sof b0)))
      (.space (.tprod sa sb))
      (.vecs (HSpace.tprod (HSpace.dual (denotSpace sigma (Basis.sof b1)))
        (denotSpace sigma (Basis.sof b0)))
        (HSpace.tprodOfLists _ _
          ((denotSpace sigma (Basis.sof b1)).dualOfList
            ((denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b1))))
          ((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0)))))
      (denotTerm sigma e) (denotValB_partial orc rho [] [] v) := by
    obtain ⟨v',hv,hagree⟩ := trace.result
    refine ⟨v',hv,?_⟩
    obtain ⟨a,n,rfl,hd,hbl,hal,hc⟩ := hagree.array
    have hn : n = ((denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b1))).length *
        ((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))).length :=
      Except.ok.inj (hd.symm.trans (dof_tprod_ok hd1 hd0))
    rw [hn] at hbl hal hc
    simp only [Agree,denotSpaceAux,BasisDenot.atSpace_vecs_self]
    refine ⟨_,dof_tprod_ok ha hb,?_,hal,?_⟩
    · rw [HSpace.tprodOfLists_length,HSpace.dualOfList_length]
    · simpa only [Basis.tof,Basis.sof,denotSpaceAux,
        RawSpaceFFS.denotBasis_tprod_dual_atSpace] using hc
  have hout := pinv_tensor hlb1 hlb0 horth1 horth0 hinfer ha hb harg
  refine ⟨?_,targetDims⟩
  obtain ⟨v',hv,hagree⟩ := hout
  refine ⟨v',hv,?_⟩
  obtain ⟨a,n,rfl,hd,hbl,hal,hc⟩ := hagree.array
  have hn : n = ((denotBasis sigma b0).atSpace (denotSpace sigma (Basis.sof b0))).length *
      ((denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b1))).length :=
    Except.ok.inj (hd.symm.trans (dof_tprod_ok hb ha))
  rw [hn] at hal hc
  simp only [Basis.tof,Basis.sof,Agree,denotSpaceAux]
  rw [RawSpaceFFS.denotBasis_tprod_dual_atSpace]
  refine ⟨_,dof_tprod_ok hd0 hd1,?_,hal,?_⟩
  · rw [HSpace.tprodOfLists_length,HSpace.dualOfList_length]
  · simpa only [denotTerm,denotTermAux,denotSpace,denotSpaceAux,
      BasisDenot.atSpace_vecs_self] using hc

theorem arm_pinvT_std_facts
    {orc : PartialFFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v : ValExpr}
    {sv0 sv1 : ValSpace}
    (hb0std : Basis.isStd b0) (hb1std : Basis.isStd b1)
    (ht : Nonempty (HasType ∅ Gamma
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b1) b0) v
      (.space (.tprod sv1 sv0)))
    (ihTy : MTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod sv0 sv1)))
    (ihE : TermFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b1) b0) v (.space (.tprod sv1 sv0))) :
    TermFactsSubctx orc ∅ Gamma Psi
      (.pinvT (Basis.sof b1) (Basis.sof b0) e)
      (.tprod (.dual b0) b1) (.pinv v)
      (.space (.tprod sv0 sv1)) := by
  refine ⟨arm_pinvT_std hb0std hb1std ht hbv hTy he ihTy ihE,?_⟩
  intro sv hsv Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hsv
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle hc
  have hshape : ValSpace.shpOfPartial (orc rho [] []) (.tprod sv0 sv1) =
      .ok [Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual] using targetDims
  obtain ⟨hd0,hd1⟩ := tprod_shape_factors hshape
  have hinshape := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  have hinputshape : (.tprod sv1 sv0 : ValSpace).shpOfPartial (orc rho [] []) =
      .ok [Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier] := by
    simp [ValSpace.shpOfPartial,hd0,hd1,bind,Except.bind,pure,Except.pure]
  rw [hinputshape] at hinshape
  obtain ⟨sa,sb,hinfer,ha,hb⟩ := infer_tprod_of_partial_shape hinshape
  simp only [ValExpr.inferSpaceCtx,hinfer]
  rw [hshape]
  simp [ValSpace.shpOfPartial,ha,hb,bind,Except.bind,pure,Except.pure]

theorem arm_pinvD_std
    {orc : PartialFFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v : ValExpr}
    {sv1 : ValSpace}
    (hsofb0 : Basis.sof b0 = .real)
    (hb0std : Basis.isStd b0) (hb1std : Basis.isStd b1)
    (_ht : Nonempty (HasType ∅ Gamma (.pinvD (Basis.sof b1) e)
      (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (_hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (_he : S.Term ∅ Gamma Psi e (.dual b1) v (.space sv1))
    (ihTy : MTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (ihE : TermFactsSubctx orc ∅ Gamma Psi e (.dual b1) v
      (.space sv1)) :
    MTermSubctx orc ∅ Gamma Psi
      (.pinvD (Basis.sof b1) e) (.tprod (.dual b0) b1)
      (.pinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1)))
      (.space (.tprod .real sv1)) := by
  obtain ⟨hb0dualv, hb1v⟩ := hbv.tprod_inv
  have hb0v := hb0dualv.dual_inv
  have hb0eq : b0 = .one :=
    std_real_basis_eq_one hb0v hb0std hsofb0
  subst b0
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : DimsAt orc sigma rho [] [] []
      (Basis.tof (.tprod (.dual (.one : Basis)) b1))
      (.space (.tprod .real sv1))
      (denotBasis sigma (.tprod (.dual (.one : Basis)) b1)) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have trace := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨hlb1,horth1⟩ := denotBasis_std_orthonormal_core
    (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl hb1std
  have hshape : ValSpace.shpOfPartial (orc rho [] []) (.tprod .real sv1) =
      .ok [Module.finrank ℝ HSpace.real.carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual,denotSpace,denotSpaceAux] using targetDims
  have hd1 := (tprod_shape_factors hshape).2
  simp only [denotSpace] at hd1
  rw [hlb1.finrank_eq] at hd1
  have harg : ResultAgree orc sigma rho [] [] []
      (.space (.dual (Basis.sof b1))) (.space sv1)
      (.vecs (HSpace.dual (denotSpace sigma (Basis.sof b1)))
        ((denotSpace sigma (Basis.sof b1)).dualOfList
          ((denotBasis sigma b1).atSpace (denotSpace sigma (Basis.sof b1)))))
      (denotTerm sigma e) (denotValB_partial orc rho [] [] v) := by
    obtain ⟨v',hv,hagree⟩ := trace.result
    refine ⟨v',hv,?_⟩
    cases v' with
    | fn _ _ => simp only [Basis.tof,Agree] at hagree
    | array a =>
      simpa only [Basis.tof,Basis.sof,Agree,denotSpaceAux,
        RawSpaceFFS.denotBasis_dual_atSpace,BasisDenot.atSpace_vecs_self] using hagree
  have hout := pinv_dual hlb1 horth1 hd1 harg
  refine ⟨?_,targetDims⟩
  obtain ⟨v',hv,hagree⟩ := hout
  refine ⟨v',hv,?_⟩
  cases v' with
  | fn _ _ => simp only [Agree] at hagree
  | array a =>
    simp only [Basis.tof,Basis.sof,Agree,denotSpaceAux]
    simp only [denotBasis,Basis.sof,denotSpace,denotSpaceAux,BasisDenot.atSpace_vecs_self]
    simpa only [Agree,denotSpaceAux,BasisDenot.atSpace_vecs_self,
      denotTerm,denotTermAux] using hagree

theorem arm_pinvD_std_facts
    {orc : PartialFFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v : ValExpr}
    {sv1 : ValSpace}
    (hsofb0 : Basis.sof b0 = .real)
    (hb0std : Basis.isStd b0) (hb1std : Basis.isStd b1)
    (ht : Nonempty (HasType ∅ Gamma (.pinvD (Basis.sof b1) e)
      (Basis.tof (.tprod (.dual b0) b1))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) b1))
    (hTy : S.TyAt Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (he : S.Term ∅ Gamma Psi e (.dual b1) v (.space sv1))
    (ihTy : MTyAtSubctx orc Gamma Psi (.tprod (.dual b0) b1)
      (.space (.tprod .real sv1)))
    (ihE : TermFactsSubctx orc ∅ Gamma Psi e (.dual b1) v
      (.space sv1)) :
    TermFactsSubctx orc ∅ Gamma Psi
      (.pinvD (Basis.sof b1) e) (.tprod (.dual b0) b1)
      (.pinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1)))
      (.space (.tprod .real sv1)) := by
  refine ⟨arm_pinvD_std hsofb0 hb0std hb1std ht hbv hTy he ihTy ihE,?_⟩
  intro sv hsv Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hsv
  rfl

end GLang.PartialAdequacy
