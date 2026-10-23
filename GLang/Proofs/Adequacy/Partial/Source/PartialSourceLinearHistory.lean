import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceFFS
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceWellFormed
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceArms
import GLang.Proofs.Adequacy.Raw.RawLlamInfrastructure

namespace GLang.PartialAdequacy
open Basis (BasisValid)
open PartialValueEval

/-- A successful coordinate delta represents the corresponding actual source basis vector. -/
theorem Agree.basis_getD_delta
    {orc : PartialFFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {s : Space} {sv : ValSpace} {B : BasisDenot}
    (hB : IsListBasis (denotSpace sigma s) (B.atSpace (denotSpace sigma s)))
    (hdims : DimsAt orc sigma rho [] [] [] (.space s) (.space sv) B)
    {n : Nat} (hn : sv.dofPartial (orc rho [] []) = .ok n) (i : Fin n) :
    ResultAgree orc sigma rho [] [] [] (.space s) (.space sv) B
      (.hil ⟨denotSpace sigma s, (B.atSpace (denotSpace sigma s)).getD i.val 0⟩)
      (denotValB_partial orc rho [] [] (.delta i.val sv)) := by
  have hN : (B.atSpace (denotSpace sigma s)).length = n := by
    have hdim := shape_dof (show sv.shpOfPartial (orc rho [] []) = .ok (srcShp sigma [] s) from (by simpa only [DimsAt] using hdims))
    rw [hn] at hdim
    exact hB.finrank_eq.symm.trans (Except.ok.inj hdim).symm
  rw [denotValB_partial]
  simp only [withDimensions, dimensions, hn, bind, Except.bind, ValExpr.inferSpaceCtx]
  rw [dof_numbers _ _ _ hn]
  refine ⟨_, rfl, ?_⟩
  simp only [ValValSem.arrayOf]
  rw [agree_space_iff hn]
  refine ⟨hN, FlatArray.length_ofFn _ _, ?_⟩
  rw [DVal.atSpace_hil_self]
  rw [Finset.sum_eq_single i]
  · simp [ValValSem.arrayOf, FlatArray.get_ofFn, i.isLt]
  · intro j _ hji
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [ValValSem.arrayOf, FlatArray.get_ofFn, j.isLt, hval]
  · exact fun hmem => absurd (Finset.mem_univ i) hmem

theorem History.extend_binder_lin_delta
    {orc : PartialFFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : History orc Delta Gamma Psi GammaV sigma rho)
    {y : VName}
    (hy : y ∉ Delta ∧ y ∉ Gamma ∧ forall b', (y, b') ∉ Psi)
    {GammaCert : NLCtx} (hleCert : NLCtxIncl GammaCert Gamma)
    {b : Basis} (htof : Basis.tof b = .space (Basis.sof b))
    (hb : BasisValid GammaCert b)
    (hisTy : Basis.IsTyBasis b)
    {sv : ValSpace} (hspace : S.Space GammaCert Psi (Basis.sof b) sv)
    {n : Nat} (hn : sv.dofPartial (orc rho [] []) = .ok n)
    (i : Fin n)
    (hdims : DimsAt orc sigma rho [] [] []
      (Basis.tof b) (.space sv) (denotBasis sigma b)) :
    exists yv,
      denotValB_partial orc rho [] [] (.delta i.val sv) = .ok yv ∧
      History orc (Finmap.insert y (Basis.sof b) Delta) Gamma
        (Psi.extend y b (.delta i.val sv))
        (Finmap.insert y (.space sv) GammaV)
        (sigma.bind y (.hil ⟨denotSpace sigma (Basis.sof b),
          ((denotBasis sigma b).atSpace
            (denotSpace sigma (Basis.sof b))).getD i.val 0⟩))
        (rho.update y yv) := by
  have hB : IsListBasis (denotSpace sigma (Basis.sof b))
      ((denotBasis sigma b).atSpace
        (denotSpace sigma (Basis.sof b))) :=
    denotBasis_atSpace_isListBasis sigma Gamma b
      (raw_basisValid_mono hb hleCert) h.ctxWF_nl h.envWF_nl
  have hdims' : DimsAt orc sigma rho [] [] []
      (.space (Basis.sof b)) (.space sv) (denotBasis sigma b) := by
    simpa only [htof] using hdims
  have hresult := Agree.basis_getD_delta hB hdims' hn i
  obtain ⟨yv, hden, hagree⟩ := hresult
  have hfvsv : ValSpace.fv sv ⊆ Psi.keyNames :=
    hspace.fv_subset_keyNames h.evalCtxScoped
  have hyKey : y ∉ Psi.keyNames := by
    rw [EvalCtx.mem_keyNames_iff_exists_basis]
    rintro ⟨b', hb'⟩
    exact hy.2.2 b' hb'
  have hynr : y ∉ ValSpace.fv sv := fun hm => hyKey (hfvsv hm)
  have hlcsv : ValSpace.lc sv :=
    realize_lc_joint.1 hspace.toEvalS h.evalCtxLc
  have hTyAt : S.TyAt GammaCert Psi b (.space sv) :=
    .space htof hb hspace
  refine ⟨yv, hden, ?_⟩
  apply History.extend_lin h ⟨hy.1, hy.2.1⟩ htof
    (raw_basisValid_mono hb hleCert) hTyAt.toEvalT
    rfl (by simp [ValExpr.InferSpaceMatchesBase, ValExpr.inferSpaceCtx])
    ?_ (.delta hlcsv) (Or.inl ?_)
    (by rw [htof]; exact DVal.matchesShape_hil_rfl _ _)
    hden (by rw [htof]; exact hagree) hdims
  · rw [EvalCtx.keyNames_extend_core]
    simpa only [ValExpr.fv] using hfvsv.trans (Finset.subset_insert _ _)
  · simpa only [ValExpr.fv] using hynr

theorem TypedHistory.extend_binder_lin_delta
    {orc : PartialFFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : TypedHistory orc Delta Gamma Psi GammaV sigma rho)
    {y : VName}
    (hy : y ∉ Delta ∧ y ∉ Gamma ∧ forall b', (y, b') ∉ Psi)
    {GammaCert : NLCtx} (hleCert : NLCtxIncl GammaCert Gamma)
    {b : Basis} (htof : Basis.tof b = .space (Basis.sof b))
    (hb : BasisValid GammaCert b)
    (hisTy : Basis.IsTyBasis b)
    {sv : ValSpace} (hspace : S.Space GammaCert Psi (Basis.sof b) sv)
    {n : Nat} (hn : sv.dofPartial (orc rho [] []) = .ok n)
    (i : Fin n)
    (hdims : DimsAt orc sigma rho [] [] []
      (Basis.tof b) (.space sv) (denotBasis sigma b)) :
    exists yv,
      denotValB_partial orc rho [] [] (.delta i.val sv) = .ok yv ∧
      TypedHistory orc (Finmap.insert y (Basis.sof b) Delta) Gamma
        (Psi.extend y b (.delta i.val sv))
        (Finmap.insert y (.space sv) GammaV)
        (sigma.bind y (.hil ⟨denotSpace sigma (Basis.sof b),
          ((denotBasis sigma b).atSpace
            (denotSpace sigma (Basis.sof b))).getD i.val 0⟩))
        (rho.update y yv) := by
  obtain ⟨yv,he,hh⟩ := h.history.extend_binder_lin_delta hy hleCert htof hb hisTy hspace hn i hdims
  have hv := h.context.evalContext
  have hs := (RuntimeValue.preservation_mutual.1 hspace.toEvalS GammaV hv).some
  have hx : y ∉ GammaV := fun hm => (h.context.mem_iff y).mp hm |>.elim hy.1 hy.2.1
  have hTy : ValTy.EvalT Psi (Basis.tof b) (.space sv) :=
    (S.TyAt.space htof hb hspace).toEvalT
  refine ⟨yv,he,hh,?_⟩
  apply Operational.TypedContext.extend_lin h.context ⟨hy.1,hy.2.1⟩
    (V2.EvalEntryCreation.ofSpace (v := .delta i.val sv) ?_ htof)
    (raw_basisValid_mono hb hleCert) htof ⟨.space hs⟩ ⟨.delta (hs.weaken hx)⟩
  refine ⟨hTy,?_,.delta (realize_lc_joint.1 hspace.toEvalS h.history.evalCtxLc)⟩
  rw [EvalCtx.keyNames_extend_core]
  exact (hspace.fv_subset_keyNames h.history.evalCtxScoped).trans (Finset.subset_insert _ _)

end GLang.PartialAdequacy
