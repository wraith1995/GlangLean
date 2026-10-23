import GLang.Proofs.Adequacy.Raw.Context.RawTypedConsistent
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobAdequacyCore
import GLang.Proofs.Adequacy.Raw.RawDofAdequacyCore
import GLang.Proofs.Adequacy.Foundations.Dims
import GLang.Proofs.Adequacy.Foundations.AgreeBasics
import GLang.Proofs.Value.Typing.ValueRealizeLc

/-!
# Raw infrastructure for linear-lambda assembly

This module contains the context, index, and coordinate facts shared by the
two strengthened linear-lambda assembly rules.  It deliberately stops below
the finite column-assembly argument: extending a raw-consistent telescope by
one concrete basis coordinate is independent of the codomain of the lambda.
-/

namespace GLang

open Basis (BasisValid)

private theorem raw_llam_basis_fv_subset_of_openVar_body
    {b : Basis} {L A : Finset Name}
    (h : forall y, y ∉ L -> forall z,
      z ∈ Basis.fv (Basis.openVar y b) -> z = y ∨ z ∈ A) :
    Basis.fv b ⊆ A := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Basis.fv b)
  rw [Finset.mem_union, not_or] at hy
  intro z hz
  rcases h y hy.1 z (Basis.fv_subset_openRec hz) with rfl | hzA
  · exact absurd hz hy.2
  · exact hzA

private theorem raw_llam_basisValid_fv_subset_keys
    {Gamma : NLCtx} {b : Basis} (h : BasisValid Gamma b) :
    Basis.fv b ⊆ Gamma.keys := by
  induction h with
  | empty | one => simp [Basis.fv]
  | dual _ _ ih => simpa only [Basis.fv] using ih
  | dsum _ _ _ _ ih0 ih1 | tprod _ _ _ _ ih0 ih1 =>
      simpa only [Basis.fv] using Finset.union_subset ih0 ih1
  | proj_ker hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_ker hb0 hb1 hs0 hs1 htype)).some
  | proj_coker hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_coker hb0 hb1 hs0 hs1 htype)).some
  | proj_img hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_img hb0 hb1 hs0 hs1 htype)).some
  | proj_coimg hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_coimg hb0 hb1 hs0 hs1 htype)).some
  | image _ _ _ ih => simpa only [Basis.fv] using ih
  | terms hb hs hsv hterms _ ih =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih) ?_
      · exact SValid.fv_closure hsv.some
      · intro z hz
        obtain ⟨e, he, hze⟩ := Term.mem_fvList.mp hz
        have hzctx := HasType.fv_closure (hterms e he).some hze
        simpa only [Finmap.keys_empty, Finset.empty_union] using hzctx
  | frame L hb0 hbody ih0 ihbody =>
      simp only [Basis.fv]
      refine Finset.union_subset ih0 ?_
      apply raw_llam_basis_fv_subset_of_openVar_body (L := L)
      intro y hy z hz
      have hzctx := ihbody y hy hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hzctx
      exact hzctx

/-- Insert the same fresh linear binding on both sides of a raw source-context
inclusion. -/
theorem RawCtxIncl.insert_lin
    {Delta Delta' : LCtx} {Gamma Gamma' : NLCtx}
    (h : RawCtxIncl Delta Gamma Delta' Gamma')
    (y : Name) (s : GLang.Space) :
    RawCtxIncl (Finmap.insert y s Delta) Gamma
      (Finmap.insert y s Delta') Gamma' := by
  refine ⟨?_, h.2⟩
  intro x t hx
  by_cases hxy : x = y
  · subst x
    rw [Finmap.lookup_insert] at hx
    cases Option.some.inj hx
    exact Or.inl (Finmap.lookup_insert Delta')
  · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
    rcases h.1 x t hx with hx' | hx'
    · exact Or.inl (by
        simpa [Finmap.lookup_insert_of_ne _ hxy] using hx')
    · exact Or.inr hx'

/-- Every semantic coordinate lies in the exact syntactic family supplied by
an assembly rule. -/
def ValSpace.rawFinOfDofUB
    {orc : FFSOracleSem} (hspec : OracleSpec orc) (rho : ValEnvSem)
    {sv : ValSpace} :
    Fin (ValSpace.dof (orc rho [] []) sv) → Fin (ValSpace.dofUB sv) :=
  fun i =>
    ⟨i.val, i.isLt.trans_le
      (ValSpace.dof_le_dofUB hspec rho [] [] sv)⟩

/-- A concrete source basis vector agrees with the value-language coordinate
delta at the same semantic index. -/
theorem RawAgree.basis_getD_delta
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {s : GLang.Space} {sv : ValSpace} {B : BasisDenot}
    (hB : IsListBasis (denotSpace sigma s)
      (B.atSpace (denotSpace sigma s)))
    (hdims : RawAgreeDimsAt orc sigma rho [] [] []
      (.space s) (.space sv) B)
    (i : Fin (ValSpace.dof (orc rho [] []) sv)) :
    RawResultAgree orc sigma rho [] [] [] (.space s) (.space sv) B
      (.hil ⟨denotSpace sigma s,
        (B.atSpace (denotSpace sigma s)).getD i.val 0⟩)
      (denotValB_semS orc rho [] [] (.delta i.val sv)) := by
  have hN : (B.atSpace (denotSpace sigma s)).length =
      ValSpace.dof (orc rho [] []) sv := by
    exact hB.finrank_eq.symm.trans
      (ValSpace.raw_dof_eq_finrank_of_shpOf
        (by simpa only [RawAgreeDimsAt] using hdims)).symm
  unfold RawResultAgree
  rw [denotValB_semS.eq_7]
  refine ⟨_, rfl, ?_⟩
  simp only [RawAgree, ValExpr.inferSpaceCtx, ValValSem.arrayOf]
  rw [LegacyAgree.space_iff]
  simp only [FlatArray.length_ofFn]
  refine ⟨hN, ?_⟩
  rw [DVal.atSpace_hil_self]
  rw [Finset.sum_eq_single i]
  · simp [i.isLt]
  · intro j _ hji
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [FlatArray.get_ofFn, j.isLt, hval]
  · exact fun hmem => absurd (Finset.mem_univ i) hmem

/-- Extend a raw-consistent world by the actual coordinate stored by a
linear-lambda family. -/
theorem RawConsistent.extend_binder_lin_delta
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    {y : VName}
    (hy : y ∉ Delta ∧ y ∉ Gamma ∧ forall b', (y, b') ∉ Psi)
    {GammaCert : NLCtx} (hleCert : NLCtxIncl GammaCert Gamma)
    {b : Basis} (htof : Basis.tof b = .space (Basis.sof b))
    (hb : BasisValid GammaCert b)
    (hisTy : Basis.IsTyBasis b)
    {sv : ValSpace} (hspace : S.Space GammaCert Psi (Basis.sof b) sv)
    (i : Fin (ValSpace.dof (orc rho [] []) sv))
    (hdims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof b) (.space sv) (denotBasis sigma b)) :
    exists yv,
      denotValB_semS orc rho [] [] (.delta i.val sv) = .ok yv ∧
      RawConsistent orc (Finmap.insert y (Basis.sof b) Delta) Gamma
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
  have hdims' : RawAgreeDimsAt orc sigma rho [] [] []
      (.space (Basis.sof b)) (.space sv) (denotBasis sigma b) := by
    simpa only [htof] using hdims
  have hresult := RawAgree.basis_getD_delta hB hdims' i
  obtain ⟨yv, hden, hagree⟩ := hresult
  have hfvb : Basis.fv b ⊆ Psi.keyNames := by
    intro z hz
    have hzCert : z ∈ GammaCert :=
      Finmap.mem_keys.mp (raw_llam_basisValid_fv_subset_keys hb hz)
    obtain ⟨tau, htau⟩ := Finmap.mem_iff.mp hzCert
    have hzGamma : z ∈ Gamma :=
      Finmap.mem_of_lookup_eq_some (hleCert z tau htau)
    obtain ⟨tau, htau⟩ := Finmap.mem_iff.mp hzGamma
    obtain ⟨bz, hbz⟩ := h.nl_mem_to_eval z
      (Finmap.mem_of_lookup_eq_some htau)
    exact EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨bz, hbz⟩
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
  apply RawConsistent.extend_lin h ⟨hy.1, hy.2.1⟩ htof
    (raw_basisValid_mono hb hleCert) hTyAt.toEvalT
    rfl (by simp [ValExpr.InferSpaceMatchesBase, ValExpr.inferSpaceCtx])
    ?_ (.delta hlcsv) (Or.inl ?_)
    (by rw [htof]; exact DVal.matchesShape_hil_rfl _ _)
    hden (by rw [htof]; exact hagree) hdims
  · rw [EvalCtx.keyNames_extend_core]
    simpa only [ValExpr.fv] using hfvsv.trans (Finset.subset_insert _ _)
  · simpa only [ValExpr.fv] using hynr

theorem RawTypedConsistent.extend_binder_lin_delta
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho)
    {y : VName}
    (hy : y ∉ Delta ∧ y ∉ Gamma ∧ forall b', (y, b') ∉ Psi)
    {GammaCert : NLCtx} (hleCert : NLCtxIncl GammaCert Gamma)
    {b : Basis} (htof : Basis.tof b = .space (Basis.sof b))
    (hb : BasisValid GammaCert b)
    (hisTy : Basis.IsTyBasis b)
    {sv : ValSpace} (hspace : S.Space GammaCert Psi (Basis.sof b) sv)
    (i : Fin (ValSpace.dof (orc rho [] []) sv))
    (hdims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof b) (.space sv) (denotBasis sigma b)) :
    exists yv,
      denotValB_semS orc rho [] [] (.delta i.val sv) = .ok yv ∧
      RawTypedConsistent orc (Finmap.insert y (Basis.sof b) Delta) Gamma
        (Psi.extend y b (.delta i.val sv))
        (Finmap.insert y (.space sv) GammaV)
        (sigma.bind y (.hil ⟨denotSpace sigma (Basis.sof b),
          ((denotBasis sigma b).atSpace
            (denotSpace sigma (Basis.sof b))).getD i.val 0⟩))
        (rho.update y yv) := by
  obtain ⟨yv,he,hh⟩ := h.raw.extend_binder_lin_delta hy hleCert htof hb hisTy hspace i hdims
  have hv := h.context.evalContext
  have hs := (RuntimeValue.preservation_mutual.1 hspace.toEvalS GammaV hv).some
  have hx : y ∉ GammaV := fun hm => (h.context.mem_iff y).mp hm |>.elim hy.1 hy.2.1
  have hTy : ValTy.EvalT Psi (Basis.tof b) (.space sv) :=
    (S.TyAt.space htof hb hspace).toEvalT
  refine ⟨yv,he,hh,?_⟩
  apply Operational.TypedContext.extend_lin h.context ⟨hy.1,hy.2.1⟩
    (V2.EvalEntryCreation.ofSpace (v := .delta i.val sv) ?_ htof)
    (raw_basisValid_mono hb hleCert) htof ⟨.space hs⟩ ⟨.delta (hs.weaken hx)⟩
  refine ⟨hTy,?_,.delta (realize_lc_joint.1 hspace.toEvalS h.raw.evalCtxLc)⟩
  rw [EvalCtx.keyNames_extend_core]
  exact (hspace.fv_subset_keyNames h.raw.evalCtxScoped).trans (Finset.subset_insert _ _)

end GLang
