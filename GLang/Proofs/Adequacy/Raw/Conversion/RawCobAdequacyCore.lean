import GLang.Proofs.Adequacy.Raw.RawSpaceAdequacyCore
import GLang.Proofs.Source.BasisSoundness

namespace GLang

open scoped BigOperators

/-- Claim (2) over raw consistency, stable under evaluator-context extension. -/
def RawMCobSubctx (orc : FFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (bSrc : Basis) (env : ValExpr) (bTgt : Basis) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
      (sigma : DEnv) (GammaV : ValCtx),
      NLCtxIncl Gamma Gamma' ->
      RawTypedConsistent orc Delta' Gamma' Psi' GammaV sigma rho ->
      CobAgree orc sigma rho bSrc bTgt env

/-- Syntactic matrix-shape information paired with raw COB adequacy. -/
def RawCobInferSubctx (orc : FFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (env : ValExpr) (b : Basis) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
      (sigma : DEnv) (GammaV : ValCtx),
      NLCtxIncl Gamma Gamma' ->
      RawTypedConsistent orc Delta' Gamma' Psi' GammaV sigma rho ->
      exists sa sb,
        ValExpr.inferSpaceCtx [] env = .tprod sa sb /\
        ValSpace.dof (orc rho [] []) sa =
          ((denotBasis sigma b).atSpace
            (denotSpace sigma (Basis.sof b))).length /\
        ValSpace.dof (orc rho [] []) sb =
          ((denotBasis sigma b).atSpace
            (denotSpace sigma (Basis.sof b))).length

/-- The pair produced by each `S.Cob` constructor in the direct mutual proof. -/
structure RawCobFactsSubctx (orc : FFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (bSrc : Basis) (env : ValExpr) (bTgt : Basis) : Prop where
  agree : RawMCobSubctx orc Gamma Psi bSrc env bTgt
  infer : RawCobInferSubctx orc Gamma Psi env bSrc

/-! ## Concrete-basis length infrastructure -/

/-- At any raw-consistent telescope above `Gamma`, a valid space basis has the
same concrete-list length as the dynamic dimension of its strengthened space
realization. -/
theorem raw_cob_basis_length (orc : FFSOracleSem)
    {Gamma Gamma' : NLCtx} {Delta' : LCtx} {Psi0 Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    {b : Basis} {sv : ValSpace}
    (hb : Basis.BasisValid Gamma b)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi0 (Basis.sof b) sv)
    (hsub : Psi0.Subctx Psi)
    (hle : NLCtxIncl Gamma Gamma')
    (hc : RawTypedConsistent orc Delta' Gamma' Psi GammaV sigma rho) :
    IsListBasis (denotSpace sigma (Basis.sof b))
        ((denotBasis sigma b).atSpace (denotSpace sigma (Basis.sof b))) /\
      ((denotBasis sigma b).atSpace
        (denotSpace sigma (Basis.sof b))).length =
        ValSpace.dof (orc rho [] []) sv := by
  have hlb := denotBasis_atSpace_isListBasis sigma Gamma' b
    (raw_basisValid_mono hb hle) hc.ctxWF_nl hc.envWF_nl
  refine ⟨hlb, ?_⟩
  have hdim := ValSpace.raw_dof_eq_finrank_of_shpOf
    (ihSpace hsub rho Delta' Gamma' sigma GammaV hle hc)
  exact (hdim.trans hlb.finrank_eq).symm

/-- Equal source spaces make any two valid concrete space bases equally long. -/
theorem raw_denotBasis_length_eq_of_sof_eq
    {Gamma : NLCtx} {sigma : DEnv} {b0 b1 : Basis}
    (hctx : CtxWF ∅ Gamma) (henv : EnvWF sigma ∅ Gamma)
    (hb0 : Basis.BasisValid Gamma b0)
    (hb1 : Basis.BasisValid Gamma b1)
    (hsof : Basis.sof b0 = Basis.sof b1) :
    ((denotBasis sigma b0).atSpace
      (denotSpace sigma (Basis.sof b0))).length =
    ((denotBasis sigma b1).atSpace
      (denotSpace sigma (Basis.sof b1))).length := by
  have h0 := denotBasis_atSpace_isListBasis sigma Gamma b0 hb0 hctx henv
  have h1 := denotBasis_atSpace_isListBasis sigma Gamma b1 hb1 hctx henv
  calc
    _ = Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier :=
      h0.finrank_eq.symm
    _ = Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier := by
      rw [hsof]
    _ = _ := h1.finrank_eq

theorem raw_denotBasis_tprod_atSpace_length
    (sigma : DEnv) (b0 b1 : Basis) :
    ((denotBasis sigma (.tprod b0 b1)).atSpace
      (denotSpace sigma (Basis.sof (.tprod b0 b1)))).length =
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (Basis.sof b0))).length *
      ((denotBasis sigma b1).atSpace
        (denotSpace sigma (Basis.sof b1))).length := by
  show (BasisDenot.atSpace
    (HSpace.tprod (denotSpace sigma (Basis.sof b0))
      (denotSpace sigma (Basis.sof b1)))
    (denotBasis sigma (.tprod b0 b1))).length = _
  simp only [denotBasis, BasisDenot.atSpace_vecs_self]
  rw [HSpace.tprodOfLists_length]

theorem raw_denotBasis_dsum_atSpace_length
    (sigma : DEnv) (b0 b1 : Basis) :
    ((denotBasis sigma (.dsum b0 b1)).atSpace
      (denotSpace sigma (Basis.sof (.dsum b0 b1)))).length =
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (Basis.sof b0))).length +
      ((denotBasis sigma b1).atSpace
        (denotSpace sigma (Basis.sof b1))).length := by
  show (BasisDenot.atSpace
    (HSpace.dsum (denotSpace sigma (Basis.sof b0))
      (denotSpace sigma (Basis.sof b1)))
    (denotBasis sigma (.dsum b0 b1))).length = _
  simp only [denotBasis, BasisDenot.atSpace_vecs_self]
  rw [HSpace.dsumOfLists_length]

theorem raw_denotBasis_dual_atSpace_length
    (sigma : DEnv) (b : Basis) :
    ((denotBasis sigma (.dual b)).atSpace
      (denotSpace sigma (Basis.sof (.dual b)))).length =
      ((denotBasis sigma b).atSpace
        (denotSpace sigma (Basis.sof b))).length := by
  show (BasisDenot.atSpace (HSpace.dual (denotSpace sigma (Basis.sof b)))
    (denotBasis sigma (.dual b))).length = _
  simp only [denotBasis, BasisDenot.atSpace_vecs_self]
  rw [HSpace.dualOfList_length]

/-! ## Structural COB-inference arms -/

theorem raw_arm_cob_infer_inverse
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {env : ValExpr}
    (hb0 : Basis.BasisValid Gamma b0)
    (hb1 : Basis.BasisValid Gamma b1)
    (h : S.Cob Gamma Psi b1 env b0)
    (ih : RawCobInferSubctx orc Gamma Psi env b1) :
    RawCobInferSubctx orc Gamma Psi (.inv env) b0 := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa, sb, hinfer, hsa, hsb⟩ :=
    ih hsub rho Delta' Gamma' sigma GammaV hle hc
  have hlen := raw_denotBasis_length_eq_of_sof_eq hc.ctxWF_nl hc.envWF_nl
    (raw_basisValid_mono hb0 hle) (raw_basisValid_mono hb1 hle)
    (S.Cob.sof_eq h).symm
  refine ⟨sb, sa, ?_, hsb.trans hlen.symm, hsa.trans hlen.symm⟩
  simp only [ValExpr.inferSpaceCtx, hinfer]

theorem raw_arm_cob_infer_trans
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b2 : Basis} {env0 env1 : ValExpr} {sv : ValSpace}
    (hb0 : Basis.BasisValid Gamma b0)
    (h0 : S.Cob Gamma Psi b0 env0 b1)
    (_h1 : S.Cob Gamma Psi b1 env1 b2)
    (_hsv : S.Space Gamma Psi (Basis.sof b0) sv)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv)
    (ih1 : RawCobInferSubctx orc Gamma Psi env1 b1) :
    RawCobInferSubctx orc Gamma Psi
      (.mtm 0 0 sv sv env1 (ValExpr.reshapBase env0 (.tprod sv sv))) b0 := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa, sb, hinfer, _hsa, hsb⟩ :=
    ih1 hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨_, hlen⟩ := raw_cob_basis_length orc hb0
    ihSpace hsub hle hc
  have hmid := raw_denotBasis_length_eq_of_sof_eq hc.ctxWF_nl hc.envWF_nl
    (raw_basisValid_mono (S.Cob.basisValid_src _h1) hle)
    (raw_basisValid_mono hb0 hle) (S.Cob.sof_eq h0).symm
  refine ⟨sv, sb, ?_, hlen.symm, hsb.trans hmid⟩
  simp only [ValExpr.reshapBase, ValExpr.inferSpaceCtx, ValTy.spaceOf, hinfer]

theorem raw_arm_cob_infer_tprod
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b0' b1' : Basis} {env0 env1 : ValExpr}
    (ih0 : RawCobInferSubctx orc Gamma Psi env0 b0')
    (ih1 : RawCobInferSubctx orc Gamma Psi env1 b1') :
    RawCobInferSubctx orc Gamma Psi (.vkrn env0 env1) (.tprod b0' b1') := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa0, sb0, hi0, ha0, hb0⟩ :=
    ih0 hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa1, sb1, hi1, ha1, hb1⟩ :=
    ih1 hsub rho Delta' Gamma' sigma GammaV hle hc
  refine ⟨.tprod sa0 sa1, .tprod sb0 sb1, ?_, ?_, ?_⟩
  · simp only [ValExpr.inferSpaceCtx, hi0, hi1]
  · rw [ValSpace.dof_tprod, ha0, ha1,
      raw_denotBasis_tprod_atSpace_length]
  · rw [ValSpace.dof_tprod, hb0, hb1,
      raw_denotBasis_tprod_atSpace_length]

theorem raw_arm_cob_infer_dsum
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b0' b1' : Basis} {env0 env1 : ValExpr}
    (ih0 : RawCobInferSubctx orc Gamma Psi env0 b0')
    (ih1 : RawCobInferSubctx orc Gamma Psi env1 b1') :
    RawCobInferSubctx orc Gamma Psi (.vblk env0 env1) (.dsum b0' b1') := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa0, sb0, hi0, ha0, hb0⟩ :=
    ih0 hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa1, sb1, hi1, ha1, hb1⟩ :=
    ih1 hsub rho Delta' Gamma' sigma GammaV hle hc
  refine ⟨.dsum sa0 sa1, .dsum sb0 sb1, ?_, ?_, ?_⟩
  · simp only [ValExpr.inferSpaceCtx, hi0, hi1]
  · rw [ValSpace.dof_dsum, ha0, ha1,
      raw_denotBasis_dsum_atSpace_length]
  · rw [ValSpace.dof_dsum, hb0, hb1,
      raw_denotBasis_dsum_atSpace_length]

theorem raw_arm_cob_infer_dual_std
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 : Basis} {env : ValExpr}
    (ih : RawCobInferSubctx orc Gamma Psi env b0) :
    RawCobInferSubctx orc Gamma Psi (.vtrans (.inv env)) (.dual b0) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa, sb, hinfer, hsa, hsb⟩ :=
    ih hsub rho Delta' Gamma' sigma GammaV hle hc
  refine ⟨sa, sb, ?_, ?_, ?_⟩
  · simp only [ValExpr.inferSpaceCtx, hinfer]
  · simpa only [raw_denotBasis_dual_atSpace_length] using hsa
  · simpa only [raw_denotBasis_dual_atSpace_length] using hsb

theorem raw_arm_cob_infer_refl
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {sv : ValSpace}
    (hb : Basis.BasisValid Gamma b)
    (htof : Basis.tof b = .space (Basis.sof b))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) sv) :
    RawCobInferSubctx orc Gamma Psi
      (.reshap (.idelta sv) (.space (.tprod sv sv))
        (.space (.tprod sv sv))) b := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨_, hlen⟩ := raw_cob_basis_length orc hb
    ihSpace hsub hle hc
  refine ⟨sv, sv, ?_, hlen.symm, hlen.symm⟩
  simp [ValExpr.inferSpaceCtx]

/-- Common inference proof for COB values whose syntactic input/output factors
are two strengthened realizations of the source basis's space. -/
theorem raw_cob_infer_of_space_pair
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {env : ValExpr} {sv0 sv1 : ValSpace}
    (hb : Basis.BasisValid Gamma b)
    (hinfer : ValExpr.inferSpaceCtx [] env = .tprod sv0 sv1)
    (ih0 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) sv0)
    (ih1 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) sv1) :
    RawCobInferSubctx orc Gamma Psi env b := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨hlb, hlen⟩ := raw_cob_basis_length orc hb ih0 hsub hle hc
  have hd1 := ValSpace.raw_dof_eq_finrank_of_shpOf
    (ih1 hsub rho Delta' Gamma' sigma GammaV hle hc)
  exact ⟨sv0, sv1, hinfer, hlen.symm, hd1.trans hlb.finrank_eq⟩

/-- Cokernel and image of one denoted linear map have equal finite
dimension. -/
theorem raw_finrank_denotSpace_coker_eq_img
    (sigma : DEnv) (s0 s1 : Space) (e : Term) :
    Module.finrank ℝ (denotSpace sigma (.coker s0 s1 e)).carrier =
      Module.finrank ℝ (denotSpace sigma (.img s0 s1 e)).carrier := by
  simp only [denotSpace]
  have hker := LinearMap.finrank_range_add_finrank_ker
    (DVal.asLinMap (denotSpaceAux sigma [] s0) (denotSpaceAux sigma [] s1)
      (denotTermAux sigma [] e))
  have horth := (denotSpaceAux sigma [] s0).finrank_add_finrank_orthRel
    (LinearMap.ker (DVal.asLinMap (denotSpaceAux sigma [] s0)
      (denotSpaceAux sigma [] s1) (denotTermAux sigma [] e)))
  have hdim : Module.finrank ℝ
      (Submodule.orthRel (denotSpaceAux sigma [] s0).innerProduct
        (LinearMap.ker (DVal.asLinMap (denotSpaceAux sigma [] s0)
          (denotSpaceAux sigma [] s1) (denotTermAux sigma [] e)))) =
      Module.finrank ℝ
        (LinearMap.range (DVal.asLinMap (denotSpaceAux sigma [] s0)
          (denotSpaceAux sigma [] s1) (denotTermAux sigma [] e))) := by
    omega
  exact hdim

theorem raw_arm_cob_infer_image
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 : Basis} {env : ValExpr}
    (hbSrc : Basis.BasisValid Gamma (.image b0))
    (hcoker : exists s0 s1 e, Basis.sof b0 = .coker s0 s1 e)
    (ih : RawCobInferSubctx orc Gamma Psi env b0) :
    RawCobInferSubctx orc Gamma Psi env (.image b0) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa, sb, hinfer, hsa, hsb⟩ :=
    ih hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨s0, s1, e, hsof⟩ := hcoker
  have hbase := denotBasis_atSpace_isListBasis sigma Gamma' b0
    (raw_basisValid_mono hbSrc.image_inv.1 hle)
    hc.ctxWF_nl hc.envWF_nl
  have himage := denotBasis_atSpace_isListBasis sigma Gamma' (.image b0)
    (raw_basisValid_mono hbSrc hle) hc.ctxWF_nl hc.envWF_nl
  have hdim :
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (Basis.sof b0))).length =
      ((denotBasis sigma (.image b0)).atSpace
        (denotSpace sigma (Basis.sof (.image b0)))).length := by
    have hsofImage : Basis.sof (.image b0) = .img s0 s1 e := by
      simp only [Basis.sof, hsof]
    rw [hbase.finrank_eq.symm, himage.finrank_eq.symm, hsof, hsofImage]
    exact raw_finrank_denotSpace_coker_eq_img sigma s0 s1 e
  exact ⟨sa, sb, hinfer, hsa.trans hdim, hsb.trans hdim⟩

theorem raw_arm_cob_infer_proj_ker_coker
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {b0 b1 : Basis} {env1 env2 env3 : ValExpr}
    {sv0 sv sv' sv0' : ValSpace}
    (hbSrc : Basis.BasisValid Gamma (.proj s b0 b1))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSpace' : RawMSpaceSubctx orc Gamma Psi s sv') :
    RawCobInferSubctx orc Gamma Psi
      (.mtm 0 0 sv0' sv0'
        (ValExpr.reshapBase env1 (.tprod sv0' sv'))
        (.mtm 0 0 sv0 sv0
          (ValExpr.reshapBase env2 (.tprod sv0 sv0'))
          (ValExpr.reshapBase env3 (.tprod sv sv0))))
      (.proj s b0 b1) := by
  exact raw_cob_infer_of_space_pair
    (env := .mtm 0 0 sv0' sv0'
      (ValExpr.reshapBase env1 (.tprod sv0' sv'))
      (.mtm 0 0 sv0 sv0
        (ValExpr.reshapBase env2 (.tprod sv0 sv0'))
        (ValExpr.reshapBase env3 (.tprod sv sv0))))
    (sv0 := sv) (sv1 := sv') hbSrc rfl ihSpace ihSpace'

theorem raw_arm_cob_infer_proj_img_coimg
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {b0 b1 : Basis} {env1 env2 env3 : ValExpr}
    {sv1 sv sv' sv1' : ValSpace}
    (hbSrc : Basis.BasisValid Gamma (.proj s b0 b1))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSpace' : RawMSpaceSubctx orc Gamma Psi s sv') :
    RawCobInferSubctx orc Gamma Psi
      (.mtm 0 0 sv1' sv1'
        (ValExpr.reshapBase env1 (.tprod sv1' sv'))
        (.mtm 0 0 sv1 sv1
          (ValExpr.reshapBase env2 (.tprod sv1 sv1'))
          (ValExpr.reshapBase env3 (.tprod sv sv1))))
      (.proj s b0 b1) := by
  exact raw_cob_infer_of_space_pair
    (env := .mtm 0 0 sv1' sv1'
      (ValExpr.reshapBase env1 (.tprod sv1' sv'))
      (.mtm 0 0 sv1 sv1
        (ValExpr.reshapBase env2 (.tprod sv1 sv1'))
        (ValExpr.reshapBase env3 (.tprod sv sv1))))
    (sv0 := sv) (sv1 := sv') hbSrc rfl ihSpace ihSpace'

theorem raw_arm_cob_infer_terms_rref
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {env0 env1 : ValExpr} {sv : ValSpace}
    (hbSrc : Basis.BasisValid Gamma b)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) sv) :
    RawCobInferSubctx orc Gamma Psi
      (ValExpr.reshapBase
        (.rrefRep env0 (ValExpr.reshapBase env1 (.tprod sv sv)))
        (.tprod sv sv)) b := by
  exact raw_cob_infer_of_space_pair
    (env := ValExpr.reshapBase
      (.rrefRep env0 (ValExpr.reshapBase env1 (.tprod sv sv)))
      (.tprod sv sv))
    (sv0 := sv) (sv1 := sv) hbSrc rfl ihSpace ihSpace

theorem raw_arm_cob_infer_proj_ker_coker_cod
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {b0 b1 : Basis} {env1 env3 : ValExpr}
    {sv0 sv sv' : ValSpace}
    (hbSrc : Basis.BasisValid Gamma (.proj s b0 b1))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSpace' : RawMSpaceSubctx orc Gamma Psi s sv') :
    RawCobInferSubctx orc Gamma Psi
      (.mtm 0 0 sv0 sv0
        (ValExpr.reshapBase env1 (.tprod sv0 sv'))
        (ValExpr.reshapBase env3 (.tprod sv sv0)))
      (.proj s b0 b1) := by
  exact raw_cob_infer_of_space_pair
    (env := .mtm 0 0 sv0 sv0
      (ValExpr.reshapBase env1 (.tprod sv0 sv'))
      (ValExpr.reshapBase env3 (.tprod sv sv0)))
    (sv0 := sv) (sv1 := sv') hbSrc rfl ihSpace ihSpace'

theorem raw_arm_cob_infer_proj_img_coimg_dom
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {b0 b1 : Basis} {env1 env3 : ValExpr}
    {sv1 sv sv' : ValSpace}
    (hbSrc : Basis.BasisValid Gamma (.proj s b0 b1))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSpace' : RawMSpaceSubctx orc Gamma Psi s sv') :
    RawCobInferSubctx orc Gamma Psi
      (.mtm 0 0 sv1 sv1
        (ValExpr.reshapBase env1 (.tprod sv1 sv'))
        (ValExpr.reshapBase env3 (.tprod sv sv1)))
      (.proj s b0 b1) := by
  exact raw_cob_infer_of_space_pair
    (env := .mtm 0 0 sv1 sv1
      (ValExpr.reshapBase env1 (.tprod sv1 sv'))
      (ValExpr.reshapBase env3 (.tprod sv sv1)))
    (sv0 := sv) (sv1 := sv') hbSrc rfl ihSpace ihSpace'

/-! ## Reflexive COB agreement -/

theorem Nat.raw_rowMajor_div_mod {n j i : Nat}
    (hj : j < n) (hi : i < n) :
    (j * n + i) / n = j /\ (j * n + i) % n = i := by
  have hn : 0 < n := Nat.zero_lt_of_lt hj
  have h : j * n + i = i + n * j := by ring
  rw [h, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hi,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  simp

theorem Nat.raw_rowMajor_lt {n j i : Nat}
    (hj : j < n) (hi : i < n) : j * n + i < n * n := by
  calc
    j * n + i < j * n + n := Nat.add_lt_add_left hi _
    _ = (j + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right _ hj

/-- Re-index a finite sum along equality of its bound. -/
theorem Fin.raw_sum_cast_of_eq {M : Type} [AddCommMonoid M]
    {n m : Nat} (h : n = m) (f : Fin n → M) :
    (∑ i, f i) = ∑ i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  rfl

theorem raw_denotValB_semS_idelta_reshap_get
    (orc : FFSOracleSem) (rho : ValEnvSem) (sv : ValSpace)
    {a : FlatArray}
    (hval : denotValB_semS orc rho [] []
      (.reshap (.idelta sv) (.space (.tprod sv sv))
        (.space (.tprod sv sv))) = .ok (.array a))
    {j i : Nat} (hj : j < ValSpace.dof (orc rho [] []) sv)
    (hi : i < ValSpace.dof (orc rho [] []) sv) :
    a.get (j * ValSpace.dof (orc rho [] []) sv + i) =
      if j = i then 1 else 0 := by
  set n := ValSpace.dof (orc rho [] []) sv with hn
  have hlt := Nat.raw_rowMajor_lt hj hi
  obtain ⟨hdiv, hmod⟩ := Nat.raw_rowMajor_div_mod hj hi
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hj)
  rw [denotValB_semS.eq_17, denotValB_semS.eq_8] at hval
  simp only [ValExpr.inferSpaceCtx, ValSpace.dof_tprod,
    reshapDenotSemS, reshapArrayBetweenS, ValValSem.arrayOf, FlatArray.length_ofFn,
    reduceIte] at hval
  injection hval with ha
  injection ha with ha
  subst a
  simp only [FlatArray.get_ofFn, ← hn, hlt, if_true, hn0, if_false,
    hdiv, hmod, hj, and_true]

theorem raw_arm_cob_refl
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {sv : ValSpace}
    (hb : Basis.BasisValid Gamma b)
    (_htof : Basis.tof b = .space (Basis.sof b))
    (_hsv : S.Space Gamma Psi (Basis.sof b) sv)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) sv) :
    RawMCobSubctx orc Gamma Psi b
      (.reshap (.idelta sv) (.space (.tprod sv sv))
        (.space (.tprod sv sv))) b := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨_, hlen⟩ := raw_cob_basis_length orc hb ihSpace hsub hle hc
  unfold CobAgree
  dsimp only
  set source := (denotBasis sigma b).atSpace
    (denotSpace sigma (Basis.sof b)) with hsource
  let a := FlatArray.ofFn
    (ValSpace.dof (orc rho [] []) sv * ValSpace.dof (orc rho [] []) sv)
    (fun i =>
      let d := ValSpace.dof (orc rho [] []) sv
      if d = 0 then 0
      else if i < d * d then
        let r := i / d
        let c := i % d
        if r = c /\ r < d then 1 else 0
      else 0)
  have hval : denotValB_semS orc rho [] []
      (.reshap (.idelta sv) (.space (.tprod sv sv))
        (.space (.tprod sv sv))) = .ok (.array a) := by
    rw [denotValB_semS.eq_17, denotValB_semS.eq_8]
    simp only [ValExpr.inferSpaceCtx, ValSpace.dof_tprod,
      reshapDenotSemS, reshapArrayBetweenS, ValValSem.arrayOf, FlatArray.length_ofFn,
      reduceIte]
    rfl
  refine ⟨rfl, a, hval, ?_, ?_⟩
  · simp [a, hlen]
  · intro j
    have hget : forall i : Fin source.length,
        a.get (j.val * source.length + i.val) =
          if j = i then 1 else 0 := by
      intro i
      have hj' : j.val < ValSpace.dof (orc rho [] []) sv :=
        hlen ▸ j.isLt
      have hi' : i.val < ValSpace.dof (orc rho [] []) sv :=
        hlen ▸ i.isLt
      have hidx : j.val * source.length + i.val =
          j.val * ValSpace.dof (orc rho [] []) sv + i.val :=
        congrArg (fun n => j.val * n + i.val) hlen
      rw [hidx,
        raw_denotValB_semS_idelta_reshap_get orc rho sv hval hj' hi']
      simp [Fin.val_inj]
    simp only [hget, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ## Image COB agreement -/

/-- The map used by `denotBasis (.image b)`, named for the list-level
linearity argument. -/
def rawImageMap {V0 V1 : HSpace}
    (f : V0.carrier →ₗ[ℝ] V1.carrier) (K : Submodule ℝ V0.carrier)
    (w : K) : LinearMap.range f :=
  ⟨f (Subtype.val w), LinearMap.mem_range_self f _⟩

theorem rawImageMap_zero {V0 V1 : HSpace}
    (f : V0.carrier →ₗ[ℝ] V1.carrier) (K : Submodule ℝ V0.carrier) :
    rawImageMap f K 0 = 0 :=
  Subtype.ext (by simp [rawImageMap])

theorem rawImageMap_sum {V0 V1 : HSpace}
    (f : V0.carrier →ₗ[ℝ] V1.carrier) (K : Submodule ℝ V0.carrier)
    {iota : Type} (s : Finset iota) (c : iota → ℝ) (v : iota → K) :
    rawImageMap f K (∑ i ∈ s, c i • v i) =
      ∑ i ∈ s, c i • rawImageMap f K (v i) :=
  Subtype.ext (by
    simp [rawImageMap, Submodule.coe_sum, Submodule.coe_smul,
      map_sum, map_smul])

theorem raw_cobAgree_map_list {V0 V1 : HSpace}
    (f : V0.carrier →ₗ[ℝ] V1.carrier) (K : Submodule ℝ V0.carrier)
    (source target : List K) (a : FlatArray)
    (htarget : target.length = source.length)
    (halen : a.length = source.length * source.length)
    (hsum : forall j : Fin source.length,
      source.getD j.val 0 = ∑ i : Fin source.length,
        a.get (j.val * source.length + i.val) • target.getD i.val 0) :
    (target.map (rawImageMap f K)).length =
        (source.map (rawImageMap f K)).length /\
      a.length = (source.map (rawImageMap f K)).length *
        (source.map (rawImageMap f K)).length /\
      forall j : Fin (source.map (rawImageMap f K)).length,
        (source.map (rawImageMap f K)).getD j.val 0 =
          ∑ i : Fin (source.map (rawImageMap f K)).length,
            a.get (j.val * (source.map (rawImageMap f K)).length + i.val) •
              (target.map (rawImageMap f K)).getD i.val 0 := by
  have hlen : (source.map (rawImageMap f K)).length = source.length := by
    simp
  refine ⟨by simp [htarget], by simp [halen], ?_⟩
  intro j
  have hj : j.val < source.length := hlen ▸ j.isLt
  rw [show (0 : LinearMap.range f) = rawImageMap f K 0 from
    (rawImageMap_zero f K).symm]
  simp only [List.getD_map, List.length_map]
  rw [Fin.raw_sum_cast_of_eq hlen]
  simp only [Fin.coe_cast]
  have e := hsum ⟨j.val, hj⟩
  simp only [Fin.val_mk] at e
  rw [e, rawImageMap_sum]

theorem Basis.raw_sof_image_of_coker
    {b : Basis} {s0 s1 : Space} {e : Term}
    (hsof : Basis.sof b = .coker s0 s1 e) :
    Basis.sof (.image b) = .img s0 s1 e := by
  simp [Basis.sof, hsof]

theorem raw_arm_cob_image
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b0' : Basis} {env : ValExpr}
    (_hbSrc : Basis.BasisValid Gamma (.image b0))
    (_hbTgt : Basis.BasisValid Gamma (.image b0'))
    (hcoker : exists s0 s1 e, Basis.sof b0 = .coker s0 s1 e)
    (h : S.Cob Gamma Psi b0 env b0')
    (ih : RawMCobSubctx orc Gamma Psi b0 env b0') :
    RawMCobSubctx orc Gamma Psi (.image b0) env (.image b0') := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨s0, s1, e, hsof⟩ := hcoker
  have hsof' : Basis.sof b0' = .coker s0 s1 e :=
    (S.Cob.sof_eq h).symm.trans hsof
  have hAgree := ih hsub rho Delta' Gamma' sigma GammaV hle hc
  unfold CobAgree at hAgree ⊢
  dsimp only at hAgree ⊢
  rw [hsof] at hAgree
  rw [Basis.raw_sof_image_of_coker hsof]
  obtain ⟨htarget, a, ha, halen, hsum⟩ := hAgree
  have hSource :
      (denotBasis sigma (.image b0)).atSpace
        (denotSpace sigma (.img s0 s1 e)) =
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (.coker s0 s1 e))).map
        (rawImageMap
          ((denotTerm sigma e).asLinMap
            (denotSpace sigma s0) (denotSpace sigma s1))
          (Submodule.orthRel (denotSpace sigma s0).innerProduct
            (LinearMap.ker ((denotTerm sigma e).asLinMap
              (denotSpace sigma s0) (denotSpace sigma s1))))) := by
    simp only [denotBasis]
    split
    · rename_i heq
      rw [hsof] at heq
      cases heq
      exact BasisDenot.atSpace_vecs_self _ _
    · rename_i heq
      exact (heq _ _ _ hsof).elim
  have hTarget :
      (denotBasis sigma (.image b0')).atSpace
        (denotSpace sigma (.img s0 s1 e)) =
      ((denotBasis sigma b0').atSpace
        (denotSpace sigma (.coker s0 s1 e))).map
        (rawImageMap
          ((denotTerm sigma e).asLinMap
            (denotSpace sigma s0) (denotSpace sigma s1))
          (Submodule.orthRel (denotSpace sigma s0).innerProduct
            (LinearMap.ker ((denotTerm sigma e).asLinMap
              (denotSpace sigma s0) (denotSpace sigma s1))))) := by
    simp only [denotBasis]
    split
    · rename_i heq
      rw [hsof'] at heq
      cases heq
      exact BasisDenot.atSpace_vecs_self _ _
    · rename_i heq
      exact (heq _ _ _ hsof').elim
  rw [hSource, hTarget]
  obtain ⟨h1, h2, h3⟩ := raw_cobAgree_map_list _ _ _ _ a
    htarget halen hsum
  exact ⟨h1, a, ha, h2, h3⟩

/-! ## Paired closed constructors -/

theorem raw_arm_cob_facts_refl
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {sv : ValSpace}
    (hb : Basis.BasisValid Gamma b)
    (htof : Basis.tof b = .space (Basis.sof b))
    (hsv : S.Space Gamma Psi (Basis.sof b) sv)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) sv) :
    RawCobFactsSubctx orc Gamma Psi b
      (.reshap (.idelta sv) (.space (.tprod sv sv))
        (.space (.tprod sv sv))) b :=
  ⟨raw_arm_cob_refl hb htof hsv ihSpace,
    raw_arm_cob_infer_refl hb htof ihSpace⟩

theorem raw_arm_cob_facts_image
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b0' : Basis} {env : ValExpr}
    (hbSrc : Basis.BasisValid Gamma (.image b0))
    (hbTgt : Basis.BasisValid Gamma (.image b0'))
    (hcoker : exists s0 s1 e, Basis.sof b0 = .coker s0 s1 e)
    (h : S.Cob Gamma Psi b0 env b0')
    (ih : RawCobFactsSubctx orc Gamma Psi b0 env b0') :
    RawCobFactsSubctx orc Gamma Psi (.image b0) env (.image b0') :=
  ⟨raw_arm_cob_image hbSrc hbTgt hcoker h ih.agree,
    raw_arm_cob_infer_image hbSrc hcoker ih.infer⟩

/-! ## Transitive COB agreement -/

theorem raw_denotValB_semS_mtm_get
    (orc : FFSOracleSem) (rho : ValEnvSem)
    {env0 env1 : ValExpr} {a a0 a1 : FlatArray}
    {sv sa sb : ValSpace} {n : Nat}
    (_henv0 : denotValB_semS orc rho [] [] env0 = .ok (.array a0))
    (henv1 : denotValB_semS orc rho [] [] env1 = .ok (.array a1))
    (hreshape : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env0 (.tprod sv sv)) = .ok (.array a0))
    (hout : denotValB_semS orc rho [] []
      (.mtm 0 0 sv sv env1 (ValExpr.reshapBase env0 (.tprod sv sv))) =
        .ok (.array a))
    (hsab : ValExpr.inferSpaceCtx [] env1 = .tprod sa sb)
    (hb : ValSpace.dof (orc rho [] []) sb = n)
    (hsv : ValSpace.dof (orc rho [] []) sv = n)
    {j i : Nat} (hj : j < n) (hi : i < n) :
    a.get (j * n + i) =
      ∑ k ∈ Finset.range n,
        a1.get (n * k + i) * a0.get (n * j + k) := by
  obtain ⟨hdiv, hmod⟩ := Nat.raw_rowMajor_div_mod hj hi
  have hlt := Nat.raw_rowMajor_lt hj hi
  have hnle : ¬ (n * n ≤ j * n + i) := Nat.not_le.mpr hlt
  rw [denotValB_semS.eq_13, henv1, hreshape] at hout
  simp only [ValValSem.bindArrays, ValValSem.bindArray] at hout
  split at hout <;> try contradiction
  injection hout with hout
  injection hout with hout
  subst a
  simp only [ValExpr.reshapBase, ValExpr.inferSpaceCtx, ValTy.spaceOf,
    hsab, ValSpace.dof_tprod, hb, hsv, FlatArray.get_ofFn, hlt,
    if_true, ge_iff_le, hnle, if_false, hdiv, hmod]

theorem raw_cobAgree_trans_list {V : HSpace}
    (source middle target : List V.carrier) (a a0 a1 : FlatArray)
    (hsum0 : forall j : Fin source.length,
      source.getD j.val 0 = ∑ i : Fin source.length,
        a0.get (j.val * source.length + i.val) • middle.getD i.val 0)
    (hsum1 : forall j : Fin source.length,
      middle.getD j.val 0 = ∑ i : Fin source.length,
        a1.get (j.val * source.length + i.val) • target.getD i.val 0)
    (hget : forall j i, j < source.length -> i < source.length ->
      a.get (j * source.length + i) =
        ∑ k ∈ Finset.range source.length,
          a1.get (source.length * k + i) *
            a0.get (source.length * j + k)) :
    forall j : Fin source.length,
      source.getD j.val 0 = ∑ i : Fin source.length,
        a.get (j.val * source.length + i.val) • target.getD i.val 0 := by
  intro j
  have hr :
      (∑ i : Fin source.length,
        a.get (j.val * source.length + i.val) • target.getD i.val 0) =
      ∑ i : Fin source.length,
        (∑ k ∈ Finset.range source.length,
          a1.get (source.length * k + i.val) *
            a0.get (source.length * j.val + k)) • target.getD i.val 0 :=
    Finset.sum_congr rfl (fun i _ => by rw [hget _ _ j.isLt i.isLt])
  rw [hr, hsum0 j]
  simp only [hsum1, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  rw [Fin.sum_univ_eq_sum_range
    (fun n =>
      (a0.get (j.val * source.length + n) *
        a1.get (n * source.length + o.val)) • target.getD o.val 0)
    source.length]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  rw [mul_comm (a0.get _) (a1.get _),
    Nat.mul_comm source.length n, Nat.mul_comm source.length j.val]

theorem raw_arm_cob_trans
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b2 : Basis} {env0 env1 : ValExpr} {sv : ValSpace}
    (hinfer1 : RawCobInferSubctx orc Gamma Psi env1 b1)
    (hb0 : Basis.BasisValid Gamma b0)
    (_hb2 : Basis.BasisValid Gamma b2)
    (h0 : S.Cob Gamma Psi b0 env0 b1)
    (_h1 : S.Cob Gamma Psi b1 env1 b2)
    (_hsv : S.Space Gamma Psi (Basis.sof b0) sv)
    (ih0 : RawMCobSubctx orc Gamma Psi b0 env0 b1)
    (ih1 : RawMCobSubctx orc Gamma Psi b1 env1 b2)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv) :
    RawMCobSubctx orc Gamma Psi b0
      (.mtm 0 0 sv sv env1
        (ValExpr.reshapBase env0 (.tprod sv sv))) b2 := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hsof0 := S.Cob.sof_eq h0
  obtain ⟨_, hlen⟩ := raw_cob_basis_length orc hb0
    ihSpace hsub hle hc
  obtain ⟨sa, sb, hsab, hna, hnb⟩ :=
    hinfer1 hsub rho Delta' Gamma' sigma GammaV hle hc
  have ha0 := ih0 hsub rho Delta' Gamma' sigma GammaV hle hc
  have ha1 := ih1 hsub rho Delta' Gamma' sigma GammaV hle hc
  unfold CobAgree at ha0 ha1 ⊢
  dsimp only at ha0 ha1 ⊢
  rw [← hsof0] at ha1 hna hnb
  obtain ⟨hmiddleLen, a0, ha0Eval, ha0Len, hsum0⟩ := ha0
  obtain ⟨htargetLen, a1, ha1Eval, ha1Len, hsum1⟩ := ha1
  set source := (denotBasis sigma b0).atSpace
    (denotSpace sigma (Basis.sof b0)) with hsource
  set middle := (denotBasis sigma b1).atSpace
    (denotSpace sigma (Basis.sof b0)) with hmiddle
  set target := (denotBasis sigma b2).atSpace
    (denotSpace sigma (Basis.sof b0)) with htarget
  rw [hmiddleLen] at hsum1 htargetLen hna hnb ha1Len
  have hn : ValSpace.dof (orc rho [] []) sv = source.length :=
    hlen.symm
  have ha0Length : a0.length = source.length * source.length := by
    simpa [source] using ha0Len
  have hreshape : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env0 (.tprod sv sv)) = .ok (.array a0) := by
    have ha0Length' : a0.length =
        ValSpace.dof (orc rho [] []) (.tprod sv sv) := by
      simpa [ValSpace.dof_tprod, hn] using ha0Length
    exact denotValB_semS_reshap_space_ok orc rho [] [] env0
      (.tprod sv sv) a0 ha0Eval ha0Length'
  have houtDof : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx []
        (.mtm 0 0 sv sv env1
          (ValExpr.reshapBase env0 (.tprod sv sv)))) =
      source.length * source.length := by
    simp only [ValExpr.reshapBase, ValExpr.inferSpaceCtx, ValTy.spaceOf,
      hsab, ValSpace.dof_tprod, hn, hnb]
  have hguard : ValueShape.mtm (orc rho [] []) sv
      (ValExpr.inferSpaceCtx [] env1)
      (ValExpr.inferSpaceCtx [] (ValExpr.reshapBase env0 (.tprod sv sv))) a1 a0 := by
    simp only [hsab, ValExpr.reshapBase, ValExpr.inferSpaceCtx, ValTy.spaceOf,
      ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, hn, hna, hnb]
    exact ⟨⟨ha1Len, ha0Length⟩, trivial, trivial⟩
  obtain ⟨a, hval⟩ : exists a, denotValB_semS orc rho [] []
      (.mtm 0 0 sv sv env1
        (ValExpr.reshapBase env0 (.tprod sv sv))) = .ok (.array a) := by
    rw [denotValB_semS.eq_13, ha1Eval, hreshape]
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hguard]
    exact ⟨_, rfl⟩
  have halen : a.length = source.length * source.length := by
    rw [denotValB_semS.eq_13, ha1Eval, hreshape] at hval
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hguard] at hval
    injection hval with hval
    injection hval with hval
    subst a
    simp [houtDof]
  have hget : forall j i, j < source.length -> i < source.length ->
      a.get (j * source.length + i) =
        ∑ k ∈ Finset.range source.length,
          a1.get (source.length * k + i) *
            a0.get (source.length * j + k) := by
    intro j i hj hi
    exact raw_denotValB_semS_mtm_get orc rho ha0Eval ha1Eval
      hreshape hval hsab hnb hn hj hi
  exact ⟨htargetLen, a, hval, halen,
    raw_cobAgree_trans_list source middle target a a0 a1
      hsum0 hsum1 hget⟩

theorem raw_arm_cob_facts_trans
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b2 : Basis} {env0 env1 : ValExpr} {sv : ValSpace}
    (hb0 : Basis.BasisValid Gamma b0)
    (hb2 : Basis.BasisValid Gamma b2)
    (h0 : S.Cob Gamma Psi b0 env0 b1)
    (h1 : S.Cob Gamma Psi b1 env1 b2)
    (hsv : S.Space Gamma Psi (Basis.sof b0) sv)
    (ih0 : RawCobFactsSubctx orc Gamma Psi b0 env0 b1)
    (ih1 : RawCobFactsSubctx orc Gamma Psi b1 env1 b2)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv) :
    RawCobFactsSubctx orc Gamma Psi b0
      (.mtm 0 0 sv sv env1
        (ValExpr.reshapBase env0 (.tprod sv sv))) b2 :=
  ⟨raw_arm_cob_trans ih1.infer hb0 hb2 h0 h1 hsv
      ih0.agree ih1.agree ihSpace,
    raw_arm_cob_infer_trans hb0 h0 h1 hsv ihSpace ih1.infer⟩

end GLang
