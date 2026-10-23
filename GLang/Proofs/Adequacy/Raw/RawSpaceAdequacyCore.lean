import GLang.Proofs.Adequacy.Raw.RawDofAdequacyCore

namespace GLang

/-! ## Motive -/

/-- Space adequacy stable under lookup-preserving evaluator-context extension. -/
def RawMSpaceSubctx (orc : FFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (s : Space) (sv : ValSpace) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    RawMSpace orc (RawTypedConsistent orc) Gamma Psi' s sv

/-- The space projection required by the exact-basis type induction. -/
def RawSpaceClaimSubctx (orc : FFSOracleSem) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {s : Space} {sv : ValSpace},
    S.Space Gamma Psi s sv -> RawMSpaceSubctx orc Gamma Psi s sv

/-- Forget evaluator-context polymorphism at the current context. -/
theorem RawMSpaceSubctx.current
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {sv : ValSpace}
    (h : RawMSpaceSubctx orc Gamma Psi s sv) :
    RawMSpace orc (RawTypedConsistent orc) Gamma Psi s sv :=
  h (EvalCtx.Subctx.refl Psi)

/-! ## Source-shape dimension bridge -/

/-- Multiplying a source shape yields the dimension of its denoted space. -/
theorem raw_srcShp_foldr (sigma : DEnv) (DeltaS : List DVal) :
    forall s : Space,
      (srcShp sigma DeltaS s).foldr (· * ·) 1 =
        Module.finrank ℝ (denotSpaceAux sigma DeltaS s).carrier
  | .empty => by
      simp only [srcShp, List.foldr, denotSpaceAux]
      exact (Module.finrank_zero_of_subsingleton
        (R := ℝ) (M := PUnit)).symm
  | .real => by
      simp only [srcShp, List.foldr, denotSpaceAux]
      exact (Module.finrank_self ℝ).symm
  | .dual s => by
      have ih := raw_srcShp_foldr sigma DeltaS s
      simp only [srcShp, denotSpaceAux]
      rw [ih]
      exact (Subspace.dual_finrank_eq
        (K := ℝ) (V := (denotSpaceAux sigma DeltaS s).carrier)).symm
  | .dsum _ _ => by
      simp only [srcShp, List.foldr, denotSpaceAux, Nat.mul_one]
      exact (Module.finrank_prod (R := ℝ)).symm
  | .tprod _ _ => by
      simp only [srcShp, List.foldr, denotSpaceAux, Nat.mul_one]
      exact (Module.finrank_tensorProduct (R := ℝ)).symm
  | .ker _ _ _ => by simp [srcShp]
  | .coker _ _ _ => by simp [srcShp]
  | .img _ _ _ => by simp [srcShp]
  | .coimg _ _ _ => by simp [srcShp]

/-- A space-shape equality pins the semantic dimension to the source one. -/
theorem ValSpace.raw_dof_eq_finrank_of_shpOf
    {orc : FFSOracle} {sv : ValSpace} {sigma : DEnv}
    {DeltaS : List DVal} {s : Space}
    (h : ValSpace.shpOf orc sv = srcShp sigma DeltaS s) :
    ValSpace.dof orc sv =
      Module.finrank ℝ (denotSpaceAux sigma DeltaS s).carrier := by
  unfold ValSpace.dof
  rw [h]
  exact raw_srcShp_foldr sigma DeltaS s

/-! ## Structural `S.Space` arms -/

theorem raw_arm_space_real
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx} :
    RawMSpaceSubctx orc Gamma Psi .real .real := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  simp [srcShp]

theorem raw_arm_space_empty
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx} :
    RawMSpaceSubctx orc Gamma Psi .empty .empty := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  simp [srcShp]

theorem raw_arm_space_dual
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {sv : ValSpace}
    (_hs : Nonempty (SValid Gamma (.dual s)))
    (_h : S.Space Gamma Psi s sv)
    (ih : RawMSpaceSubctx orc Gamma Psi s sv) :
    RawMSpaceSubctx orc Gamma Psi (.dual s) sv := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hshape := ih hsub rho Delta' Gamma' sigma GammaV hle hc
  simpa [srcShp] using hshape

theorem raw_arm_space_tprod
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (_hs : Nonempty (SValid Gamma (.tprod s0 s1)))
    (_h0 : S.Space Gamma Psi s0 sv0)
    (_h1 : S.Space Gamma Psi s1 sv1)
    (ih0 : RawMSpaceSubctx orc Gamma Psi s0 sv0)
    (ih1 : RawMSpaceSubctx orc Gamma Psi s1 sv1) :
    RawMSpaceSubctx orc Gamma Psi (.tprod s0 s1) (.tprod sv0 sv1) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [ValSpace.shpOf_tprod,
    ValSpace.raw_dof_eq_finrank_of_shpOf
      (ih0 hsub rho Delta' Gamma' sigma GammaV hle hc),
    ValSpace.raw_dof_eq_finrank_of_shpOf
      (ih1 hsub rho Delta' Gamma' sigma GammaV hle hc)]
  rfl

theorem raw_arm_space_dsum
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (_hs : Nonempty (SValid Gamma (.dsum s0 s1)))
    (_h0 : S.Space Gamma Psi s0 sv0)
    (_h1 : S.Space Gamma Psi s1 sv1)
    (ih0 : RawMSpaceSubctx orc Gamma Psi s0 sv0)
    (ih1 : RawMSpaceSubctx orc Gamma Psi s1 sv1) :
    RawMSpaceSubctx orc Gamma Psi (.dsum s0 s1) (.dsum sv0 sv1) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [ValSpace.shpOf_dsum,
    ValSpace.raw_dof_eq_finrank_of_shpOf
      (ih0 hsub rho Delta' Gamma' sigma GammaV hle hc),
    ValSpace.raw_dof_eq_finrank_of_shpOf
      (ih1 hsub rho Delta' Gamma' sigma GammaV hle hc)]
  rfl

/-! ## Exact-basis type arms -/

/-- The space-valued exact-basis type arm consumes its particular sibling
space IH; it does not require an external global space theorem. -/
theorem raw_arm_tyAt_space
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {sv : ValSpace}
    (htof : Basis.tof b = .space (Basis.sof b))
    (_hbv : Basis.BasisValid Gamma b)
    (_hs : S.Space Gamma Psi (Basis.sof b) sv)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) sv) :
    RawMTyAtSubctx orc Gamma Psi b (.space sv) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [htof]
  simpa only [RawAgreeDimsAt] using
    ihSpace hsub rho Delta' Gamma' sigma GammaV hle hc

/-- The dependent-frame exact-basis arm follows the same concrete frame basis
after every evaluator-context extension. -/
theorem raw_arm_tyAt_frame
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {tauV0 tauV1 : ValTy}
    (hbv : Basis.BasisValid Gamma (.frame b0 b1))
    (hdom : S.TyAt Gamma Psi b0 tauV0)
    (L : Finset Name)
    (hcod : forall y, y ∉ L ->
      S.TyAt (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauV0))
        (Basis.openVar y b1) (ValTy.openVar y tauV0 tauV1))
    (hisTy : Basis.IsTyBasis (.frame b0 b1))
    (ihdom : RawMTyAtSubctx orc Gamma Psi b0 tauV0)
    (ihcod : forall y, y ∉ L ->
      RawMTyAtSubctx orc
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauV0))
        (Basis.openVar y b1) (ValTy.openVar y tauV0 tauV1)) :
    RawMTyAtSubctx orc Gamma Psi (.frame b0 b1)
      (.piTy tauV0 tauV1) := by
  intro Psi' hsub
  exact rawMTyAt_frame
    (RawTypedConsistent.worldExtendNLAt
      hspec.toOracleSpec.fvIrrel)
    (fun hc => hc.evalCtxLc)
    hspec.rawBinderCoherent hbv (hdom.mono hsub) L
    (fun y hy => (hcod y hy).mono (hsub.extend y b0 (.var y tauV0)))
    hisTy
    (ihdom hsub)
    (fun y hy => ihcod y hy (hsub.extend y b0 (.var y tauV0)))

end GLang
