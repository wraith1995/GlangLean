import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMotives

namespace GLang.PartialAdequacy

/-- A Pi-valued result has no inferred-space obligation. -/
theorem rawMDof_pi_vacuous
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {tauV0 tauV1 : ValTy} :
    MDofSubctx orc Gamma Psi v (.piTy tauV0 tauV1) := by
  intro sv h
  cases h

/-- Any value expression that carries its result type as its inferred-space
annotation has a definitionally closed companion. -/
theorem rawMDof_annotated
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {mk : ValTy -> ValExpr} {tauV : ValTy}
    (hinfer : forall sv, tauV = .space sv ->
      ValExpr.inferSpaceCtx [] (mk tauV) = sv) :
    MDofSubctx orc Gamma Psi (mk tauV) tauV := by
  intro sv htau Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [hinfer sv htau]

/-- `reshape` records the target type, so its inferred-space companion does
not consume the operand trace or operand companion. -/
theorem arm_reshape_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {target source : ValTy} :
    MDofSubctx orc Gamma Psi (.reshap v target source) target := by
  intro sv htau Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases htau
  rfl

/-- `nllam` is Pi-valued, so the companion is vacuous independently of its
opened body. -/
theorem arm_nllam_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {tauV0 tauV1 : ValTy} {body : ValExpr} :
    MDofSubctx orc Gamma Psi
      (.vlam tauV0 tauV1 body) (.piTy tauV0 tauV1) :=
  rawMDof_pi_vacuous (Psi := Psi)

/-- `appN_val` records the separately compiled result type in `.appV`; no
operand `mDof` fact is needed. -/
theorem arm_appN_val_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {funExpr argExpr : ValExpr} {tauOut : ValTy} :
    MDofSubctx orc Gamma Psi
      (.applyAt funExpr argExpr tauOut) tauOut := by
  intro sv htau Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases htau
  rfl

/-! ## Exact nonlinear/linear lookup -/

/-- The variable proof is shared by the linear and nonlinear source-variable
rules.  The creation record supplies `inferSpaceCtx`; transported stored raw
dimensions and current exact-basis type dimensions meet at the same source
shape. -/
theorem arm_var_dof
    {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} {tauV : ValTy}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (hTy : S.TyAt Gamma Psi b tauV)
    (ihTy : MTyAtSubctx orc Gamma Psi b tauV) :
    MDofSubctx orc Gamma Psi v tauV := by
  intro sv htau Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  subst tauV
  have hlookup' : EvalCtx.lookup Psi' (x, b) = some v :=
    hsub (x, b) v hlookup
  have hmem : (x, b) ∈ Psi' := Finmap.mem_of_lookup_eq_some hlookup'
  obtain ⟨v0, tauStored, xs0, yV0, Gamma0, Psi0, hPsi,
      hsigmaCurrent, hStoredTy, hinferSpace, hfvb, hfvTy, hdenCurrent,
      hagreeCurrent, hdimsStored⟩ := hc.history.stored_raw_current hirr hmem
  have hv0 : v0 = v := Option.some.inj (hPsi.symm.trans hlookup')
  subst v0
  have hdimsTarget : DimsAt orc sigma rho [] [] []
      (Basis.tof b) (.space sv) (denotBasis sigma b) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨s, htofS, _hspace⟩ := hTy.toTy.space_inv
  have htof : Basis.tof b = .space (Basis.sof b) := by
    calc
      Basis.tof b = .space s := htofS
      _ = .space (Basis.sof b) :=
        congrArg Ty.space (Basis.sof_of_tof_space htofS).symm
  rw [htof] at hdimsStored hdimsTarget
  cases tauStored with
  | piTy tau0 tau1 =>
      simpa only [DimsAt] using hdimsStored
  | space svStored =>
      simp only [DimsAt] at hdimsStored hdimsTarget
      rw [hinferSpace.spaceEq]
      exact hdimsStored.trans hdimsTarget.symm

theorem arm_var_nlin_dof
    {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} {tauV : ValTy}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (_hGamma : Gamma.lookup x = some (Basis.tof b))
    (_hbv : Basis.BasisValid Gamma b)
    (hTy : S.TyAt Gamma Psi b tauV)
    (ihTy : MTyAtSubctx orc Gamma Psi b tauV) :
    MDofSubctx orc Gamma Psi v tauV :=
  arm_var_dof hirr hlookup hTy ihTy

theorem arm_var_lin_dof
    {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} {s : Space} {tauV : ValTy}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (_htof : Basis.tof b = .space s)
    (_hbv : Basis.BasisValid Gamma b)
    (hTy : S.TyAt Gamma Psi b tauV)
    (ihTy : MTyAtSubctx orc Gamma Psi b tauV) :
    MDofSubctx orc Gamma Psi v tauV :=
  arm_var_dof hirr hlookup hTy ihTy

/-- Promotion only enlarges the source nonlinear context. -/
theorem arm_promote_dof
    {orc : PartialFFSOracleSem} {Gamma Gamma'' : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {tauV : ValTy} (lin : LCtx)
    (hdisj : Finmap.Disjoint lin.toNL Gamma'')
    (hleP : NLCtxIncl Gamma Gamma'')
    (ih : MDofSubctx orc Gamma Psi v tauV) :
    MDofSubctx orc (lin.toNL ∪ Gamma'') Psi v tauV := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  apply ih hspace hsub rho Delta' Gamma' sigma GammaV ?_ hc
  intro x tau hx
  have hx'' : Gamma''.lookup x = some tau := hleP x tau hx
  apply hle x tau
  have hnot : x ∉ lin.toNL := fun hlin =>
    hdisj x hlin (Finmap.mem_of_lookup_eq_some hx'')
  rw [Finmap.lookup_union_right hnot]
  exact hx''

/-- Scalar multiplication inherits the vector operand's inferred shape. -/
theorem arm_scale_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v0 v1 : ValExpr} {sv : ValSpace}
    (ih1 : MDofSubctx orc Gamma Psi v1 (.space sv)) :
    MDofSubctx orc Gamma Psi (.scale v0 v1) (.space sv) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  simpa only [ValExpr.inferSpaceCtx] using
    ih1 rfl hsub rho Delta' Gamma' sigma GammaV hle hc

/-- Addition carries its result realization explicitly. -/
theorem arm_add_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v0 v1 : ValExpr} {sv : ValSpace} :
    MDofSubctx orc Gamma Psi (.vadd sv v0 v1) (.space sv) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- Direct-sum inference composes the two child shape companions. -/
theorem arm_dsumE_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v0 v1 : ValExpr} {sv0 sv1 : ValSpace}
    (ih0 : MDofSubctx orc Gamma Psi v0 (.space sv0))
    (ih1 : MDofSubctx orc Gamma Psi v1 (.space sv1)) :
    MDofSubctx orc Gamma Psi (.dsumE v0 v1)
      (.space (.dsum sv0 sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  have hd0 := ih0 rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  have hd1 := ih1 rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  simp only [ValExpr.inferSpaceCtx, ValSpace.shpOfPartial]
  simp only [ValSpace.dofPartial, hd0, hd1]

/-- Tensor-product inference composes the two child shape companions. -/
theorem arm_tprodE_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v0 v1 : ValExpr} {sv0 sv1 : ValSpace}
    (ih0 : MDofSubctx orc Gamma Psi v0 (.space sv0))
    (ih1 : MDofSubctx orc Gamma Psi v1 (.space sv1)) :
    MDofSubctx orc Gamma Psi (.tprodE v0 v1)
      (.space (.tprod sv0 sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  have hd0 := ih0 rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  have hd1 := ih1 rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  simp only [ValExpr.inferSpaceCtx, ValSpace.shpOfPartial]
  simp only [ValSpace.dofPartial, hd0, hd1]

/-- The one-dimensional pseudo-inverse operand is explicitly reshaped, so
the output inference is definitional and consumes no child companion. -/
theorem arm_pinvD_std_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {sv1 : ValSpace} :
    MDofSubctx orc Gamma Psi
      (.pinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1)))
      (.space (.tprod .real sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- Generalized one-dimensional pseudo-inverse is likewise fixed by its
explicit operand reshape. -/
theorem arm_pinvD_gpinv_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v env0 env1 : ValExpr} {sv1 : ValSpace} :
    MDofSubctx orc Gamma Psi
      (.gpinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1))
        env1 env0)
      (.space (.tprod .real sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- Standard inner product is an explicitly realized identity tensor. -/
theorem arm_inner_std_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {sv : ValSpace} :
    MDofSubctx orc Gamma Psi (.idelta sv)
      (.space (.tprod sv sv)) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- A base reshape is the common annotated producer used by linear
application and both linear-lambda assembly rules. -/
theorem rawMDof_reshapBase
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {sv : ValSpace} :
    MDofSubctx orc Gamma Psi (ValExpr.reshapBase v sv)
      (.space sv) := by
  apply arm_reshape_dof

/-- Tensor linear application records the declared output realization in its
outer reshape; no child companion is needed to produce this field. -/
theorem arm_appL_lin_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {env0 env1 : ValExpr} {sv0 sv1 : ValSpace} :
    MDofSubctx orc Gamma Psi
      (ValExpr.reshapBase (.ttv sv0 env0 env1) sv1) (.space sv1) :=
  rawMDof_reshapBase

/-- Inner-product linear application infers `real` definitionally from the
explicit tensor reshape of the functional. -/
theorem arm_appI_lin_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {env0 env1 : ValExpr} {sv : ValSpace} :
    MDofSubctx orc Gamma Psi
      (.ttv sv
        (.reshap env0 (.space (.tprod sv .real)) (.space sv)) env1)
      (.space .real) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- Change of basis has a reshaped square map as its first contraction
operand, which fixes the result inference to `sv`. -/
theorem arm_cob_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v env0 : ValExpr} {sv : ValSpace} :
    MDofSubctx orc Gamma Psi
      (.ttv sv (ValExpr.reshapBase env0 (.tprod sv sv))
        (ValExpr.reshapBase v sv)) (.space sv) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- Both frame re-anchoring and frame eta reconstruction are Pi-valued. -/
theorem arm_frame_reanchor_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {body : ValExpr} {tauV0 tauV1 : ValTy} :
    MDofSubctx orc Gamma Psi (.vlam tauV0 tauV1 body)
      (.piTy tauV0 tauV1) :=
  rawMDof_pi_vacuous

theorem arm_frame_eta_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {body : ValExpr} {tauV0 tauV1 : ValTy} :
    MDofSubctx orc Gamma Psi (.vlam tauV0 tauV1 body)
      (.piTy tauV0 tauV1) :=
  rawMDof_pi_vacuous

/-- Linear-lambda assembly records its tensor output while retaining the
actual empty-sum source annotation. -/
theorem arm_llam_assemble_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {sv0 sv1 : ValSpace} {es : List ValExpr} :
    MDofSubctx orc Gamma Psi
      (ValExpr.sumAt sv0 es (.tprod sv0 sv1))
      (.space (.tprod sv0 sv1)) := by
  apply arm_reshape_dof

/-- Real-codomain assembly records its output with the actual sum source. -/
theorem arm_llam_assemble_real_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {sv : ValSpace} {es : List ValExpr} :
    MDofSubctx orc Gamma Psi (ValExpr.sumAt sv es sv)
      (.space sv) := by
  apply arm_reshape_dof

theorem arm_zero_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {sv : ValSpace} :
    MDofSubctx orc Gamma Psi (.zero sv) (.space sv) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

theorem arm_rlit_dof
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx} {r : ℝ} :
    MDofSubctx orc Gamma Psi (.rlit r) (.space .real) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

end GLang.PartialAdequacy
