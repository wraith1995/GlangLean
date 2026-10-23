import GLang.Proofs.Value.Queries.ValueQueryConstructors
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyCore

namespace GLang

/-! ## Inferred-space companion motive -/

/-- The exact pair needed from each term induction hypothesis. -/
structure RawTermDofFactsSubctx (orc : FFSOracleSem) (Delta : LCtx)
    (Gamma : NLCtx) (Psi : EvalCtx) (e : Term) (b : Basis)
    (v : ValExpr) (tauV : ValTy) : Prop where
  trace : RawMTermTraceSubctx orc Delta Gamma Psi e b v tauV
  dof : RawMDofTraceSubctx orc Gamma Psi v tauV

/-! ## Constructor-independent arms -/

/-- A Pi-valued result has no inferred-space obligation. -/
theorem rawMDof_pi_vacuous
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {tauV0 tauV1 : ValTy} :
    RawMDofTraceSubctx orc Gamma Psi v (.piTy tauV0 tauV1) := by
  intro sv h
  cases h

/-- Any value expression that carries its result type as its inferred-space
annotation has a definitionally closed companion. -/
theorem rawMDof_annotated
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {mk : ValTy -> ValExpr} {tauV : ValTy}
    (hinfer : forall sv, tauV = .space sv ->
      ValExpr.inferSpaceCtx [] (mk tauV) = sv) :
    RawMDofTraceSubctx orc Gamma Psi (mk tauV) tauV := by
  intro sv htau Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [hinfer sv htau]

/-- `reshape` records the target type, so its inferred-space companion does
not consume the operand trace or operand companion. -/
theorem arm_reshape_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {target source : ValTy} :
    RawMDofTraceSubctx orc Gamma Psi (.reshap v target source) target := by
  intro sv htau Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases htau
  rfl

/-- `nllam` is Pi-valued, so the companion is vacuous independently of its
opened body. -/
theorem arm_nllam_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {tauV0 tauV1 : ValTy} {body : ValExpr} :
    RawMDofTraceSubctx orc Gamma Psi
      (.vlam tauV0 tauV1 body) (.piTy tauV0 tauV1) :=
  rawMDof_pi_vacuous (Psi := Psi)

/-- `appN_val` converts to the separately compiled result type explicitly; no
operand `mDof` fact is needed. -/
theorem arm_appN_val_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {funExpr argExpr : ValExpr} {tauOut : ValTy} :
    RawMDofTraceSubctx orc Gamma Psi
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
    {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} {tauV : ValTy}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (hTy : S.TyAt Gamma Psi b tauV)
    (ihTy : RawMTyAtSubctx orc Gamma Psi b tauV) :
    RawMDofTraceSubctx orc Gamma Psi v tauV := by
  intro sv htau Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  subst tauV
  have hlookup' : EvalCtx.lookup Psi' (x, b) = some v :=
    hsub (x, b) v hlookup
  have hmem : (x, b) ∈ Psi' := Finmap.mem_of_lookup_eq_some hlookup'
  obtain ⟨v0, tauStored, xs0, yV0, Gamma0, Psi0, hPsi,
      hsigmaCurrent, hStoredTy, hinferSpace, hfvb, hfvTy, hdenCurrent,
      hagreeCurrent, hdimsStored⟩ := hc.raw.stored_raw_current hirr hmem
  have hv0 : v0 = v := Option.some.inj (hPsi.symm.trans hlookup')
  subst v0
  have hdimsTarget : RawAgreeDimsAt orc sigma rho [] [] []
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
      simpa only [RawAgreeDimsAt] using hdimsStored
  | space svStored =>
      simp only [RawAgreeDimsAt] at hdimsStored hdimsTarget
      rw [hinferSpace.spaceEq]
      exact hdimsStored.trans hdimsTarget.symm

theorem arm_var_nlin_dof
    {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} {tauV : ValTy}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (_hGamma : Gamma.lookup x = some (Basis.tof b))
    (_hbv : Basis.BasisValid Gamma b)
    (hTy : S.TyAt Gamma Psi b tauV)
    (ihTy : RawMTyAtSubctx orc Gamma Psi b tauV) :
    RawMDofTraceSubctx orc Gamma Psi v tauV :=
  arm_var_dof hirr hlookup hTy ihTy

theorem arm_var_lin_dof
    {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} {s : Space} {tauV : ValTy}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (_htof : Basis.tof b = .space s)
    (_hbv : Basis.BasisValid Gamma b)
    (hTy : S.TyAt Gamma Psi b tauV)
    (ihTy : RawMTyAtSubctx orc Gamma Psi b tauV) :
    RawMDofTraceSubctx orc Gamma Psi v tauV :=
  arm_var_dof hirr hlookup hTy ihTy

/-! ## Shape-only infrastructure for the four FFS consumers -/

/-- Equal shapes imply equal total dimensions. -/
theorem dof_eq_of_shpOf_eq {orc : FFSOracle} {s s' : ValSpace}
    (h : ValSpace.shpOf orc s = ValSpace.shpOf orc s') :
    ValSpace.dof orc s = ValSpace.dof orc s' := by
  unfold ValSpace.dof
  rw [h]

/-- A space shape equal to a tensor shape must itself be a tensor. -/
theorem eq_tprod_of_shpOf_eq {orc : FFSOracle} {s a b : ValSpace}
    (h : ValSpace.shpOf orc s = ValSpace.shpOf orc (.tprod a b)) :
    exists sa sb, s = .tprod sa sb := by
  cases s with
  | tprod sa sb => exact ⟨sa, sb, rfl⟩
  | empty =>
      have hh := congrArg List.length h
      simp only [ValSpace.shpOf_empty, ValSpace.shpOf_tprod,
        List.length_cons, List.length_nil] at hh
      omega
  | real =>
      have hh := congrArg List.length h
      simp only [ValSpace.shpOf_real, ValSpace.shpOf_tprod,
        List.length_cons, List.length_nil] at hh
      omega
  | dsum s0 s1 =>
      have hh := congrArg List.length h
      simp only [ValSpace.shpOf_dsum, ValSpace.shpOf_tprod,
        List.length_cons, List.length_nil] at hh
      omega
  | ffs p s w =>
      have hh := congrArg List.length h
      simp only [ValSpace.shpOf_ffs, ValSpace.shpOf_tprod,
        List.length_cons, List.length_nil] at hh
      omega

/-- Tensor shape equality pins the dimensions of both factors. -/
theorem tprod_factor_dof_eq_of_shpOf_eq {orc : FFSOracle}
    {a b a' b' : ValSpace}
    (h : ValSpace.shpOf orc (.tprod a b) =
      ValSpace.shpOf orc (.tprod a' b')) :
    ValSpace.dof orc a = ValSpace.dof orc a' /\
      ValSpace.dof orc b = ValSpace.dof orc b' := by
  simp only [ValSpace.shpOf_tprod] at h
  exact ⟨(List.cons.inj h).1, (List.cons.inj (List.cons.inj h).2).1⟩

/-! ## Remaining structural producers for the term mutual -/

/-- Promotion only enlarges the source nonlinear context. -/
theorem arm_promote_dof
    {orc : FFSOracleSem} {Gamma Gamma'' : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {tauV : ValTy} (lin : LCtx)
    (hdisj : Finmap.Disjoint lin.toNL Gamma'')
    (hleP : NLCtxIncl Gamma Gamma'')
    (ih : RawMDofTraceSubctx orc Gamma Psi v tauV) :
    RawMDofTraceSubctx orc (lin.toNL ∪ Gamma'') Psi v tauV := by
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
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v0 v1 : ValExpr} {sv : ValSpace}
    (ih1 : RawMDofTraceSubctx orc Gamma Psi v1 (.space sv)) :
    RawMDofTraceSubctx orc Gamma Psi (.scale v0 v1) (.space sv) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  simpa only [ValExpr.inferSpaceCtx] using
    ih1 rfl hsub rho Delta' Gamma' sigma GammaV hle hc

/-- Addition carries its result realization explicitly. -/
theorem arm_add_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v0 v1 : ValExpr} {sv : ValSpace} :
    RawMDofTraceSubctx orc Gamma Psi (.vadd sv v0 v1) (.space sv) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- Direct-sum inference composes the two child shape companions. -/
theorem arm_dsumE_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v0 v1 : ValExpr} {sv0 sv1 : ValSpace}
    (ih0 : RawMDofTraceSubctx orc Gamma Psi v0 (.space sv0))
    (ih1 : RawMDofTraceSubctx orc Gamma Psi v1 (.space sv1)) :
    RawMDofTraceSubctx orc Gamma Psi (.dsumE v0 v1)
      (.space (.dsum sv0 sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  have hd0 := ih0 rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  have hd1 := ih1 rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  simp only [ValExpr.inferSpaceCtx, ValSpace.shpOf_dsum]
  rw [dof_eq_of_shpOf_eq hd0, dof_eq_of_shpOf_eq hd1]

/-- Tensor-product inference composes the two child shape companions. -/
theorem arm_tprodE_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v0 v1 : ValExpr} {sv0 sv1 : ValSpace}
    (ih0 : RawMDofTraceSubctx orc Gamma Psi v0 (.space sv0))
    (ih1 : RawMDofTraceSubctx orc Gamma Psi v1 (.space sv1)) :
    RawMDofTraceSubctx orc Gamma Psi (.tprodE v0 v1)
      (.space (.tprod sv0 sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  have hd0 := ih0 rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  have hd1 := ih1 rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  simp only [ValExpr.inferSpaceCtx, ValSpace.shpOf_tprod]
  rw [dof_eq_of_shpOf_eq hd0, dof_eq_of_shpOf_eq hd1]

/-- Tensor pseudo-inverse swaps the two child-inferred factors. -/
theorem arm_pinvT_std_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {sv0 sv1 : ValSpace}
    (ih : RawMDofTraceSubctx orc Gamma Psi v
      (.space (.tprod sv1 sv0))) :
    RawMDofTraceSubctx orc Gamma Psi (.pinv v)
      (.space (.tprod sv0 sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  have hd := ih rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨a, b, hab⟩ := eq_tprod_of_shpOf_eq hd
  rw [hab] at hd
  have hfac := tprod_factor_dof_eq_of_shpOf_eq hd
  have hinfer : ValExpr.inferSpaceCtx [] (.pinv v) = .tprod b a := by
    rw [ValExpr.inferSpaceCtx, hab]
  rw [hinfer]
  simp only [ValSpace.shpOf_tprod]
  rw [hfac.2, hfac.1]

/-- Generalized tensor pseudo-inverse has the same inferred-space swap; the
two inner-product operands do not participate in this conclusion. -/
theorem arm_pinvT_gpinv_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v env0 env1 : ValExpr} {sv0 sv1 : ValSpace}
    (ih : RawMDofTraceSubctx orc Gamma Psi v
      (.space (.tprod sv1 sv0))) :
    RawMDofTraceSubctx orc Gamma Psi (.gpinv v env1 env0)
      (.space (.tprod sv0 sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  have hd := ih rfl hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨a, b, hab⟩ := eq_tprod_of_shpOf_eq hd
  rw [hab] at hd
  have hfac := tprod_factor_dof_eq_of_shpOf_eq hd
  have hinfer : ValExpr.inferSpaceCtx [] (.gpinv v env1 env0) =
      .tprod b a := by
    rw [ValExpr.inferSpaceCtx, hab]
  rw [hinfer]
  simp only [ValSpace.shpOf_tprod]
  rw [hfac.2, hfac.1]

/-- The one-dimensional pseudo-inverse operand is explicitly reshaped, so
the output inference is definitional and consumes no child companion. -/
theorem arm_pinvD_std_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {sv1 : ValSpace} :
    RawMDofTraceSubctx orc Gamma Psi
      (.pinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1)))
      (.space (.tprod .real sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- Generalized one-dimensional pseudo-inverse is likewise fixed by its
explicit operand reshape. -/
theorem arm_pinvD_gpinv_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v env0 env1 : ValExpr} {sv1 : ValSpace} :
    RawMDofTraceSubctx orc Gamma Psi
      (.gpinv (.reshap v (.space (.tprod sv1 .real)) (.space sv1))
        env1 env0)
      (.space (.tprod .real sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- Standard inner product is an explicitly realized identity tensor. -/
theorem arm_inner_std_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {sv : ValSpace} :
    RawMDofTraceSubctx orc Gamma Psi (.idelta sv)
      (.space (.tprod sv sv)) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- A base reshape is the common annotated producer used by linear
application and both linear-lambda assembly rules. -/
theorem rawMDof_reshapBase
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v : ValExpr} {sv : ValSpace} :
    RawMDofTraceSubctx orc Gamma Psi (ValExpr.reshapBase v sv)
      (.space sv) := by
  apply arm_reshape_dof

/-- Tensor linear application records the declared output realization in its
outer reshape; no child companion is needed to produce this field. -/
theorem arm_appL_lin_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {env0 env1 : ValExpr} {sv0 sv1 : ValSpace} :
    RawMDofTraceSubctx orc Gamma Psi
      (ValExpr.reshapBase (.ttv sv0 env0 env1) sv1) (.space sv1) :=
  rawMDof_reshapBase

/-- Inner-product linear application infers `real` definitionally from the
explicit tensor reshape of the functional. -/
theorem arm_appI_lin_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {env0 env1 : ValExpr} {sv : ValSpace} :
    RawMDofTraceSubctx orc Gamma Psi
      (.ttv sv
        (.reshap env0 (.space (.tprod sv .real)) (.space sv)) env1)
      (.space .real) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- Change of basis has a reshaped square map as its first contraction
operand, which fixes the result inference to `sv`. -/
theorem arm_cob_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {v env0 : ValExpr} {sv : ValSpace} :
    RawMDofTraceSubctx orc Gamma Psi
      (.ttv sv (ValExpr.reshapBase env0 (.tprod sv sv))
        (ValExpr.reshapBase v sv)) (.space sv) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- Both frame re-anchoring and frame eta reconstruction are Pi-valued. -/
theorem arm_frame_reanchor_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {body : ValExpr} {tauV0 tauV1 : ValTy} :
    RawMDofTraceSubctx orc Gamma Psi (.vlam tauV0 tauV1 body)
      (.piTy tauV0 tauV1) :=
  rawMDof_pi_vacuous

theorem arm_frame_eta_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {body : ValExpr} {tauV0 tauV1 : ValTy} :
    RawMDofTraceSubctx orc Gamma Psi (.vlam tauV0 tauV1 body)
      (.piTy tauV0 tauV1) :=
  rawMDof_pi_vacuous

/-- Linear-lambda assembly records its tensor output while retaining the
actual empty-sum source annotation. -/
theorem arm_llam_assemble_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {sv0 sv1 : ValSpace} {es : List ValExpr} :
    RawMDofTraceSubctx orc Gamma Psi
      (ValExpr.sumAt sv0 es (.tprod sv0 sv1))
      (.space (.tprod sv0 sv1)) := by
  apply arm_reshape_dof

/-- Real-codomain assembly records its output with the actual sum source. -/
theorem arm_llam_assemble_real_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {sv : ValSpace} {es : List ValExpr} :
    RawMDofTraceSubctx orc Gamma Psi (ValExpr.sumAt sv es sv)
      (.space sv) := by
  apply arm_reshape_dof

theorem arm_zero_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {sv : ValSpace} :
    RawMDofTraceSubctx orc Gamma Psi (.zero sv) (.space sv) := by
  intro sv' hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

theorem arm_rlit_dof
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx} {r : ℝ} :
    RawMDofTraceSubctx orc Gamma Psi (.rlit r) (.space .real) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  rfl

/-- A raw base trace supplies the successful flat array and the exact target
length needed by the checked witness reshape. -/
theorem rawTermTrace_ok_array_length
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {e : ValExpr} {sourceSpace : Space} {sv : ValSpace}
    {B : BasisDenot} {source : DVal}
    (h : RawTermTraceAt orc sigma rho e (.space sourceSpace)
      (.space sv) B source) :
    exists a : FlatArray,
      denotValB_semS orc rho [] [] e = .ok (.array a) /\
      a.length = ValSpace.dof (orc rho [] []) sv := by
  obtain ⟨value, heval, hagree⟩ := h.result
  cases value with
  | fn T f => simpa only [RawAgree] using hagree
  | array a =>
      simp only [RawAgree, LegacyAgree] at hagree
      exact ⟨a, heval, hagree.2.1⟩

theorem ffsOperandRank_reshap_of_shpOf
    (orc : FFSOracleSem) (rho : ValEnvSem)
    {s1 s2 : ValSpace} (w : ValExpr)
    (hshape : ValSpace.shpOf (orc rho [] []) s1 =
      ValSpace.shpOf (orc rho [] []) s2)
    {a : FlatArray}
    (hw : denotValB_semS orc rho [] [] w = .ok (.array a))
    (hlen : a.length = ValSpace.dof (orc rho [] []) s2) :
    ffsOperandRank orc rho [] [] s1 w =
      ffsOperandRank orc rho [] [] s2 (ValExpr.reshapBase w s2) := by
  have hrsh : denotValB_semS orc rho [] []
      (ValExpr.reshapBase w s2) = .ok (.array a) := by
    simpa only [ValExpr.reshapBase] using
      denotValB_semS_reshap_space_ok orc rho [] [] w s2 a hw hlen
  unfold ffsOperandRank
  rw [hshape, hw, hrsh]

/-- The numerical oracle specification turns the preceding rank equality into
equality of FFS dimensions. -/
theorem oracle_dim_reshap_of_shpOf
    (orc : FFSOracleSem) (hspec : OracleSpec orc)
    (rho : ValEnvSem) (p : ValFFSProp) {s1 s2 : ValSpace}
    (w : ValExpr) (hf : ValueQueryDependencies.Finite (.expr [] w))
    (hs2 : ValueQueryDependencies.Finite (.space [] s2)) (hinfer : ValExpr.inferSpaceCtx [] w = s1)
    (hshape : ValSpace.shpOf (orc rho [] []) s1 =
      ValSpace.shpOf (orc rho [] []) s2)
    {a : FlatArray}
    (hw : denotValB_semS orc rho [] [] w = .ok (.array a))
    (hlen : a.length = ValSpace.dof (orc rho [] []) s2) :
    orc rho [] [] p s1 w =
      orc rho [] [] p s2 (ValExpr.reshapBase w s2) := by
  rw [hspec.rank rho p s1 w hinfer ((hinfer ▸ hf.inferSpace).ffs hf),
    hspec.rank rho p s2 (ValExpr.reshapBase w s2) rfl (hs2.ffs (hf.reshapBase hs2)),
    hshape,
    ffsOperandRank_reshap_of_shpOf orc rho w hshape hw hlen]

/-- Shape-only FFS bridge shared by all four embedding constructors. -/
theorem shpOf_ffs_embed
    (orc : FFSOracleSem) (hspec : OracleSpec orc)
    (rho : ValEnvSem) (p : ValFFSProp) {a b sv0 sv1 : ValSpace}
    (w : ValExpr) (hf : ValueQueryDependencies.Finite (.expr [] w))
    (hs : ValueQueryDependencies.Finite (.space [] (.tprod sv0 sv1)))
    (hw : ValExpr.inferSpaceCtx [] w = .tprod a b)
    (ih : ValSpace.shpOf (orc rho [] []) (.tprod a b) =
      ValSpace.shpOf (orc rho [] []) (.tprod sv0 sv1))
    {arr : FlatArray}
    (heval : denotValB_semS orc rho [] [] w = .ok (.array arr))
    (hlen : arr.length =
      ValSpace.dof (orc rho [] []) (.tprod sv0 sv1)) :
    ValSpace.shpOf (orc rho [] []) (.ffs p (.tprod a b) w) =
      ValSpace.shpOf (orc rho [] [])
        (.ffs p (.tprod sv0 sv1)
          (ValExpr.reshapBase w (.tprod sv0 sv1))) := by
  simp only [ValSpace.shpOf_ffs]
  rw [oracle_dim_reshap_of_shpOf orc hspec rho p w hf hs hw ih heval hlen]

/-! ## Four FFS-space witness consumers -/

/-- Common world-local payload consumed by each FFS embedding companion arm. -/
structure FFSWitnessInputs (orc : FFSOracleSem) (sigma : DEnv)
    (rho : ValEnvSem) (v : ValExpr) (sv0 sv1 : ValSpace) : Prop where
  dof : ValSpace.shpOf (orc rho [] []) (ValExpr.inferSpaceCtx [] v) =
    ValSpace.shpOf (orc rho [] []) (.tprod sv0 sv1)
  trace : exists (sourceSpace : Space) (B : BasisDenot) (source : DVal),
    RawTermTraceAt orc sigma rho v (.space sourceSpace)
      (.space (.tprod sv0 sv1)) B source
  finite : ValueQueryDependencies.Finite (.expr [] v)
  spaceFinite : ValueQueryDependencies.Finite (.space [] (.tprod sv0 sv1))

/-- At a fixed raw world, the paired term induction hypothesis supplies
exactly the common FFS witness payload.  The only extra input is the
constructor-local fact that the source basis is base-kind. -/
theorem RawTermDofFactsSubctx.ffsWitnessInputs
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {sv0 sv1 : ValSpace}
    (h : RawTermDofFactsSubctx orc ∅ Gamma Psi e b v
      (.space (.tprod sv0 sv1)))
    (he : S.Term ∅ Gamma Psi e b v (.space (.tprod sv0 sv1)))
    {sourceSpace : Space}
    (hbase : Basis.tof b = .space sourceSpace)
    {Psi' : EvalCtx} (hsub : Psi.Subctx Psi')
    (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
    (sigma : DEnv) (GammaV : ValCtx)
    (hle : NLCtxIncl Gamma Gamma')
    (hc : RawTypedConsistent orc Delta' Gamma' Psi' GammaV sigma rho) :
    FFSWitnessInputs orc sigma rho v sv0 sv1 := by
  refine ⟨h.dof rfl hsub rho Delta' Gamma' sigma GammaV hle hc,
    ⟨sourceSpace, denotBasis sigma b, denotTerm sigma e, ?_⟩,
    hc.exprFinite (he.mono hsub).toOpStep,
    (hc.typeFinite (he.mono hsub).toEvalT).space_inv⟩
  have hctx : RawCtxIncl ∅ Gamma Delta' Gamma' := by
    refine ⟨?_, hle⟩
    intro x s hx
    simp at hx
  simpa only [hbase] using
    h.trace hsub (Graded.CtxDisj.empty Gamma)
      rho Delta' Gamma' sigma GammaV hctx hc

/-- The shared FFS payload reduces the witness to an inferred tensor, proves
the checked reshape succeeds, and pins both tensor-factor dimensions. -/
theorem FFSWitnessInputs.elim
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {sigma : DEnv} {rho : ValEnvSem} {v : ValExpr}
    {sv0 sv1 : ValSpace}
    (h : FFSWitnessInputs orc sigma rho v sv0 sv1)
    (p : ValFFSProp) :
    exists a b,
      ValExpr.inferSpaceCtx [] v = .tprod a b /\
      ValSpace.shpOf (orc rho [] []) (.ffs p (.tprod a b) v) =
        ValSpace.shpOf (orc rho [] [])
          (.ffs p (.tprod sv0 sv1)
            (ValExpr.reshapBase v (.tprod sv0 sv1))) /\
      ValSpace.dof (orc rho [] []) a =
        ValSpace.dof (orc rho [] []) sv0 /\
      ValSpace.dof (orc rho [] []) b =
        ValSpace.dof (orc rho [] []) sv1 := by
  obtain ⟨a, b, hab⟩ := eq_tprod_of_shpOf_eq h.dof
  have hdof := h.dof
  rw [hab] at hdof
  obtain ⟨sourceSpace, B, source, htrace⟩ := h.trace
  obtain ⟨arr, heval, hlen⟩ := rawTermTrace_ok_array_length htrace
  have hffs := shpOf_ffs_embed orc hspec rho p v h.finite h.spaceFinite hab hdof heval hlen
  have hfactors := tprod_factor_dof_eq_of_shpOf_eq hdof
  exact ⟨a, b, hab, hffs, hfactors⟩

/-- Kernel embedding: the FFS factor and the domain tail are both pinned. -/
theorem ffs_consumer_kernel
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {sigma : DEnv} {rho : ValEnvSem} {v env0 env1 : ValExpr}
    {sv0 sv1 : ValSpace}
    (h : FFSWitnessInputs orc sigma rho v sv0 sv1) :
    ValSpace.shpOf (orc rho [] [])
        (ValExpr.inferSpaceCtx [] (.vtrans (.gsvdUI v env0 env1))) =
      ValSpace.shpOf (orc rho [] [])
        (.tprod
          (.ffs .kernel (.tprod sv0 sv1)
            (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) := by
  obtain ⟨a, b, hab, hffs, ha, hb⟩ := h.elim hspec .kernel
  have hinfer : ValExpr.inferSpaceCtx []
      (.vtrans (.gsvdUI v env0 env1)) =
      .tprod (.ffs .kernel (.tprod a b) v) a := by
    rw [ValExpr.inferSpaceCtx, ValExpr.inferSpaceCtx, hab]
  rw [hinfer]
  simp only [ValSpace.shpOf_tprod]
  rw [dof_eq_of_shpOf_eq hffs, ha]

/-- Cokernel embedding: the FFS factor and the domain tail are both pinned. -/
theorem ffs_consumer_cokernel
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {sigma : DEnv} {rho : ValEnvSem} {v env0 env1 : ValExpr}
    {sv0 sv1 : ValSpace}
    (h : FFSWitnessInputs orc sigma rho v sv0 sv1) :
    ValSpace.shpOf (orc rho [] [])
        (ValExpr.inferSpaceCtx [] (.vtrans (.gsvdU v env0 env1))) =
      ValSpace.shpOf (orc rho [] [])
        (.tprod
          (.ffs .cokernel (.tprod sv0 sv1)
            (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) := by
  obtain ⟨a, b, hab, hffs, ha, hb⟩ := h.elim hspec .cokernel
  have hinfer : ValExpr.inferSpaceCtx []
      (.vtrans (.gsvdU v env0 env1)) =
      .tprod (.ffs .cokernel (.tprod a b) v) a := by
    rw [ValExpr.inferSpaceCtx, ValExpr.inferSpaceCtx, hab]
  rw [hinfer]
  simp only [ValSpace.shpOf_tprod]
  rw [dof_eq_of_shpOf_eq hffs, ha]

/-- Image embedding: the FFS factor and the codomain tail are both pinned. -/
theorem ffs_consumer_image
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {sigma : DEnv} {rho : ValEnvSem} {v env0 env1 : ValExpr}
    {sv0 sv1 : ValSpace}
    (h : FFSWitnessInputs orc sigma rho v sv0 sv1) :
    ValSpace.shpOf (orc rho [] [])
        (ValExpr.inferSpaceCtx [] (.vtrans (.gsvdV v env0 env1))) =
      ValSpace.shpOf (orc rho [] [])
        (.tprod
          (.ffs .image (.tprod sv0 sv1)
            (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) := by
  obtain ⟨a, b, hab, hffs, ha, hb⟩ := h.elim hspec .image
  have hinfer : ValExpr.inferSpaceCtx []
      (.vtrans (.gsvdV v env0 env1)) =
      .tprod (.ffs .image (.tprod a b) v) b := by
    rw [ValExpr.inferSpaceCtx, ValExpr.inferSpaceCtx, hab]
  rw [hinfer]
  simp only [ValSpace.shpOf_tprod]
  rw [dof_eq_of_shpOf_eq hffs, hb]

/-- Coimage embedding: the FFS factor and the codomain tail are both pinned. -/
theorem ffs_consumer_coimage
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {sigma : DEnv} {rho : ValEnvSem} {v env0 env1 : ValExpr}
    {sv0 sv1 : ValSpace}
    (h : FFSWitnessInputs orc sigma rho v sv0 sv1) :
    ValSpace.shpOf (orc rho [] [])
        (ValExpr.inferSpaceCtx [] (.vtrans (.gsvdVI v env0 env1))) =
      ValSpace.shpOf (orc rho [] [])
        (.tprod
          (.ffs .coimage (.tprod sv0 sv1)
            (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) := by
  obtain ⟨a, b, hab, hffs, ha, hb⟩ := h.elim hspec .coimage
  have hinfer : ValExpr.inferSpaceCtx []
      (.vtrans (.gsvdVI v env0 env1)) =
      .tprod (.ffs .coimage (.tprod a b) v) b := by
    rw [ValExpr.inferSpaceCtx, ValExpr.inferSpaceCtx, hab]
  rw [hinfer]
  simp only [ValSpace.shpOf_tprod]
  rw [dof_eq_of_shpOf_eq hffs, hb]

/-! The following four wrappers put the world-local calculations back into
the exact direct-mutual motive.  Thus they also serve as executable audits of
which child fields each constructor consumes: a single paired witness IH, and
nothing from either environment-term IH. -/

theorem arm_embed_kernel_dof
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {b0 b1 : Basis}
    {v env0 env1 : ValExpr} {sv0 sv1 : ValSpace}
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1)))
    (ih : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    RawMDofTraceSubctx orc Gamma Psi
      (.vtrans (.gsvdUI v env0 env1))
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  exact ffs_consumer_kernel hspec
    (ih.ffsWitnessInputs he rfl hsub rho Delta' Gamma' sigma GammaV hle hc)

theorem arm_embed_cokernel_dof
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {b0 b1 : Basis}
    {v env0 env1 : ValExpr} {sv0 sv1 : ValSpace}
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1)))
    (ih : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    RawMDofTraceSubctx orc Gamma Psi
      (.vtrans (.gsvdU v env0 env1))
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  exact ffs_consumer_cokernel hspec
    (ih.ffsWitnessInputs he rfl hsub rho Delta' Gamma' sigma GammaV hle hc)

theorem arm_embed_image_dof
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {b0 b1 : Basis}
    {v env0 env1 : ValExpr} {sv0 sv1 : ValSpace}
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1)))
    (ih : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    RawMDofTraceSubctx orc Gamma Psi
      (.vtrans (.gsvdV v env0 env1))
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  exact ffs_consumer_image hspec
    (ih.ffsWitnessInputs he rfl hsub rho Delta' Gamma' sigma GammaV hle hc)

theorem arm_embed_coimage_dof
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {b0 b1 : Basis}
    {v env0 env1 : ValExpr} {sv0 sv1 : ValSpace}
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1)))
    (ih : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    RawMDofTraceSubctx orc Gamma Psi
      (.vtrans (.gsvdVI v env0 env1))
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) := by
  intro sv hspace Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  cases hspace
  exact ffs_consumer_coimage hspec
    (ih.ffsWitnessInputs he rfl hsub rho Delta' Gamma' sigma GammaV hle hc)

end GLang
