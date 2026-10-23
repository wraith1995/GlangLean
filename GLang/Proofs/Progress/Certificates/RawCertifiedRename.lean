import GLang.Proofs.Progress.CheckedErasure
import GLang.Proofs.Progress.Supporting.ProgressRename
import GLang.Proofs.Progress.Supporting.ProgressMasterDefs
import GLang.Proofs.Preservation.ValuePreservationV2

namespace GLang
namespace RawCertifiedOperational

/-- The checked counterpart of the existing `ESubst.rename` and
`ESubst.delta` transports.  An implementation is expected to be a single
five-way mutual recursion over `C.Space`/`C.Ty`/`C.TyAt`/`C.Cob`/`C.Term`,
using the source WF premise to cross `promote` soundly.

The nonlinear fields are stated at an arbitrary valid domain basis.  Checked
standard progress specializes them to `Basis.std tau0`; higher-order basis
transport uses the same fields at the target frame's domain basis. -/
structure CheckedRenameLaws : Prop where
  tyAt_nl :
    ∀ {Gamma : NLCtx} {Psi : EvalCtx} {x y : VName}
      {tau0 : Ty} {tauV0 tauV : ValTy} {b0 b : Basis},
      V2.CtxWF' ∅ Gamma ->
      (∃ k, Nonempty (TValid Gamma tau0 k)) ->
      Basis.tof b0 = tau0 -> Basis.BasisValid Gamma b0 ->
      x ∉ Gamma -> y ∉ Gamma -> x ≠ y ->
      ESubst x b0 tauV0 (.var y) (.var y tauV0)
        (Psi.extend x b0 (.var x tauV0))
        (Psi.extend y b0 (.var y tauV0)) ->
      C.TyAt (Finmap.insert x tau0 Gamma)
          (Psi.extend x b0 (.var x tauV0)) b tauV ->
      C.TyAt (Finmap.insert y tau0 Gamma)
          (Psi.extend y b0 (.var y tauV0))
          (Basis.subst x (.var y) b)
          (ValTy.subst x (.var y tauV0) tauV)

  term_nl :
    ∀ {Gamma : NLCtx} {Psi : EvalCtx} {x y : VName}
      {tau0 : Ty} {tauV0 tauV : ValTy} {e : Term}
      {b0 b : Basis} {v : ValExpr},
      V2.CtxWF' ∅ Gamma ->
      (∃ k, Nonempty (TValid Gamma tau0 k)) ->
      Basis.tof b0 = tau0 -> Basis.BasisValid Gamma b0 ->
      x ∉ Gamma -> y ∉ Gamma -> x ≠ y ->
      ESubst x b0 tauV0 (.var y) (.var y tauV0)
        (Psi.extend x b0 (.var x tauV0))
        (Psi.extend y b0 (.var y tauV0)) ->
      C.Term ∅ (Finmap.insert x tau0 Gamma)
          (Psi.extend x b0 (.var x tauV0)) e b v tauV ->
      C.Term ∅ (Finmap.insert y tau0 Gamma)
          (Psi.extend y b0 (.var y tauV0))
          (Term.subst x (.var y) e)
          (Basis.subst x (.var y) b)
          (ValExpr.subst x (.var y tauV0) v)
          (ValTy.subst x (.var y tauV0) tauV)

  term_delta :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {x y : VName}
      {s : Space} {sv : ValSpace} {i : Nat}
      {tauV : ValTy} {e : Term} {b bout : Basis} {v : ValExpr},
      V2.CtxWF' Delta Gamma ->
      Nonempty (SValid Gamma s) ->
      x ∉ Delta -> y ∉ Delta -> x ∉ Gamma -> y ∉ Gamma -> x ≠ y ->
      b = Basis.stdSpace s ->
      ESubst x b (.space sv) (.var y) (.delta i sv)
        (Psi.extend x b (.var x (.space sv)))
        (Psi.extend y b (.delta i sv)) ->
      C.Term (Finmap.insert x s Delta) Gamma
          (Psi.extend x b (.var x (.space sv))) e bout v tauV ->
      C.Term (Finmap.insert y s Delta) Gamma
          (Psi.extend y b (.delta i sv))
          (Term.subst x (.var y) e)
          (Basis.subst x (.var y) bout)
          (ValExpr.subst x (.delta i sv) v)
          (ValTy.subst x (.delta i sv) tauV)

/-! ## Nonlinear checked cofinite packaging -/

/-- Package one checked realization of a standard-basis opened codomain into
the exact fixed family consumed by `C.TyAt.frame`.

The fixed codomain is `closeRec 0 x tauV`; at another fresh `y`, the value
side is definitionally restored with `ValTy.openVar_closeRec_of_lc`. -/
theorem checkedTyAt_cofinite_of_fresh
    (laws : CheckedRenameLaws)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName}
    {tau0 tau1 : Ty} {tauV0 tauV : ValTy}
    (hwf : V2.CtxWF' ∅ Gamma)
    (htau0 : ∃ k, Nonempty (TValid Gamma tau0 k))
    (hxGamma : x ∉ Gamma)
    (h : C.TyAt (Finmap.insert x tau0 Gamma)
      (Psi.extend x (Basis.std tau0) (.var x tauV0))
      (Basis.std (Ty.openVar x tau1)) tauV)
    (hxPsi : x ∉ EvalCtx.avoidB Psi)
    (hxb : x ∉ Basis.fv (Basis.std tau0))
    (hxtauV0 : x ∉ ValTy.fv tauV0)
    (hxtau1 : x ∉ Ty.fv tau1)
    (hlctauV0 : ValTy.lc tauV0)
    (hlctauV : ValTy.lc tauV) :
    ∃ L : Finset VName, ∀ y, y ∉ L ->
      C.TyAt (Finmap.insert y tau0 Gamma)
        (Psi.extend y (Basis.std tau0) (.var y tauV0))
        (Basis.std (Ty.openVar y tau1))
        (ValTy.openVar y tauV0 (ValTy.closeRec 0 x tauV)) := by
  refine ⟨EvalCtx.avoidB Psi ∪ Gamma.keys ∪ {x}, ?_⟩
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨hyPsi, hyGammaKeys⟩, hyx⟩ := hy
  have hyGamma : y ∉ Gamma := by
    intro hm
    exact hyGammaKeys (Finmap.mem_keys.mpr hm)
  have hes := ESubst.rename hxPsi hyPsi hxb hxtauV0 hlctauV0
  have hr := laws.tyAt_nl hwf htau0 (Basis.tof_std tau0)
    (Basis.std_valid tau0 (Classical.choice (Classical.choose_spec htau0)))
    hxGamma hyGamma (Ne.symm hyx) hes h
  have hsrc : Basis.subst x (.var y) (Basis.std (Ty.openVar x tau1)) =
      Basis.std (Ty.openVar y tau1) := by
    rw [<- Basis.std_subst]
    exact congrArg Basis.std
      ((Ty.subst_intro x (.var y) tau1 hxtau1 0).symm)
  rw [hsrc] at hr
  rw [ValTy.openVar_closeRec_of_lc x y tauV0 hlctauV]
  exact hr

/-- Package one checked opened term run into the fixed locally-nameless family
used by `C.Term.nllam`.  Both its value and its realized result type are closed
once at `x` and re-opened coherently at every fresh name. -/
theorem checkedTerm_nllam_cofinite_of_fresh
    (laws : CheckedRenameLaws)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName}
    {tau0 tau1 : Ty} {tauV0 tauV : ValTy}
    {e : Term} {v : ValExpr}
    (hwf : V2.CtxWF' ∅ Gamma)
    (htau0 : ∃ k, Nonempty (TValid Gamma tau0 k))
    (hxGamma : x ∉ Gamma)
    (h : C.Term ∅ (Finmap.insert x tau0 Gamma)
      (Psi.extend x (Basis.std tau0) (.var x tauV0))
      (Term.openVar x e) (Basis.std (Ty.openVar x tau1)) v tauV)
    (hxPsi : x ∉ EvalCtx.avoidB Psi)
    (hxb : x ∉ Basis.fv (Basis.std tau0))
    (hxtauV0 : x ∉ ValTy.fv tauV0)
    (hxe : x ∉ Term.fv e)
    (hxtau1 : x ∉ Ty.fv tau1)
    (hlctauV0 : ValTy.lc tauV0)
    (hlcv : ValExpr.lc v)
    (hlctauV : ValTy.lc tauV) :
    ∃ L : Finset VName, ∀ y, y ∉ L ->
      C.Term ∅ (Finmap.insert y tau0 Gamma)
        (Psi.extend y (Basis.std tau0) (.var y tauV0))
        (Term.openVar y e) (Basis.std (Ty.openVar y tau1))
        (ValExpr.openVar y tauV0 (ValExpr.closeRec 0 x v))
        (ValTy.openVar y tauV0 (ValTy.closeRec 0 x tauV)) := by
  refine ⟨EvalCtx.avoidB Psi ∪ Gamma.keys ∪ {x}, ?_⟩
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨hyPsi, hyGammaKeys⟩, hyx⟩ := hy
  have hyGamma : y ∉ Gamma := by
    intro hm
    exact hyGammaKeys (Finmap.mem_keys.mpr hm)
  have hes := ESubst.rename hxPsi hyPsi hxb hxtauV0 hlctauV0
  have hr := laws.term_nl hwf htau0 (Basis.tof_std tau0)
    (Basis.std_valid tau0 (Classical.choice (Classical.choose_spec htau0)))
    hxGamma hyGamma (Ne.symm hyx) hes h
  have hsrcT : Term.subst x (.var y) (Term.openVar x e) =
      Term.openVar y e := (Term.subst_intro x (.var y) e hxe 0).symm
  have hsrcB : Basis.subst x (.var y) (Basis.std (Ty.openVar x tau1)) =
      Basis.std (Ty.openVar y tau1) := by
    rw [<- Basis.std_subst]
    exact congrArg Basis.std
      ((Ty.subst_intro x (.var y) tau1 hxtau1 0).symm)
  rw [hsrcT, hsrcB] at hr
  rw [ValExpr.openVar_closeRec_of_lc x y tauV0 hlcv,
    ValTy.openVar_closeRec_of_lc x y tauV0 hlctauV]
  exact hr

/-- `frame_eta` specialization. -/
theorem checkedTerm_frameEta_cofinite_of_fresh
    (laws : CheckedRenameLaws)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName}
    {tau0 tau1 : Ty} {tauV0 tauV : ValTy}
    {n0 : Term} {v : ValExpr}
    (hwf : V2.CtxWF' ∅ Gamma)
    (htau0 : ∃ k, Nonempty (TValid Gamma tau0 k))
    (hxGamma : x ∉ Gamma)
    (h : C.Term ∅ (Finmap.insert x tau0 Gamma)
      (Psi.extend x (Basis.std tau0) (.var x tauV0))
      (.appN n0 (.var x)) (Basis.std (Ty.openVar x tau1)) v tauV)
    (hxPsi : x ∉ EvalCtx.avoidB Psi)
    (hxb : x ∉ Basis.fv (Basis.std tau0))
    (hxtauV0 : x ∉ ValTy.fv tauV0)
    (hxn0 : x ∉ Term.fv n0)
    (hxtau1 : x ∉ Ty.fv tau1)
    (hlctauV0 : ValTy.lc tauV0)
    (hlcv : ValExpr.lc v)
    (hlctauV : ValTy.lc tauV) :
    ∃ L : Finset VName, ∀ y, y ∉ L ->
      C.Term ∅ (Finmap.insert y tau0 Gamma)
        (Psi.extend y (Basis.std tau0) (.var y tauV0))
        (.appN n0 (.var y)) (Basis.std (Ty.openVar y tau1))
        (ValExpr.openVar y tauV0 (ValExpr.closeRec 0 x v))
        (ValTy.openVar y tauV0 (ValTy.closeRec 0 x tauV)) := by
  refine ⟨EvalCtx.avoidB Psi ∪ Gamma.keys ∪ {x}, ?_⟩
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨hyPsi, hyGammaKeys⟩, hyx⟩ := hy
  have hyGamma : y ∉ Gamma := by
    intro hm
    exact hyGammaKeys (Finmap.mem_keys.mpr hm)
  have hes := ESubst.rename hxPsi hyPsi hxb hxtauV0 hlctauV0
  have hr := laws.term_nl hwf htau0 (Basis.tof_std tau0)
    (Basis.std_valid tau0 (Classical.choice (Classical.choose_spec htau0)))
    hxGamma hyGamma (Ne.symm hyx) hes h
  have hsrcT : Term.subst x (.var y) (.appN n0 (.var x)) =
      .appN n0 (.var y) := by
    simp [Term.subst, Term.subst_fresh x (.var y) n0 hxn0]
  have hsrcB : Basis.subst x (.var y) (Basis.std (Ty.openVar x tau1)) =
      Basis.std (Ty.openVar y tau1) := by
    rw [<- Basis.std_subst]
    exact congrArg Basis.std
      ((Ty.subst_intro x (.var y) tau1 hxtau1 0).symm)
  rw [hsrcT, hsrcB] at hr
  rw [ValExpr.openVar_closeRec_of_lc x y tauV0 hlcv,
    ValTy.openVar_closeRec_of_lc x y tauV0 hlctauV]
  exact hr

/-! ## Linear checked cofinite packaging -/

/-- Turn one checked symbolic linear-body run into every concrete coordinate
column required by `C.Term.llam_assemble` and
`C.Term.llam_assemble_real`.  The result for coordinate `i` is fixed as
`ValExpr.subst x (.delta i sv) v`, hence it is independent of the fresh name
chosen to open the source binder. -/
theorem checkedTerm_llam_cofinite_of_placeholder
    (laws : CheckedRenameLaws)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {x : VName}
    {s : Space} {sv : ValSpace} {tauV : ValTy}
    {e : Term} {bout : Basis} {v : ValExpr}
    (hwf : V2.CtxWF' Delta Gamma)
    (hs : Nonempty (SValid Gamma s))
    (hxDelta : x ∉ Delta) (hxGamma : x ∉ Gamma)
    (h : C.Term (Finmap.insert x s Delta) Gamma
      (Psi.extend x (Basis.stdSpace s) (.var x (.space sv)))
      (Term.openVar x e) bout v tauV)
    (hxPsi : x ∉ EvalCtx.avoidB Psi)
    (hxBasis : x ∉ Basis.fv (Basis.stdSpace s))
    (hxsv : x ∉ ValSpace.fv sv)
    (hxe : x ∉ Term.fv e)
    (hxbout : x ∉ Basis.fv bout)
    (hxtauV : x ∉ ValTy.fv tauV)
    (hlcsv : ValSpace.lc sv) :
    ∃ L : Finset VName, ∀ y, y ∉ L -> ∀ i : Nat,
      C.Term (Finmap.insert y s Delta) Gamma
        (Psi.extend y (Basis.stdSpace s) (.delta i sv))
        (Term.openVar y e) bout
        (ValExpr.subst x (.delta i sv) v) tauV := by
  refine ⟨EvalCtx.avoidB Psi ∪ Delta.keys ∪ Gamma.keys ∪ {x}, ?_⟩
  intro y hy i
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨⟨hyPsi, hyDeltaKeys⟩, hyGammaKeys⟩, hyx⟩ := hy
  have hyDelta : y ∉ Delta := by
    intro hm
    exact hyDeltaKeys (Finmap.mem_keys.mpr hm)
  have hyGamma : y ∉ Gamma := by
    intro hm
    exact hyGammaKeys (Finmap.mem_keys.mpr hm)
  have hes := ESubst.delta (i := i) hxPsi hyPsi hxBasis hxsv hlcsv
  have hr := laws.term_delta hwf hs hxDelta hyDelta hxGamma hyGamma
    (Ne.symm hyx) rfl hes h
  have hsrcT : Term.subst x (.var y) (Term.openVar x e) =
      Term.openVar y e := (Term.subst_intro x (.var y) e hxe 0).symm
  rw [hsrcT, Basis.subst_fresh x (.var y) bout hxbout,
    ValTy.subst_fresh x (.delta i sv) tauV hxtauV] at hr
  exact hr

/-! ## Closed leaf sanity checks -/

/-- Renaming for closed real and empty type leaves. -/
theorem tyAt_one_any {Gamma : NLCtx} {Psi : EvalCtx} :
    C.TyAt Gamma Psi .one (.space .real) :=
  .space rfl .one .real

theorem tyAt_empty_any {Gamma : NLCtx} {Psi : EvalCtx} :
    C.TyAt Gamma Psi .empty (.space .empty) :=
  .space rfl .empty .empty

end RawCertifiedOperational
end GLang
