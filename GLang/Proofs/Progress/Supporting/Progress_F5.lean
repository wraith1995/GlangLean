

import GLang.Proofs.Progress.Supporting.ProgressMasterDefs

namespace GLang.V2

/-- Private F5 helper (FLAGGED — sibling families need the same conversion;
    candidate for promotion into `ProgressMasterDefs`): forward-only covering
    restricts to the empty linear context — the `Δ`-clause is vacuous at `∅`
    (`Finmap.lookup_empty`), the `Γ`-clause is untouched. Feeds the
    `pMotiveS` IHs (which live at `Δ = ∅`) from a term-level covering. -/
private theorem VarsCovered.drop_lin {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    (h : VarsCovered Δ Γ Ψ) : VarsCovered ∅ Γ Ψ :=
  ⟨fun _ _ hx => by simp [Finmap.lookup_empty] at hx, h.2⟩

/-- refine_21 `HasType.app_linear` (catalog F5): `OpStep.appL_lin` at
    `b₀ := stdSpace s₀`, `b₁ := stdSpace s₁`. IH₀'s basis
    `std (.space (.tprod (.dual s₀) s₁))` is defeq the rule's
    `.tprod (.dual b₀) b₁` (C2); `hsv` transports the space IH along
    `sof_stdSpace`; the rule's `.appL (sof b₀) (sof b₁) …` annotation is
    re-aligned by `sof_stdSpace`. Δ-split: `VarsCovered.mono_lin`.
    Tail: (V) — space-typed. -/
theorem progress_arm_app_linear {Δ₀ Δ₁ : LCtx} {ε : NLCtx} {e₀ e₁ : Term}
    {s₀ s₁ : Space}
    (_hsval₀ : SValid ε s₀) (_hsval₁ : SValid ε s₁)
    (hdisj : Δ₀.Disjoint Δ₁)
    (_ht₀ : HasType Δ₀ ε e₀ (Ty.space (s₀.dual.tprod s₁)))
    (_ht₁ : HasType Δ₁ ε e₁ (Ty.space s₀))
    (ihs₀ : pMotiveS ε s₀) (ihs₁ : pMotiveS ε s₁)
    (ih₀ : pMotiveH Δ₀ ε e₀ (Ty.space (s₀.dual.tprod s₁)))
    (ih₁ : pMotiveH Δ₁ ε e₁ (Ty.space s₀)) :
    pMotiveH (Δ₀ ∪ Δ₁) ε (Term.appL s₀ s₁ e₀ e₁) (Ty.space s₁) := by
  intro Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨hcov₀, hcov₁⟩ := hcov.mono_lin hdisj
  obtain ⟨v₀, hv₀⟩ := (ih₀ Ψ hP hcov₀).1
  obtain ⟨v₁, hv₁⟩ := (ih₁ Ψ hP hcov₁).1
  obtain ⟨sv₀, hsv₀⟩ := ihs₀ Ψ hP hcov₀.drop_lin
  obtain ⟨sv₁, hsv₁⟩ := ihs₁ Ψ hP hcov₁.drop_lin
  have hsv₀' : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s₀)) sv₀ := by
    rw [Basis.sof_stdSpace]; exact hsv₀
  have hsv₁' : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s₁)) sv₁ := by
    rw [Basis.sof_stdSpace]; exact hsv₁
  have hstep := ValExpr.OpStep.appL_lin
    (b₀ := Basis.stdSpace s₀) (b₁ := Basis.stdSpace s₁)
    hv₀ hsv₀' hv₁ hsv₁' (by simp only [Basis.tof_stdSpace, Basis.sof_stdSpace])
  simp only [Basis.sof_stdSpace] at hstep
  exact ⟨_, hstep⟩

/-- refine_22 `HasType.app_inner` (catalog F5): `OpStep.appI_lin` at
    `b₀ := stdSpace s` (IH₀'s basis defeq `.dual b₀`, C2); the conclusion
    lands at `.one`, defeq `std (.space .real)` (C1/C9); annotation
    re-aligned by `sof_stdSpace`. Tail: (V). -/
theorem progress_arm_app_inner {Δ₀ Δ₁ : LCtx} {ε : NLCtx} {e₀ e₁ : Term}
    {s : Space}
    (_hsval : SValid ε s)
    (hdisj : Δ₀.Disjoint Δ₁)
    (_ht₀ : HasType Δ₀ ε e₀ (Ty.space s.dual))
    (_ht₁ : HasType Δ₁ ε e₁ (Ty.space s))
    (ihs : pMotiveS ε s)
    (ih₀ : pMotiveH Δ₀ ε e₀ (Ty.space s.dual))
    (ih₁ : pMotiveH Δ₁ ε e₁ (Ty.space s)) :
    pMotiveH (Δ₀ ∪ Δ₁) ε (Term.appI s e₀ e₁) (Ty.space Space.real) := by
  intro Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨hcov₀, hcov₁⟩ := hcov.mono_lin hdisj
  obtain ⟨v₀, hv₀⟩ := (ih₀ Ψ hP hcov₀).1
  obtain ⟨v₁, hv₁⟩ := (ih₁ Ψ hP hcov₁).1
  obtain ⟨sv, hsv⟩ := ihs Ψ hP hcov₀.drop_lin
  have hsv' : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s)) sv := by
    rw [Basis.sof_stdSpace]; exact hsv
  have hstep := ValExpr.OpStep.appI_lin (b₀ := Basis.stdSpace s) hv₀ hsv' hv₁
  simp only [Basis.sof_stdSpace] at hstep
  exact ⟨_, hstep⟩

/-- refine_26 `HasType.pinv_tensor` (catalog F5): `OpStep.pinvT_std` with the
    catalog-verified SWAPPED instantiation `b₀ := stdSpace s₁`,
    `b₁ := stdSpace s₀` — the rule's premise then sits at
    `.tprod (.dual (stdSpace s₀)) (stdSpace s₁)` (defeq the IH's basis, C2)
    and its conclusion at `.tprod (.dual (stdSpace s₁)) (stdSpace s₀)` (defeq
    the goal's, C2); `isStd` premises by `Basis.isStd_stdSpace`; the
    `.pinvT (sof b₁) (sof b₀) e` annotation re-aligns by `sof_stdSpace`.
    Tail: (V). -/
theorem progress_arm_pinv_tensor {ε : NLCtx} {e : Term} {s₀ s₁ : Space}
    (_hsval₀ : SValid ε s₀) (_hsval₁ : SValid ε s₁)
    (_ht : HasType ∅ ε e (Ty.space (s₀.dual.tprod s₁)))
    (_ihs₀ : pMotiveS ε s₀) (_ihs₁ : pMotiveS ε s₁)
    (ih : pMotiveH ∅ ε e (Ty.space (s₀.dual.tprod s₁))) :
    pMotiveH ∅ ε (Term.pinvT s₀ s₁ e) (Ty.space (s₁.dual.tprod s₀)) := by
  intro Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨v, hv⟩ := (ih Ψ hP hcov).1
  have hstep := ValExpr.OpStep.pinvT_std
    (b₀ := Basis.stdSpace s₁) (b₁ := Basis.stdSpace s₀) hv
    (Basis.isStd_stdSpace s₁) (Basis.isStd_stdSpace s₀)
  simp only [Basis.sof_stdSpace] at hstep
  exact ⟨_, hstep⟩

/-- refine_27 `HasType.pinv_dual` (catalog F5): `OpStep.pinvD_std` at
    `b₀ := .one` (`hsofb₀ : sof .one = .real` is `rfl`; `isStd .one`
    trivial), `b₁ := stdSpace s` (premise at `.dual b₁`, defeq the IH's
    basis, C2). Goal basis `std (.space (.tprod (.dual .real) s))` is defeq
    `.tprod (.dual .one) (stdSpace s)` (`stdSpace .real = .one`); the
    `.pinvD (sof b₁) e` annotation re-aligns by `sof_stdSpace`. Tail: (V). -/
theorem progress_arm_pinv_dual {ε : NLCtx} {e : Term} {s : Space}
    (_hsval : SValid ε s)
    (_ht : HasType ∅ ε e (Ty.space s.dual))
    (ihs : pMotiveS ε s)
    (ih : pMotiveH ∅ ε e (Ty.space s.dual)) :
    pMotiveH ∅ ε (Term.pinvD s e) (Ty.space (Space.real.dual.tprod s)) := by
  intro Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨v, hv⟩ := (ih Ψ hP hcov).1
  -- E4/E7 premise `hsv₁ : EvalS (sof b₁) sv₁` from the space IH.
  obtain ⟨sv, hsv⟩ := ihs Ψ hP hcov.drop_lin
  have hsv' : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s)) sv := by
    rw [Basis.sof_stdSpace]; exact hsv
  have hstep := ValExpr.OpStep.pinvD_std
    (b₀ := .one) (b₁ := Basis.stdSpace s) hv rfl trivial
    (Basis.isStd_stdSpace s) hsv'
  simp only [Basis.sof_stdSpace] at hstep
  exact ⟨_, hstep⟩

/-- refine_31 `HasType.llam_real` (catalog F5): dimension-complete linear
    functional assembly.  Evaluate the body once with a fresh symbolic
    linear variable, then substitute each concrete `.delta i sv'` into that
    derivation. This produces the ordinary rule's exact fixed
    `Fin (dofUB sv')` family. -/
theorem progress_arm_llam_real {Δ : LCtx} {ε : NLCtx} {s : Space} {e : Term}
    (L : Finset Name) (_hsval : SValid ε s)
    (_hbody : (y : Name) → y ∉ L →
      HasType (Finmap.insert y s Δ) ε (Term.openVar y e) (Ty.space Space.real))
    (ihs : pMotiveS ε s)
    (ihbody : ∀ y ∉ L,
      pMotiveH (Finmap.insert y s Δ) ε (Term.openVar y e) (Ty.space Space.real)) :
    pMotiveH Δ ε (Term.llam s Space.real e) (Ty.space s.dual) := by
  intro Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨sv', hsv'⟩ := ihs Ψ hP hcov.drop_lin
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Ψ ∪ L ∪ Term.fv e ∪ Basis.fv (Basis.stdSpace s)
      ∪ ValSpace.fv sv')
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨hxΨ, hxL⟩, hxe⟩, hxb⟩, hxsv⟩ := hx
  have hτv : ValTy.EvalT Ψ (.space s) (.space sv') := .space hsv'
  have hfresh : (x, Basis.stdSpace s) ∉ Ψ :=
    (EvalCtx.avoidB_spec hxΨ).1 _
  have hP' : PCarrier
      (Ψ.extend x (Basis.stdSpace s) (.var x (.space sv'))) :=
    hP.extend_var hfresh (evalT_fv hτv hP.1) hτv
      (fun _ _ h => nomatch h)
  have hcov' : VarsCovered (Finmap.insert x s Δ) ε
      (Ψ.extend x (Basis.stdSpace s) (.var x (.space sv'))) :=
    hcov.extend_var_lin
  obtain ⟨v, hv⟩ :=
    ((ihbody x hxL) _ hP' hcov').1
  have hv' : ValExpr.OpStep
      (Ψ.extend x (Basis.stdSpace s) (.var x (.space sv')))
      (Term.openVar x e) .one v := by
    exact hv
  have hlcsv' : ValSpace.lc sv' :=
    realize_lc_joint.1 hsv' hP.1.toEvalCtxLc
  let env : Fin (ValSpace.dofUB sv') → ValExpr := fun i =>
    ValExpr.subst x (.delta i.val sv') v
  have hstep := ValExpr.OpStep.llam_assemble_real
    (b' := Basis.stdSpace s) (e := e) (env := env)
    (Basis.htof_stdSpace s)
    (by simpa only [Basis.sof_stdSpace] using hsv')
    (EvalCtx.avoidB Ψ)
    (fun y hy i => by
      simpa only [env] using hv'.delta_of_placeholder hxΨ hy hxb hxsv hxe
        (by simp [Basis.fv]) hlcsv')
  simp only [Basis.sof_stdSpace] at hstep
  exact ⟨_, hstep⟩

/-- refine_32 `HasType.llam_tensor` (catalog F5): the tensor-codomain version
    of `progress_arm_llam_real`.  One symbolic body run is specialized to
    every coordinate in `Fin (dofUB sv')`. -/
theorem progress_arm_llam_tensor {Δ : LCtx} {ε : NLCtx} {s₀ s : Space}
    {e : Term} (L : Finset Name)
    (_hne : s ≠ Space.real)
    (_hsval₀ : SValid ε s₀) (_hsval : SValid ε s)
    (_hbody : (y : Name) → y ∉ L →
      HasType (Finmap.insert y s₀ Δ) ε (Term.openVar y e) (Ty.space s))
    (ihs₀ : pMotiveS ε s₀) (ihs : pMotiveS ε s)
    (ihbody : ∀ y ∉ L,
      pMotiveH (Finmap.insert y s₀ Δ) ε (Term.openVar y e) (Ty.space s)) :
    pMotiveH Δ ε (Term.llam s₀ s e) (Ty.space (s₀.dual.tprod s)) := by
  intro Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨sv', hsv'⟩ := ihs₀ Ψ hP hcov.drop_lin
  obtain ⟨sv, hsvv⟩ := ihs Ψ hP hcov.drop_lin
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Ψ ∪ L ∪ Term.fv e ∪ Basis.fv (Basis.stdSpace s₀)
      ∪ Basis.fv (Basis.stdSpace s) ∪ ValSpace.fv sv')
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨hxΨ, hxL⟩, hxe⟩, hxb₀⟩, hxbs⟩, hxsv⟩ := hx
  have hτv : ValTy.EvalT Ψ (.space s₀) (.space sv') := .space hsv'
  have hfresh : (x, Basis.stdSpace s₀) ∉ Ψ :=
    (EvalCtx.avoidB_spec hxΨ).1 _
  have hP' : PCarrier
      (Ψ.extend x (Basis.stdSpace s₀) (.var x (.space sv'))) :=
    hP.extend_var hfresh (evalT_fv hτv hP.1) hτv
      (fun _ _ h => nomatch h)
  have hcov' : VarsCovered (Finmap.insert x s₀ Δ) ε
      (Ψ.extend x (Basis.stdSpace s₀) (.var x (.space sv'))) :=
    hcov.extend_var_lin
  obtain ⟨v, hv⟩ := ((ihbody x hxL) _ hP' hcov').1
  have hv' : ValExpr.OpStep
      (Ψ.extend x (Basis.stdSpace s₀) (.var x (.space sv')))
      (Term.openVar x e) (Basis.stdSpace s) v := hv
  have hlcsv' : ValSpace.lc sv' :=
    realize_lc_joint.1 hsv' hP.1.toEvalCtxLc
  have h₁ : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s₀)) sv' := by
    rw [Basis.sof_stdSpace]; exact hsv'
  have h₂ : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s)) sv := by
    rw [Basis.sof_stdSpace]; exact hsvv
  let env : Fin (ValSpace.dofUB sv') → ValExpr := fun i =>
    ValExpr.subst x (.delta i.val sv') v
  have hstep := ValExpr.OpStep.llam_assemble
    (b' := Basis.stdSpace s₀) (b := Basis.stdSpace s)
    (e := e) (env := env)
    (Basis.htof_stdSpace s₀) h₁ h₂
    (EvalCtx.avoidB Ψ) (fun y hy i => by
      simpa only [env] using hv'.delta_of_placeholder hxΨ hy hxb₀ hxsv hxe
        hxbs hlcsv')
  simp only [Basis.sof_stdSpace] at hstep
  exact ⟨_, hstep⟩

end GLang.V2
