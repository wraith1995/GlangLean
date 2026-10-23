

import GLang.Proofs.Progress.Supporting.ProgressMasterDefs

namespace GLang.V2

/-! ## refine_33 `HasType.embed` -/

/-- F6 arm `embed` (refine_33). NEAR-IDENTITY: `pMotiveSub`'s conclusion is
    verbatim the goal's first conjunct (the basis shapes agree definitionally,
    catalog C4/C5); the type is space-typed, so the anchored tail is vacuous
    (the (V) discharge). -/
theorem progress_arm_embed :
    ∀ {ε : NLCtx} {s₀ s₁ : Space} (a : SubType ε s₀ s₁),
      pMotiveSub ε s₀ s₁ →
        pMotiveH ∅ ε (Term.embed s₀) (Ty.space (s₀.dual.tprod s₁)) := by
  intro ε s₀ s₁ _a ih Ψ hP hcov
  exact ⟨ih Ψ hP hcov, fun _ _ h => nomatch h⟩

/-! ## refine_34 `HasType.nllam` -/

/-- F6 arm `nllam` (refine_34), VERBATIM (P5c). -/
theorem progress_arm_nllam :
    ∀ {ε : NLCtx} {τ₀ τ₁ : Ty} {k₀ k₁ : Kind} {e : Term} (L : Finset Name)
      (a : TValid ε (τ₀.piTy τ₁) (k₀.arrow k₁))
      (a : (y : Name) → y ∉ L →
        HasType ∅ (Finmap.insert y τ₀ ε) (Term.openVar y e) (Ty.openVar y τ₁)),
      pMotiveT ε (τ₀.piTy τ₁) →
        (∀ y ∉ L, pMotiveH ∅ (Finmap.insert y τ₀ ε) (Term.openVar y e) (Ty.openVar y τ₁)) →
          pMotiveH ∅ ε (Term.nllam τ₀ e) (τ₀.piTy τ₁) := by
  intro ε τ₀ τ₁ k₀ k₁ e L _htv _hbody ihT ihBody Ψ hP hcov
  -- (1) the carried recursive anchoring of `(τ₀, τ₁)` at Ψ, and its components.
  have hanc : StdPiAnchored Ψ τ₀ τ₁ := (ihT Ψ hP hcov).2 τ₀ τ₁ rfl
  obtain ⟨τv₀, τv₁, h₀A, L₁, h₁A⟩ := hanc.inv
  have h₀ : ValTy.EvalT Ψ τ₀ τv₀ := h₀A.toEvalT
  -- (2) fresh `y₀` against everything the kits/IHs mention.
  obtain ⟨y₀, hy₀⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Ψ ∪ L ∪ Term.fv e ∪ Basis.fv (Basis.std τ₀)
      ∪ Basis.fv (Basis.std τ₁) ∪ ValTy.fv τv₀)
  simp only [Finset.mem_union, not_or] at hy₀
  obtain ⟨⟨⟨⟨⟨hy₀Ψ, hy₀L⟩, hy₀e⟩, hy₀b₀⟩, hy₀b₁⟩, hy₀τv₀⟩ := hy₀
  have hfresh : (y₀, Basis.std τ₀) ∉ Ψ := (EvalCtx.avoidB_spec hy₀Ψ).1 _

  have hpi : ∀ τ₀' τ₁', τ₀ = .piTy τ₀' τ₁' → StdPiAnchored Ψ τ₀' τ₁' :=
    fun _ _ heq => hanc.dom_pi heq
  have hP' := hP.extend_var hfresh (evalT_fv h₀ hP.1) h₀ hpi
  have hcov' : VarsCovered ∅ (Finmap.insert y₀ τ₀ ε)
      (EvalCtx.extend Ψ y₀ (Basis.std τ₀) (.var y₀ τv₀)) := hcov.extend_var
  -- (3) body IH at `y₀`, `Ψ'`.
  obtain ⟨⟨v₀, hv₀⟩, -⟩ := ihBody y₀ hy₀L
    (EvalCtx.extend Ψ y₀ (Basis.std τ₀) (.var y₀ τv₀)) hP' hcov'
  have hlcτv₀ : ValTy.lc τv₀ := evalT_lc h₀ hP.1.toEvalCtxLc
  have hlcv₀ : ValExpr.lc v₀ := opStep_lc hv₀ hP'.1.toEvalCtxLc
  -- (4) cofinite packaging of the body family (P3 kit; basis re-aligned by
  -- `std_openVar`).
  rw [Basis.std_openVar] at hv₀
  obtain ⟨L₂, he₂⟩ := opStep_nllam_cofinite_of_fresh hv₀ hy₀Ψ hy₀b₀ hy₀τv₀
    hy₀e hy₀b₁ hlcτv₀ hlcv₀
  -- (5) fire `OpStep.nllam` at `b₀ := std τ₀`, `b₁ := std τ₁`; the codomain
  -- `h₁` family is the CARRIED anchored family (step 1), forgetfully; the goal
  -- basis `std (.piTy τ₀ τ₁)` is definitionally `.frame (std τ₀) (std τ₁)` (C3).
  refine ⟨⟨_, ValExpr.OpStep.nllam (Basis.tof_std τ₀) (Basis.tof_std τ₁) h₀
      (L₂ ∪ L₁)
      (fun y hy => he₂ y (fun h => hy (Finset.mem_union_left _ h)))
      (fun y hy =>
        (h₁A y (fun h => hy (Finset.mem_union_right _ h))).toEvalT)⟩, ?_⟩
  -- (6) the produced anchored tail: the carried anchoring, verbatim.
  intro τ₀' τ₁' heq
  cases heq
  exact hanc

/-! ## refine_23 `HasType.app_nonlinear` -/

/-- F6 arm `app_nonlinear` (refine_23), VERBATIM (P5c). -/
theorem progress_arm_app_nonlinear :
    ∀ {ε : NLCtx} {e₀ e₁ : Term} {τ₀ τ₁ : Ty}
      (a : HasType ∅ ε e₀ (τ₀.piTy τ₁)) (a : HasType ∅ ε e₁ τ₀),
      pMotiveH ∅ ε e₀ (τ₀.piTy τ₁) → pMotiveH ∅ ε e₁ τ₀ →
        pMotiveH ∅ ε (e₀.appN e₁) (Ty.instantiate e₁ τ₁) := by
  intro ε e₀ e₁ τ₀ τ₁ _ht₀ ht₁ ih₀ ih₁ Ψ hP hcov
  obtain ⟨⟨env₀, h₀⟩, hanchf⟩ := ih₀ Ψ hP hcov
  obtain ⟨⟨env₁, h₁⟩, -⟩ := ih₁ Ψ hP hcov
  -- the carried std-anchored codomain (P5c: recursive; `.inv` exposes the
  -- still-anchored components, `.toEvalT` forgets per consumer).
  have hancPi : StdPiAnchored Ψ τ₀ τ₁ := hanchf τ₀ τ₁ rfl
  obtain ⟨τv₀, τv₁, hev0A, L, hcodA⟩ := hancPi.inv
  have hev0 : ValTy.EvalT Ψ τ₀ τv₀ := hev0A.toEvalT
  -- lc facts (source lc from typing regularity; realized lc from the carrier).
  have hlcn : Term.lc e₁ := ht₁.lc
  have hlcenv₁ : ValExpr.lc env₁ := opStep_lc h₁ hP.1.toEvalCtxLc
  have hlcτv₀ : ValTy.lc τv₀ := evalT_lc hev0 hP.1.toEvalCtxLc
  -- the substitution value: the argument reshaped to the canonical domain
  -- realization (`OpStep.reshape_cob`), making the substituted codomain land
  -- structurally.
  have hev0' : ValTy.EvalT Ψ (Basis.tof (Basis.std τ₀)) τv₀ := by
    rw [Basis.tof_std]; exact hev0
  have hcut : ValExpr.OpStep Ψ e₁ (Basis.std τ₀)
      (.reshap env₁ τv₀ τv₀) :=
    .reshape_cob h₁ hev0' hev0'
  -- fresh `y` for the dependent codomain binder.
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Ψ ∪ L ∪ Basis.fv (Basis.std τ₀) ∪ Ty.fv τ₁ ∪ ValTy.fv τv₁)
  simp only [Finset.mem_union, not_or] at hy
  obtain ⟨⟨⟨⟨hyΨ, hyL⟩, hyb₀⟩, hyτ₁⟩, _hyτv₁⟩ := hy
  obtain ⟨hyfresh, hyvals, hybases⟩ := EvalCtx.avoidB_spec hyΨ
  have hyτv₀ : y ∉ ValTy.fv τv₀ := by
    intro hm
    have hkn : y ∈ Ψ.keyNames := evalT_fv hev0 hP.1 hm
    have : y ∈ EvalCtx.avoidB Ψ := by
      rw [EvalCtx.avoidB, EvalCtx.avoid]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hkn)
    exact hyΨ this
  -- the application `ESubst` (substituting the reshaped argument value).
  have hes := appN_esubst (Ψ₀ := Ψ) (y := y) (b₀ := Basis.std τ₀) (τv₀ := τv₀)
    (n₁ := e₁) (env₁ := .reshap env₁ τv₀ τv₀)
    hyfresh hyb₀
    (fun z b v hl => hyvals (z, b) v hl)
    (fun z b v hl => hybases z b (Finmap.mem_of_lookup_eq_some hl))
    hlcn (.reshap hlcenv₁ hlcτv₀ hlcτv₀)
    (by
      simp only [ValExpr.inferSpace]
      exact (ValSpace.subst_fresh y _ _
        (fun hm => hyτv₀ (ValSpace.fv_spaceOf_subset τv₀ hm))).symm)
    (by simpa only [ValExpr.inferType] using (ValTy.subst_fresh y _ τv₀ hyτv₀).symm)
    hcut
  -- realize the substituted codomain (`appN_realize_core` at `b₁ := std τ₁`).
  have hcody : ValTy.EvalT (EvalCtx.extend Ψ y (Basis.std τ₀) (.var y τv₀))
      (Ty.openVar y (Basis.tof (Basis.std τ₁))) (ValTy.openVar y τv₀ τv₁) := by
    rw [Basis.tof_std]; exact (hcodA y hyL).toEvalT
  have hyfvb₁ : y ∉ Ty.fv (Basis.tof (Basis.std τ₁)) := by
    rw [Basis.tof_std]; exact hyτ₁
  have hout0 := appN_realize_core hes hyfvb₁ hcody
  -- the witness step: plain function eval at the std frame (C3 defeq).
  have hstep := ValExpr.OpStep.appN_val (b₀ := Basis.std τ₀)
    (b₁ := Basis.std τ₁) h₀ h₁ hout0
  -- conclusion basis aligned by C6 (`std_openRec` at k = 0).
  have hstep' : ValExpr.OpStep Ψ (e₀.appN e₁) (Basis.std (Ty.instantiate e₁ τ₁))
      (.applyAt env₀ env₁
        (ValTy.subst y (.reshap env₁ τv₀ τv₀)
          (ValTy.openVar y τv₀ τv₁))) := by
    rw [show Basis.std (Ty.instantiate e₁ τ₁) = Basis.instantiate e₁ (Basis.std τ₁)
      from Basis.std_openRec e₁ τ₁ 0]
    exact hstep
  refine ⟨⟨_, hstep'⟩, ?_⟩
  -- the produced anchored tail at a Π-typed output (R2): transport the
  -- RECURSIVELY anchored codomain family member along the application substitution.
  intro τ₀' τ₁' heq
  have hA := stdAnchored_substC (hcodA y hyL) hes
  rw [show Ty.subst y e₁ (Ty.openVar y τ₁) = Ty.instantiate e₁ τ₁ from
    (Ty.subst_intro y e₁ τ₁ hyτ₁ 0).symm, heq] at hA
  exact ⟨_, hA⟩

end GLang.V2
