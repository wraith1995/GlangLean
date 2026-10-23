

import GLang.Proofs.Progress.Supporting.ProgressMasterDefs

namespace GLang.V2

/-- Restrict a covering to the empty linear context: clause A is vacuous
    (`Finmap.lookup x ∅ = none`), clause B is untouched. Needed to feed the
    `pMotiveS` IHs (stated at `Δ = ∅`) from arms holding `VarsCovered Δ Γ Ψ`
    at an arbitrary (unused) `Δ`. -/
private theorem varsCovered_empty_lin {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    (h : VarsCovered Δ Γ Ψ) : VarsCovered ∅ Γ Ψ :=
  ⟨fun x s hx => by rw [Finmap.lookup_empty] at hx; exact absurd hx (by simp),
   h.2⟩

/-! ## refine_16 `HasType.zero` -/

/-- Arm `HasType.zero` (catalog refine_16): `OpStep.zero` at the standard
    space basis; the rule's `.zero (sof b)` annotation re-aligns by
    `sof_stdSpace`. The Δ-side of the covering is unused (zero types in any
    `Δ`); the space IH is fed through `varsCovered_empty_lin`. Tail: (V). -/
theorem progress_arm_zero :
    ∀ {Δ : LCtx} {ε : NLCtx} {s : Space}, SValid ε s →
      pMotiveS ε s → pMotiveH Δ ε (Term.zero s) (Ty.space s) := by
  intro Δ ε s _ ihs Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨sv, hsv⟩ := ihs Ψ hP (varsCovered_empty_lin hcov)
  have hsv' : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s)) sv := by
    rw [Basis.sof_stdSpace]; exact hsv
  have h := ValExpr.OpStep.zero (Ψ := Ψ) (Basis.htof_stdSpace s) hsv'
  rw [Basis.sof_stdSpace] at h
  exact ⟨.zero sv, h⟩

/-! ## refine_17 `HasType.smul` -/

/-- Arm `HasType.smul` (catalog refine_17): `OpStep.scale` — the scalar
    operand's IH basis `Basis.std (.space .real)` is definitionally `.one`
    (C1/C9), the vector operand stays at `Basis.std (.space s)`; the linear
    split is `VarsCovered.mono_lin` on the rule's disjointness premise.
    Tail: (V); IH witnesses via `.1`. -/
theorem progress_arm_smul :
    ∀ {Δ₀ Δ₁ : LCtx} {ε : NLCtx} {e₀ e₁ : Term} {s : Space}, SValid ε s →
      Finmap.Disjoint Δ₀ Δ₁ →
        HasType Δ₀ ε e₀ (Ty.space Space.real) → HasType Δ₁ ε e₁ (Ty.space s) →
          pMotiveS ε s → pMotiveH Δ₀ ε e₀ (Ty.space Space.real) →
            pMotiveH Δ₁ ε e₁ (Ty.space s) →
              pMotiveH (Δ₀ ∪ Δ₁) ε (e₀.smul e₁) (Ty.space s) := by
  intro Δ₀ Δ₁ ε e₀ e₁ s _ hdisj _ _ _ ih₀ ih₁ Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨hcov₀, hcov₁⟩ := hcov.mono_lin hdisj
  obtain ⟨v₀, hv₀⟩ := (ih₀ Ψ hP hcov₀).1
  obtain ⟨v₁, hv₁⟩ := (ih₁ Ψ hP hcov₁).1
  -- `hv₀` is at `Basis.std (.space .real)` ≡ `.one` (defeq, C1/C9).
  exact ⟨.scale v₀ v₁, .scale hv₀ hv₁⟩

/-! ## refine_18 `HasType.add` -/

/-- Arm `HasType.add` (catalog refine_18): both operands evaluate at the
    shared standard basis, and the `SValid` IH supplies the one result-space
    annotation recorded by `OpStep.add`. Tail: (V); IH witnesses via `.1`. -/
theorem progress_arm_add :
    ∀ {Δ : LCtx} {ε : NLCtx} {e₀ e₁ : Term} {s : Space}, SValid ε s →
      HasType Δ ε e₀ (Ty.space s) → HasType Δ ε e₁ (Ty.space s) →
        pMotiveS ε s → pMotiveH Δ ε e₀ (Ty.space s) →
          pMotiveH Δ ε e₁ (Ty.space s) →
            pMotiveH Δ ε (e₀.add e₁) (Ty.space s) := by
  intro Δ ε e₀ e₁ s _ _ _ ihs ih₀ ih₁ Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨sv, hsv⟩ := ihs Ψ hP (varsCovered_empty_lin hcov)
  obtain ⟨v₀, hv₀⟩ := (ih₀ Ψ hP hcov).1
  obtain ⟨v₁, hv₁⟩ := (ih₁ Ψ hP hcov).1
  have hsv' : ValSpace.EvalS Ψ
      (Basis.sof (Basis.std (Ty.space s))) sv := by
    simpa only [Basis.std, Basis.sof_stdSpace] using hsv
  exact ⟨.vadd sv v₀ v₁,
    .add (Basis.htof_stdSpace s) hsv' hv₀ hv₁⟩

/-! ## refine_19 `HasType.inner` -/

/-- Arm `HasType.inner` (catalog refine_19): `OpStep.inner_std` at
    `b₀ := stdSpace s` (`isStd_stdSpace`, the space IH, `sof_stdSpace`);
    the goal basis `Basis.std (.space (.tprod (.dual s) (.dual s)))` is
    definitionally the rule's `.tprod (.dual (stdSpace s)) (.dual (stdSpace s))`
    (C2). The arm's `Δ` is `∅`, so the covering feeds the space IH directly.
    Tail: (V). -/
theorem progress_arm_inner :
    ∀ {ε : NLCtx} {s : Space}, SValid ε s →
      pMotiveS ε s →
        pMotiveH ∅ ε (Term.inner s) (Ty.space (s.dual.tprod s.dual)) := by
  intro ε s _ ihs Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨sv, hsv⟩ := ihs Ψ hP hcov
  exact ⟨.idelta sv,
    .inner_std (Basis.isStd_stdSpace s) hsv (Basis.sof_stdSpace s)⟩

/-! ## refine_20 `HasType.real_lit` -/

/-- Arm `HasType.real_lit` (catalog refine_20, P2 erratum-fix rule):
    `OpStep.rlit` at `.one`, definitionally `Basis.std (.space .real)` (C1).
    Tail: (V). -/
theorem progress_arm_real_lit :
    ∀ {ε : NLCtx} (r : ℝ),
      pMotiveH ∅ ε (Term.real r) (Ty.space Space.real) := by
  intro ε r Ψ _ _
  exact ⟨⟨.rlit r, .rlit r⟩, fun _ _ h => nomatch h⟩

/-! ## refine_29 `HasType.dsumE` -/

/-- Arm `HasType.dsumE` (catalog refine_29): `OpStep.dsumE` on the two term
    IHs (space-basis premises by `htof_stdSpace`); the goal basis
    `Basis.std (.space (.dsum s₀ s₁))` is definitionally
    `.dsum (stdSpace s₀) (stdSpace s₁)` (C2). No Δ split (shared `Δ`).
    Tail: (V); IH witnesses via `.1`. -/
theorem progress_arm_dsumE :
    ∀ {Δ : LCtx} {ε : NLCtx} {e₀ e₁ : Term} {s₀ s₁ : Space},
      SValid ε s₀ → SValid ε s₁ →
        HasType Δ ε e₀ (Ty.space s₀) → HasType Δ ε e₁ (Ty.space s₁) →
          pMotiveS ε s₀ → pMotiveS ε s₁ → pMotiveH Δ ε e₀ (Ty.space s₀) →
            pMotiveH Δ ε e₁ (Ty.space s₁) →
              pMotiveH Δ ε (e₀.dsumE e₁) (Ty.space (s₀.dsum s₁)) := by
  intro Δ ε e₀ e₁ s₀ s₁ _ _ _ _ _ _ ih₀ ih₁ Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨v₀, hv₀⟩ := (ih₀ Ψ hP hcov).1
  obtain ⟨v₁, hv₁⟩ := (ih₁ Ψ hP hcov).1
  exact ⟨.dsumE v₀ v₁,
    .dsumE hv₀ hv₁ (Basis.htof_stdSpace s₀) (Basis.htof_stdSpace s₁)⟩

/-! ## refine_30 `HasType.tprodE` -/

/-- Arm `HasType.tprodE` (catalog refine_30): as `dsumE` plus the linear
    split (`VarsCovered.mono_lin` on the rule's disjointness premise); goal
    basis definitionally `.tprod (stdSpace s₀) (stdSpace s₁)` (C2).
    Tail: (V); IH witnesses via `.1`. -/
theorem progress_arm_tprodE :
    ∀ {Δ₀ Δ₁ : LCtx} {ε : NLCtx} {e₀ e₁ : Term} {s₀ s₁ : Space},
      SValid ε s₀ → SValid ε s₁ →
        Finmap.Disjoint Δ₀ Δ₁ →
          HasType Δ₀ ε e₀ (Ty.space s₀) → HasType Δ₁ ε e₁ (Ty.space s₁) →
            pMotiveS ε s₀ → pMotiveS ε s₁ → pMotiveH Δ₀ ε e₀ (Ty.space s₀) →
              pMotiveH Δ₁ ε e₁ (Ty.space s₁) →
                pMotiveH (Δ₀ ∪ Δ₁) ε (e₀.tprodE e₁)
                  (Ty.space (s₀.tprod s₁)) := by
  intro Δ₀ Δ₁ ε e₀ e₁ s₀ s₁ _ _ hdisj _ _ _ _ ih₀ ih₁ Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨hcov₀, hcov₁⟩ := hcov.mono_lin hdisj
  obtain ⟨v₀, hv₀⟩ := (ih₀ Ψ hP hcov₀).1
  obtain ⟨v₁, hv₁⟩ := (ih₁ Ψ hP hcov₁).1
  exact ⟨.tprodE v₀ v₁,
    .tprodE hv₀ hv₁ (Basis.htof_stdSpace s₀) (Basis.htof_stdSpace s₁)⟩

end GLang.V2
