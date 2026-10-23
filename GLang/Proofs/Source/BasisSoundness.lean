/-
# Basis denotation soundness

This module proves the cases of `denotBasis_isBasis`, the space-level standard
basis orthonormality theorem, and the list-basis facts used by adequacy.
`GLang.BasisSoundness` supplies `IsListBasis`, `SoundOfDenot`, and their
linear-algebra lemmas. Projected bases use the proved spectral constructions
in `GLang.BasisFSV`; term bases use the proved `HSpace.lexInd` properties.

The recursive type-level standard-basis theorem, including dependent frames,
is `stdBasis_orthonormal` in `GLang.BasisOrthonormalAt`.
-/

import GLang.Proofs.Basis.BasisSoundness
import GLang.Proofs.Source.Soundness
import GLang.Proofs.Basis.BasisSoundnessLive
import GLang.Operational.Ordinary

namespace GLang

/-! ## B4 closure (first path): `denotBasis_atSpace_ok`.

The `BasisDenot.atSpace` helper uses a `Classical.dec` carrier-equality
cast . For well-typed inputs the cast is the
identity. Concretely: when `denotBasis σ b = .vecs V' vs` and we know
that `V'.carrier = V.carrier` because both came from `denotSpace σ
(Basis.sof b)`, the cast reduces to the underlying list `vs`.

We state the lemma in its strongest form (the cast becomes literally
`vs`, no `▸` arithmetic visible) — the proof is `rfl` for the cases
where `denotBasis` lands on `.vecs V'`s whose `V'` is *definitionally*
`denotSpace σ (Basis.sof b)`.

Placed BEFORE the main theorem so the `.dsum` / `.tprod` cases can call
it inside the induction.  -/

/-- **B4 closure (statement at the `denotBasis` level).** Under the
    soundness predicate, `BasisDenot.atSpace` of `denotBasis σ b` at the
    expected `denotSpace σ (Basis.sof b)` equals the underlying list
    that `denotBasis` produced — up to the (provably-identity-on-this-
    path) carrier-equality cast.

    `SoundOfDenot` supplies equality of the denoted spaces and the list-basis
    property. The vector case uses `atSpace_vecs_eq`; the frame case is
    excluded by the shape of the soundness hypothesis. -/
theorem denotBasis_atSpace_ok {σ : DEnv} {b : Basis}
    (h_sound : SoundOfDenot (.vecs (denotSpace σ (Basis.sof b))) (denotBasis σ b)) :
    -- The cast in `atSpace` vanishes whenever soundness gives us the
    -- HSpace-equality witness explicitly.
    ∃ vs : List (denotSpace σ (Basis.sof b)).carrier,
      BasisDenot.atSpace (denotSpace σ (Basis.sof b)) (denotBasis σ b) = vs ∧
      IsListBasis (denotSpace σ (Basis.sof b)) vs := by
  -- Case-split on what shape `denotBasis σ b` produced.
  cases hd : denotBasis σ b with
  | vecs V' vs =>
      rw [hd] at h_sound
      unfold SoundOfDenot at h_sound
      obtain ⟨h_eq, h_basis⟩ := h_sound
      refine ⟨h_eq ▸ vs, ?_, ?_⟩
      · exact BasisDenot.atSpace_vecs_eq vs h_eq
      · exact h_basis
  | frame T f =>

      rw [hd] at h_sound
      exact absurd h_sound (by unfold SoundOfDenot; exact not_false)

/-! ## `IsListBasis.dual` — closed.

The dual list `HSpace.dualOfList V vs` is constructed via the Gram-inverse
formula `w_i = Σ_k (G⁻¹)_{ik} • V.IP v_k`. When the input list `vs` is a
basis (`IsListBasis V vs`), the Gram matrix `G_{ij} = ⟨v_i, v_j⟩` is
invertible (PD, since LI ⇒ PD via the standard `x^T G x = ⟨Σ x_i v_i,
Σ x_j v_j⟩ > 0` argument), and the resulting `w_i` satisfy the duality
identity `w_i(v_j) = δ_{ij}`. Mathlib's `Module.DualBases.basis.dualBasis`
machinery then certifies that the `w_i` form a basis of the dual space.

**Status.** Closed. The lemma `IsListBasis.dual` is proved in
`GLang/Proofs/Basis/BasisSoundness.lean` under the heading "Gram-matrix helpers for
`.dual` (agent: dual)". The closure path traversed:

  (i)   `IsListBasis.gram_dotProduct_mulVec` — bilinearity expansion
        `Σᵢⱼ xᵢ xⱼ ⟨vᵢ, vⱼ⟩ = ⟨Σᵢ xᵢ vᵢ, Σⱼ xⱼ vⱼ⟩`.
  (ii)  `IsListBasis.gram_posDef` — combines with `LinearIndependent`
        + IP definiteness/positivity to yield `Matrix.PosDef G`.
  (iii) `IsListBasis.gram_isUnit` — via `Matrix.PosDef.isUnit`.
  (iv)  `IsListBasis.dual_delta` — δ identity `w_i (v_j) = δᵢⱼ` via
        `Matrix.nonsing_inv_mul` on `G⁻¹ * G = 1`.
  (v)   `IsListBasis.dualBases` — `Module.DualBases (vs.get) (dualVec)`
        instance (eval_same, eval_of_ne, total via span+LI).
  (vi)  `IsListBasis.dual` — applies `Module.DualBases.basis.dualBasis`
        together with `coe_dualBasis` and `IsListBasis.of_basis_fin`.

The wrappers in `denotBasis_isBasis` below just call `IsListBasis.dual`
on the recovered list basis. -/

/-! ## Projected-basis soundness

The four subspace cases use the proved FSV containment, independence, and
length theorems through `IsListBasis.of_fsv_contract`. The main induction
below dispatches to these lemmas. -/

/-- **Obligation (kernel `.proj`).** When `BasisValid` holds and
    `Basis.sof (.proj (.ker s₀ s₁ e) b₀ b₁) = .ker s₀ s₁ e`, the
    `BasisFSV.fsvLeft f (· = 0) …` output (lifted via `liftToSubmodule
    (ker f)`) is a basis of `HSpace.ofSubmodule V₀ (LinearMap.ker f)`.
    Reduces to `fsvLeft_subset_ker` + `fsvLeft_linearly_independent`
    + `fsvLeft_dim_eq`. -/
theorem denotBasis_proj_ker_isBasis (σ : DEnv) (ε : NLCtx)
    (s₀ s₁ : Space) (e : Term) (b₀ b₁ : Basis)
    (_hb : Basis.BasisValid ε (.proj (.ker s₀ s₁ e) b₀ b₁))
    (_hσ : EnvWF σ ∅ ε) :
    SoundOfDenot
      (.vecs (denotSpace σ (Basis.sof (.proj (.ker s₀ s₁ e) b₀ b₁))))
      (denotBasis σ (.proj (.ker s₀ s₁ e) b₀ b₁)) := by
  set V₀ : HSpace := denotSpace σ s₀ with hV₀
  set V₁ : HSpace := denotSpace σ s₁ with hV₁
  set f : V₀.carrier →ₗ[ℝ] V₁.carrier := (denotTerm σ e).asLinMap V₀ V₁ with hf
  set vs₀ : List V₀.carrier := (denotBasis σ b₀).atSpace V₀ with hvs₀
  set vs₁ : List V₁.carrier := (denotBasis σ b₁).atSpace V₁ with hvs₁
  set raw : List V₀.carrier :=
    BasisFSV.fsvLeft V₀ V₁ f (fun μ => decide (μ = 0)) vs₀ vs₁ with hraw
  set K : Submodule ℝ V₀.carrier := LinearMap.ker f with hK
  simp only [Basis.sof, denotSpace, denotBasis]
  refine ⟨rfl, ?_⟩
  exact IsListBasis.of_fsv_contract V₀ K raw
    (BasisFSV.fsvLeft_subset_ker V₀ V₁ f vs₀ vs₁)
    (BasisFSV.fsvLeft_linearly_independent V₀ V₁ f
      (fun μ => decide (μ = 0)) vs₀ vs₁)
    (BasisFSV.fsvLeft_dim_eq V₀ V₁ f vs₀ vs₁)

/-- **Obligation (cokernel `.proj`).** Analogue for `.coker`, lifted
    via `liftToSubmodule (orthRel V₀.IP (ker f))`. Reduces to
    `fsvLeft_subset_coker` + LI + `fsvLeft_dim_eq_coker`. -/
theorem denotBasis_proj_coker_isBasis (σ : DEnv) (ε : NLCtx)
    (s₀ s₁ : Space) (e : Term) (b₀ b₁ : Basis)
    (_hb : Basis.BasisValid ε (.proj (.coker s₀ s₁ e) b₀ b₁))
    (_hσ : EnvWF σ ∅ ε) :
    SoundOfDenot
      (.vecs (denotSpace σ (Basis.sof (.proj (.coker s₀ s₁ e) b₀ b₁))))
      (denotBasis σ (.proj (.coker s₀ s₁ e) b₀ b₁)) := by
  set V₀ : HSpace := denotSpace σ s₀ with hV₀
  set V₁ : HSpace := denotSpace σ s₁ with hV₁
  set f : V₀.carrier →ₗ[ℝ] V₁.carrier := (denotTerm σ e).asLinMap V₀ V₁ with hf
  set vs₀ : List V₀.carrier := (denotBasis σ b₀).atSpace V₀ with hvs₀
  set vs₁ : List V₁.carrier := (denotBasis σ b₁).atSpace V₁ with hvs₁
  set raw : List V₀.carrier :=
    BasisFSV.fsvLeft V₀ V₁ f (fun μ => decide (μ ≠ 0)) vs₀ vs₁ with hraw
  set K : Submodule ℝ V₀.carrier :=
    Submodule.orthRel V₀.innerProduct (LinearMap.ker f) with hK
  simp only [Basis.sof, denotSpace, denotBasis]
  refine ⟨rfl, ?_⟩
  exact IsListBasis.of_fsv_contract V₀ K raw
    (BasisFSV.fsvLeft_subset_coker V₀ V₁ f vs₀ vs₁)
    (BasisFSV.fsvLeft_linearly_independent V₀ V₁ f
      (fun μ => decide (μ ≠ 0)) vs₀ vs₁)
    (BasisFSV.fsvLeft_dim_eq_coker V₀ V₁ f vs₀ vs₁)

/-- **Obligation (image `.proj`).** Analogue for `.img`, lifted via
    `liftToSubmodule (LinearMap.range f)`. Reduces to
    `fsvRight_subset_range` + LI + `fsvRight_dim_eq`. -/
theorem denotBasis_proj_img_isBasis (σ : DEnv) (ε : NLCtx)
    (s₀ s₁ : Space) (e : Term) (b₀ b₁ : Basis)
    (_hb : Basis.BasisValid ε (.proj (.img s₀ s₁ e) b₀ b₁))
    (_hσ : EnvWF σ ∅ ε) :
    SoundOfDenot
      (.vecs (denotSpace σ (Basis.sof (.proj (.img s₀ s₁ e) b₀ b₁))))
      (denotBasis σ (.proj (.img s₀ s₁ e) b₀ b₁)) := by
  set V₀ : HSpace := denotSpace σ s₀ with hV₀
  set V₁ : HSpace := denotSpace σ s₁ with hV₁
  set f : V₀.carrier →ₗ[ℝ] V₁.carrier := (denotTerm σ e).asLinMap V₀ V₁ with hf
  set vs₀ : List V₀.carrier := (denotBasis σ b₀).atSpace V₀ with hvs₀
  set vs₁ : List V₁.carrier := (denotBasis σ b₁).atSpace V₁ with hvs₁
  set raw : List V₁.carrier :=
    BasisFSV.fsvRight V₀ V₁ f (fun μ => decide (μ ≠ 0)) vs₀ vs₁ with hraw
  set K : Submodule ℝ V₁.carrier := LinearMap.range f with hK
  simp only [Basis.sof, denotSpace, denotBasis]
  refine ⟨rfl, ?_⟩
  exact IsListBasis.of_fsv_contract V₁ K raw
    (BasisFSV.fsvRight_subset_range V₀ V₁ f vs₀ vs₁)
    (BasisFSV.fsvRight_linearly_independent V₀ V₁ f
      (fun μ => decide (μ ≠ 0)) vs₀ vs₁)
    (BasisFSV.fsvRight_dim_eq V₀ V₁ f vs₀ vs₁)

/-- **Obligation (coimage `.proj`).** Analogue for `.coimg`, lifted via
    `liftToSubmodule (orthRel V₁.IP (range f))`. Reduces to
    `fsvRight_subset_coimg` + LI + `fsvRight_dim_eq_coimg`. -/
theorem denotBasis_proj_coimg_isBasis (σ : DEnv) (ε : NLCtx)
    (s₀ s₁ : Space) (e : Term) (b₀ b₁ : Basis)
    (_hb : Basis.BasisValid ε (.proj (.coimg s₀ s₁ e) b₀ b₁))
    (_hσ : EnvWF σ ∅ ε) :
    SoundOfDenot
      (.vecs (denotSpace σ (Basis.sof (.proj (.coimg s₀ s₁ e) b₀ b₁))))
      (denotBasis σ (.proj (.coimg s₀ s₁ e) b₀ b₁)) := by
  set V₀ : HSpace := denotSpace σ s₀ with hV₀
  set V₁ : HSpace := denotSpace σ s₁ with hV₁
  set f : V₀.carrier →ₗ[ℝ] V₁.carrier := (denotTerm σ e).asLinMap V₀ V₁ with hf
  set vs₀ : List V₀.carrier := (denotBasis σ b₀).atSpace V₀ with hvs₀
  set vs₁ : List V₁.carrier := (denotBasis σ b₁).atSpace V₁ with hvs₁
  set raw : List V₁.carrier :=
    BasisFSV.fsvRight V₀ V₁ f (fun μ => decide (μ = 0)) vs₀ vs₁ with hraw
  set K : Submodule ℝ V₁.carrier :=
    Submodule.orthRel V₁.innerProduct (LinearMap.range f) with hK
  simp only [Basis.sof, denotSpace, denotBasis]
  refine ⟨rfl, ?_⟩
  exact IsListBasis.of_fsv_contract V₁ K raw
    (BasisFSV.fsvRight_subset_coimg V₀ V₁ f vs₀ vs₁)
    (BasisFSV.fsvRight_linearly_independent V₀ V₁ f
      (fun μ => decide (μ = 0)) vs₀ vs₁)
    (BasisFSV.fsvRight_dim_eq_coimg V₀ V₁ f vs₀ vs₁)

/-! ## The main soundness theorem. -/

set_option maxHeartbeats 5000000 in
/-- **Main soundness theorem (statement).** If `b` is a valid basis in
    context `ε` and `σ` matches `ε` (no linear context — bases are
    pure-`ε` syntactic objects), then `denotBasis σ b` is sound at the
    expected space `denotSpace σ (Basis.sof b)`. -/
theorem denotBasis_isBasis (σ : DEnv) (ε : NLCtx) (b : Basis)
    (hb : Basis.BasisValid ε b)
    (_hctx : CtxWF ∅ ε)
    (_hσ : EnvWF σ ∅ ε) :
    SoundOfDenot (ExpectedSpace.ofBasis σ b) (denotBasis σ b) := by
  cases b with
  | empty =>
      -- denotBasis σ .empty = .vecs HSpace.empty []
      -- ExpectedSpace.ofBasis σ .empty = .vecs HSpace.empty
      -- IsListBasis HSpace.empty [] holds vacuously: PUnit is the zero module.
      simp only [ExpectedSpace.ofBasis, Basis.sof, denotSpace, denotBasis,
        SoundOfDenot]
      exact ⟨rfl, isListBasis_empty⟩
  | one =>
      -- denotBasis σ .one = .vecs HSpace.real [(1 : ℝ)]
      -- ExpectedSpace.ofBasis σ .one = .vecs HSpace.real
      simp only [ExpectedSpace.ofBasis, Basis.sof, denotSpace, denotBasis,
        SoundOfDenot]
      exact ⟨rfl, isListBasis_one⟩
  | dual b =>
      -- Strategy: apply IH on `b` to get `SoundOfDenot V (denotBasis σ b)`,
      -- case-split on whether `b` is `.frame`-shape. For non-`.frame` bases,
      -- extract an `IsListBasis V vs` (via `denotBasis_atSpace_ok`), then
      -- apply `IsListBasis.dual` to lift it through the Gram-corrected
      -- dual construction (`HSpace.dualOfList`). The `.frame` sub-case is
      -- degenerate (Basis.sof (.frame _ _ _) = .empty so V = HSpace.empty;
      -- the dual list is empty; isListBasis_empty closes it).
      cases b with
      | empty =>
          have h_sound := denotBasis_isBasis σ ε Basis.empty hb.dual_inv _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.dual Basis.empty) =
                .vecs (HSpace.dual (denotSpace σ (Basis.sof Basis.empty)))
                      ((denotSpace σ (Basis.sof Basis.empty)).dualOfList vsList) := by
            -- Unfold denotBasis on the outer .dual to expose the inner atSpace.
            show denotBasis σ _ = _
            unfold denotBasis

            simp only []
            -- Try to rewrite the atSpace; if Lean's simp doesn't reduce the let,
            -- use conv to descend.
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : HSpace.dual (denotSpace σ (Basis.sof Basis.empty)) =
                     denotSpace σ (Basis.dual Basis.empty).sof,
                  IsListBasis (denotSpace σ (Basis.dual Basis.empty).sof)
                    (h ▸ (denotSpace σ (Basis.sof Basis.empty)).dualOfList vsList)
          refine ⟨rfl, ?_⟩
          exact IsListBasis.dual h_basis
      | one =>
          have h_sound := denotBasis_isBasis σ ε Basis.one hb.dual_inv _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.dual Basis.one) =
                .vecs (HSpace.dual (denotSpace σ (Basis.sof Basis.one)))
                      ((denotSpace σ (Basis.sof Basis.one)).dualOfList vsList) := by
            -- Unfold denotBasis on the outer .dual to expose the inner atSpace.
            show denotBasis σ _ = _
            unfold denotBasis

            simp only []
            -- Try to rewrite the atSpace; if Lean's simp doesn't reduce the let,
            -- use conv to descend.
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : HSpace.dual (denotSpace σ (Basis.sof Basis.one)) =
                     denotSpace σ (Basis.dual Basis.one).sof,
                  IsListBasis (denotSpace σ (Basis.dual Basis.one).sof)
                    (h ▸ (denotSpace σ (Basis.sof Basis.one)).dualOfList vsList)
          refine ⟨rfl, ?_⟩
          exact IsListBasis.dual h_basis
      | dual b' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.dual b') hb.dual_inv _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.dual (Basis.dual b')) =
                .vecs (HSpace.dual (denotSpace σ (Basis.sof (Basis.dual b'))))
                  ((denotSpace σ (Basis.sof (Basis.dual b'))).dualOfList vsList) := by
            -- Unfold denotBasis on the outer .dual to expose the inner atSpace.
            show denotBasis σ _ = _
            unfold denotBasis

            simp only []
            -- Try to rewrite the atSpace; if Lean's simp doesn't reduce the let,
            -- use conv to descend.
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : HSpace.dual (denotSpace σ (Basis.sof (Basis.dual b'))) =
                     denotSpace σ (Basis.dual (Basis.dual b')).sof,
                  IsListBasis (denotSpace σ (Basis.dual (Basis.dual b')).sof)
                    (h ▸ (denotSpace σ (Basis.sof (Basis.dual b'))).dualOfList vsList)
          refine ⟨rfl, ?_⟩
          exact IsListBasis.dual h_basis
      | dsum b₀' b₁' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.dsum b₀' b₁') hb.dual_inv _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.dual (Basis.dsum b₀' b₁')) =
                .vecs (HSpace.dual (denotSpace σ (Basis.sof (Basis.dsum b₀' b₁'))))
                  ((denotSpace σ (Basis.sof (Basis.dsum b₀' b₁'))).dualOfList vsList) := by
            -- Unfold denotBasis on the outer .dual to expose the inner atSpace.
            show denotBasis σ _ = _
            unfold denotBasis

            simp only []
            -- Try to rewrite the atSpace; if Lean's simp doesn't reduce the let,
            -- use conv to descend.
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : HSpace.dual (denotSpace σ (Basis.sof (Basis.dsum b₀' b₁'))) =
                     denotSpace σ (Basis.dual (Basis.dsum b₀' b₁')).sof,
                  IsListBasis (denotSpace σ (Basis.dual (Basis.dsum b₀' b₁')).sof)
                    (h ▸ (denotSpace σ (Basis.sof (Basis.dsum b₀' b₁'))).dualOfList vsList)
          refine ⟨rfl, ?_⟩
          exact IsListBasis.dual h_basis
      | tprod b₀' b₁' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.tprod b₀' b₁') hb.dual_inv _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.dual (Basis.tprod b₀' b₁')) =
                .vecs (HSpace.dual (denotSpace σ (Basis.sof (Basis.tprod b₀' b₁'))))
                  ((denotSpace σ (Basis.sof (Basis.tprod b₀' b₁'))).dualOfList vsList) := by
            -- Unfold denotBasis on the outer .dual to expose the inner atSpace.
            show denotBasis σ _ = _
            unfold denotBasis

            simp only []
            -- Try to rewrite the atSpace; if Lean's simp doesn't reduce the let,
            -- use conv to descend.
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : HSpace.dual (denotSpace σ (Basis.sof (Basis.tprod b₀' b₁'))) =
                     denotSpace σ (Basis.dual (Basis.tprod b₀' b₁')).sof,
                  IsListBasis (denotSpace σ (Basis.dual (Basis.tprod b₀' b₁')).sof)
                    (h ▸ (denotSpace σ (Basis.sof (Basis.tprod b₀' b₁'))).dualOfList vsList)
          refine ⟨rfl, ?_⟩
          exact IsListBasis.dual h_basis
      | proj s' b₀' b₁' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.proj s' b₀' b₁') hb.dual_inv _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.dual (Basis.proj s' b₀' b₁')) =
                .vecs (HSpace.dual (denotSpace σ (Basis.sof (Basis.proj s' b₀' b₁'))))
                  ((denotSpace σ (Basis.sof (Basis.proj s' b₀' b₁'))).dualOfList vsList) := by
            -- Unfold denotBasis on the outer .dual to expose the inner atSpace.
            show denotBasis σ _ = _
            unfold denotBasis

            simp only []
            -- Try to rewrite the atSpace; if Lean's simp doesn't reduce the let,
            -- use conv to descend.
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : HSpace.dual (denotSpace σ (Basis.sof (Basis.proj s' b₀' b₁'))) =
                     denotSpace σ (Basis.dual (Basis.proj s' b₀' b₁')).sof,
                  IsListBasis (denotSpace σ (Basis.dual (Basis.proj s' b₀' b₁')).sof)
                    (h ▸ (denotSpace σ (Basis.sof (Basis.proj s' b₀' b₁'))).dualOfList vsList)
          refine ⟨rfl, ?_⟩
          exact IsListBasis.dual h_basis
      | image b' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.image b') hb.dual_inv _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.dual (Basis.image b')) =
                .vecs (HSpace.dual (denotSpace σ (Basis.sof (Basis.image b'))))
                  ((denotSpace σ (Basis.sof (Basis.image b'))).dualOfList vsList) := by
            -- Unfold denotBasis on the outer .dual to expose the inner atSpace.
            show denotBasis σ _ = _
            unfold denotBasis

            simp only []
            -- Try to rewrite the atSpace; if Lean's simp doesn't reduce the let,
            -- use conv to descend.
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : HSpace.dual (denotSpace σ (Basis.sof (Basis.image b'))) =
                     denotSpace σ (Basis.dual (Basis.image b')).sof,
                  IsListBasis (denotSpace σ (Basis.dual (Basis.image b')).sof)
                    (h ▸ (denotSpace σ (Basis.sof (Basis.image b'))).dualOfList vsList)
          refine ⟨rfl, ?_⟩
          exact IsListBasis.dual h_basis
      | terms s' es' b' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.terms s' es' b') hb.dual_inv _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.dual (Basis.terms s' es' b')) =
                .vecs (HSpace.dual (denotSpace σ (Basis.sof (Basis.terms s' es' b'))))
                  ((denotSpace σ
                      (Basis.sof (Basis.terms s' es' b'))).dualOfList vsList) := by
            -- Unfold denotBasis on the outer .dual to expose the inner atSpace.
            show denotBasis σ _ = _
            unfold denotBasis

            simp only []
            -- Try to rewrite the atSpace; if Lean's simp doesn't reduce the let,
            -- use conv to descend.
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : HSpace.dual (denotSpace σ (Basis.sof (Basis.terms s' es' b'))) =
                     denotSpace σ (Basis.dual (Basis.terms s' es' b')).sof,
                  IsListBasis (denotSpace σ (Basis.dual (Basis.terms s' es' b')).sof)
                    (h ▸ (denotSpace σ
                            (Basis.sof (Basis.terms s' es' b'))).dualOfList vsList)
          refine ⟨rfl, ?_⟩
          exact IsListBasis.dual h_basis
      | frame b₀ b₁ =>
          -- Degenerate: Basis.sof (.frame ...) = .empty, so
          -- denotSpace σ (Basis.sof (.dual (.frame ...))) =
          --   HSpace.dual (denotSpace σ .empty) = HSpace.dual HSpace.empty.
          -- The dual list is dualOfList HSpace.empty [] = [] (since vs = []),
          -- and (HSpace.dual HSpace.empty) is also a trivial space, so
          -- isListBasis_empty applies after a carrier-equality argument...
          -- ...but HSpace.dual HSpace.empty's carrier is PUnit →ₗ ℝ which is
          -- ZERO-DIM, so "[]" is a basis trivially. We use isListBasis_empty
          -- after observing the carrier of HSpace.dual HSpace.empty is
          -- equivalent to PUnit. Concretely, isListBasis_dual_empty:
          show SoundOfDenot (ExpectedSpace.ofBasis σ (Basis.dual _)) _
          simp only [ExpectedSpace.ofBasis, Basis.sof, denotSpace, denotBasis]
          unfold SoundOfDenot
          refine ⟨rfl, ?_⟩
          -- After simp, goal is IsListBasis (HSpace.dual HSpace.empty)
          --   (HSpace.dualOfList HSpace.empty
          --     ((denotBasis σ (.frame ...)).atSpace HSpace.empty)).
          -- (denotBasis σ (.frame ...)).atSpace HSpace.empty = [] (by atSpace_frame).
          -- So the dualOfList of [] is []. And IsListBasis _ [] holds for any
          -- HSpace whose carrier is the zero module — but HSpace.dual
          -- HSpace.empty has carrier PUnit →ₗ ℝ, which IS the zero module
          -- (since PUnit is zero). We rely on isListBasis_dual_empty
          -- (added in BasisSoundness.lean).
          simp only [BasisDenot.atSpace_frame, HSpace.dualOfList_nil]
          exact isListBasis_dual_empty
  | dsum b₀ b₁ =>

      obtain ⟨hb₀, hb₁⟩ := hb.dsum_inv
      have h_sound_0 := denotBasis_isBasis σ ε b₀ hb₀ _hctx _hσ
      have h_sound_1 := denotBasis_isBasis σ ε b₁ hb₁ _hctx _hσ

      cases b₀ with
      | empty | one | dual _ | dsum _ _ | tprod _ _
      | proj _ _ _ | image _ | terms _ _ _ =>
          (cases b₁ with
          | empty | one | dual _ | dsum _ _ | tprod _ _
          | proj _ _ _ | image _ | terms _ _ _ =>
              -- Both non-frame: rewrite IHs to `.vecs`-shape via the
              -- `ofBasis_vecs_of_not_frame` lemma, then apply the
              -- `denotBasis_atSpace_ok` + `IsListBasis.dsum` bridge.
              rw [ExpectedSpace.ofBasis_vecs_of_not_frame (by intros; exact Basis.noConfusion)] at h_sound_0
              rw [ExpectedSpace.ofBasis_vecs_of_not_frame (by intros; exact Basis.noConfusion)] at h_sound_1
              obtain ⟨vs₀, h_atSpace₀, h_basis₀⟩ := denotBasis_atSpace_ok h_sound_0
              obtain ⟨vs₁, h_atSpace₁, h_basis₁⟩ := denotBasis_atSpace_ok h_sound_1
              -- Reduce all of denotBasis on the LHS of the IH facts to
              -- match the goal's simp-normalised form.
              simp only [denotBasis, Basis.sof] at h_atSpace₀ h_atSpace₁
              rw [ExpectedSpace.ofBasis_dsum]
              show SoundOfDenot (.vecs (denotSpace σ (Basis.sof (Basis.dsum _ _))))
                  (denotBasis σ (Basis.dsum _ _))
              simp only [Basis.sof, denotSpace, denotBasis]
              show SoundOfDenot (.vecs (HSpace.dsum _ _)) (.vecs _ _)
              unfold SoundOfDenot
              refine ⟨rfl, ?_⟩
              show IsListBasis (HSpace.dsum _ _) _
              -- `convert` matches the dsum-of-bases structurally; in
              -- some cases the IH `vs₀ = atSpace (denotBasis _ _)`
              -- collapses the matched holes, in others `convert` leaves
              -- residual equality goals discharged by the atSpace facts.
              first
              | (convert IsListBasis.dsum h_basis₀ h_basis₁ using 2)
              | (convert IsListBasis.dsum h_basis₀ h_basis₁ using 2 <;>
                 first | exact h_atSpace₀ | exact h_atSpace₁ | rfl)
          | frame b₁₀ b₁₁ =>
              -- b₁ is a frame: vs₁ = (denotBasis σ b₁).atSpace V₁ = [] (since
              -- denotBasis σ (.frame _ _ _) is `.frame`-shape and `atSpace` of
              -- frame is `[]`). Also V₁ = denotSpace σ .empty = HSpace.empty
              -- since Basis.sof (.frame _ _ _) = .empty. Use IH₀ for vs₀ and
              -- `isListBasis_empty` for the empty RHS.
              rw [ExpectedSpace.ofBasis_vecs_of_not_frame (by intros; exact Basis.noConfusion)] at h_sound_0
              obtain ⟨vs₀, h_atSpace₀, h_basis₀⟩ := denotBasis_atSpace_ok h_sound_0
              simp only [denotBasis, Basis.sof] at h_atSpace₀
              rw [ExpectedSpace.ofBasis_dsum]
              show SoundOfDenot (.vecs (denotSpace σ (Basis.sof (Basis.dsum _ _))))
                  (denotBasis σ (Basis.dsum _ _))
              simp only [Basis.sof, denotSpace, denotBasis,
                         BasisDenot.atSpace_frame]
              show SoundOfDenot (.vecs (HSpace.dsum _ HSpace.empty)) (.vecs _ _)
              unfold SoundOfDenot
              refine ⟨rfl, ?_⟩
              -- After atSpace_frame simp, the second list in dsumOfLists is [].
              rw [h_atSpace₀]
              exact IsListBasis.dsum h_basis₀ isListBasis_empty)
      | frame b₀₀ b₀₁ =>
          -- b₀ is a frame. Then V₀ = HSpace.empty (since Basis.sof of frame is
          -- .empty) and vs₀ = []. Case-split on b₁.
          cases b₁ with
          | empty | one | dual _ | dsum _ _ | tprod _ _
          | proj _ _ _ | image _ | terms _ _ _ =>
              -- b₀ frame, b₁ non-frame: use IH₁ on b₁ and isListBasis_empty on b₀.
              rw [ExpectedSpace.ofBasis_vecs_of_not_frame (by intros; exact Basis.noConfusion)] at h_sound_1
              obtain ⟨vs₁, h_atSpace₁, h_basis₁⟩ := denotBasis_atSpace_ok h_sound_1
              simp only [denotBasis, Basis.sof] at h_atSpace₁
              rw [ExpectedSpace.ofBasis_dsum]
              show SoundOfDenot (.vecs (denotSpace σ (Basis.sof (Basis.dsum _ _))))
                  (denotBasis σ (Basis.dsum _ _))
              simp only [Basis.sof, denotSpace, denotBasis,
                         BasisDenot.atSpace_frame]
              show SoundOfDenot (.vecs (HSpace.dsum HSpace.empty _)) (.vecs _ _)
              unfold SoundOfDenot
              refine ⟨rfl, ?_⟩
              rw [h_atSpace₁]
              exact IsListBasis.dsum isListBasis_empty h_basis₁
          | frame b₁₀ b₁₁ =>
              -- Both frames: V₀ = V₁ = HSpace.empty, vs₀ = vs₁ = [].
              rw [ExpectedSpace.ofBasis_dsum]
              show SoundOfDenot (.vecs (denotSpace σ (Basis.sof (Basis.dsum _ _))))
                  (denotBasis σ (Basis.dsum _ _))
              simp only [Basis.sof, denotSpace, denotBasis,
                         BasisDenot.atSpace_frame]
              show SoundOfDenot (.vecs (HSpace.dsum HSpace.empty HSpace.empty))
                                (.vecs _ _)
              unfold SoundOfDenot
              refine ⟨rfl, ?_⟩
              exact IsListBasis.dsum isListBasis_empty isListBasis_empty
  | tprod b₀ b₁ =>
      -- Analogue of `.dsum` with the same frame-inside-tprod residual.
      obtain ⟨hb₀, hb₁⟩ := hb.tprod_inv
      have h_sound_0 := denotBasis_isBasis σ ε b₀ hb₀ _hctx _hσ
      have h_sound_1 := denotBasis_isBasis σ ε b₁ hb₁ _hctx _hσ
      cases b₀ with
      | empty | one | dual _ | dsum _ _ | tprod _ _
      | proj _ _ _ | image _ | terms _ _ _ =>
          (cases b₁ with
          | empty | one | dual _ | dsum _ _ | tprod _ _
          | proj _ _ _ | image _ | terms _ _ _ =>
              rw [ExpectedSpace.ofBasis_vecs_of_not_frame (by intros; exact Basis.noConfusion)] at h_sound_0
              rw [ExpectedSpace.ofBasis_vecs_of_not_frame (by intros; exact Basis.noConfusion)] at h_sound_1
              obtain ⟨vs₀, h_atSpace₀, h_basis₀⟩ := denotBasis_atSpace_ok h_sound_0
              obtain ⟨vs₁, h_atSpace₁, h_basis₁⟩ := denotBasis_atSpace_ok h_sound_1
              simp only [denotBasis, Basis.sof] at h_atSpace₀ h_atSpace₁
              rw [ExpectedSpace.ofBasis_tprod]
              show SoundOfDenot (.vecs (denotSpace σ (Basis.sof (Basis.tprod _ _))))
                  (denotBasis σ (Basis.tprod _ _))
              simp only [Basis.sof, denotSpace, denotBasis]
              show SoundOfDenot (.vecs (HSpace.tprod _ _)) (.vecs _ _)
              unfold SoundOfDenot
              refine ⟨rfl, ?_⟩
              show IsListBasis (HSpace.tprod _ _) _
              first
              | (convert IsListBasis.tprod h_basis₀ h_basis₁ using 2)
              | (convert IsListBasis.tprod h_basis₀ h_basis₁ using 2 <;>
                 first | exact h_atSpace₀ | exact h_atSpace₁ | rfl)
          | frame b₁₀ b₁₁ =>
              -- b₁ is a frame: vs₁ = []; V₁ = HSpace.empty. Use IH₀ + emptiness.
              rw [ExpectedSpace.ofBasis_vecs_of_not_frame (by intros; exact Basis.noConfusion)] at h_sound_0
              obtain ⟨vs₀, h_atSpace₀, h_basis₀⟩ := denotBasis_atSpace_ok h_sound_0
              simp only [denotBasis, Basis.sof] at h_atSpace₀
              rw [ExpectedSpace.ofBasis_tprod]
              show SoundOfDenot (.vecs (denotSpace σ (Basis.sof (Basis.tprod _ _))))
                  (denotBasis σ (Basis.tprod _ _))
              simp only [Basis.sof, denotSpace, denotBasis,
                         BasisDenot.atSpace_frame]
              show SoundOfDenot (.vecs (HSpace.tprod _ HSpace.empty)) (.vecs _ _)
              unfold SoundOfDenot
              refine ⟨rfl, ?_⟩
              rw [h_atSpace₀]
              exact IsListBasis.tprod h_basis₀ isListBasis_empty)
      | frame b₀₀ b₀₁ =>
          cases b₁ with
          | empty | one | dual _ | dsum _ _ | tprod _ _
          | proj _ _ _ | image _ | terms _ _ _ =>
              rw [ExpectedSpace.ofBasis_vecs_of_not_frame (by intros; exact Basis.noConfusion)] at h_sound_1
              obtain ⟨vs₁, h_atSpace₁, h_basis₁⟩ := denotBasis_atSpace_ok h_sound_1
              simp only [denotBasis, Basis.sof] at h_atSpace₁
              rw [ExpectedSpace.ofBasis_tprod]
              show SoundOfDenot (.vecs (denotSpace σ (Basis.sof (Basis.tprod _ _))))
                  (denotBasis σ (Basis.tprod _ _))
              simp only [Basis.sof, denotSpace, denotBasis,
                         BasisDenot.atSpace_frame]
              show SoundOfDenot (.vecs (HSpace.tprod HSpace.empty _)) (.vecs _ _)
              unfold SoundOfDenot
              refine ⟨rfl, ?_⟩
              rw [h_atSpace₁]
              exact IsListBasis.tprod isListBasis_empty h_basis₁
          | frame b₁₀ b₁₁ =>
              rw [ExpectedSpace.ofBasis_tprod]
              show SoundOfDenot (.vecs (denotSpace σ (Basis.sof (Basis.tprod _ _))))
                  (denotBasis σ (Basis.tprod _ _))
              simp only [Basis.sof, denotSpace, denotBasis,
                         BasisDenot.atSpace_frame]
              show SoundOfDenot (.vecs (HSpace.tprod HSpace.empty HSpace.empty))
                                (.vecs _ _)
              unfold SoundOfDenot
              refine ⟨rfl, ?_⟩
              exact IsListBasis.tprod isListBasis_empty isListBasis_empty
  | proj s b₀ b₁ =>
      -- The proved FSV properties establish this case. `BasisValid`'s
      -- `.proj` clause (`Basis.BasisValid_proj` in `Basis.lean`)
      -- forces `s ∈ {.ker, .coker, .img, .coimg}` — any other shape
      -- makes the `BasisValid` premise `False`. We case-split on `s`
      -- and dispatch each FFS shape to its per-shape obligation
      -- (`denotBasis_proj_{ker,coker,img,coimg}_isBasis` above), which
      -- in turn consume the FSV contract through the
      -- `IsListBasis.of_fsv_contract` bridge in `BasisSoundness.lean`.
      --
      -- `ExpectedSpace.ofBasis σ (.proj s _ _) = .vecs (denotSpace σ s)`
      -- (`.proj` is not a frame), so the goal rewrites cleanly.
      rw [ExpectedSpace.ofBasis_vecs_of_not_frame
            (by intros; exact Basis.noConfusion)]
      cases s with
      | ker s₀ s₁ e =>
          exact denotBasis_proj_ker_isBasis σ ε s₀ s₁ e b₀ b₁ hb _hσ
      | coker s₀ s₁ e =>
          exact denotBasis_proj_coker_isBasis σ ε s₀ s₁ e b₀ b₁ hb _hσ
      | img s₀ s₁ e =>
          exact denotBasis_proj_img_isBasis σ ε s₀ s₁ e b₀ b₁ hb _hσ
      | coimg s₀ s₁ e =>
          exact denotBasis_proj_coimg_isBasis σ ε s₀ s₁ e b₀ b₁ hb _hσ
      -- All other shapes make `BasisValid` `False`; absurd via `hb`.
      | empty => nomatch hb
      | real => nomatch hb
      | dual _ => nomatch hb
      | dsum _ _ => nomatch hb
      | tprod _ _ => nomatch hb
  | image b =>

      obtain ⟨hb_inner, s₀, s₁, e, hsof, _he⟩ := hb.image_inv
      -- `b ≠ .frame ...` since Basis.sof (.frame _ _) = .empty.
      have h_b_not_frame : ∀ b₀ b₁, b ≠ .frame b₀ b₁ := by
        intro b₀ b₁ heq
        rw [heq] at hsof
        simp [Basis.sof] at hsof
      have h_sound_b := denotBasis_isBasis σ ε b hb_inner _hctx _hσ
      rw [ExpectedSpace.ofBasis_vecs_of_not_frame h_b_not_frame] at h_sound_b
      obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound_b
      -- vsList : List (denotSpace σ (Basis.sof b)).carrier.
      -- Local abbreviations.
      rw [ExpectedSpace.ofBasis_vecs_of_not_frame
            (by intros; exact Basis.noConfusion)]
      let V₀ := denotSpace σ s₀
      let V₁ := denotSpace σ s₁
      let f : V₀.carrier →ₗ[ℝ] V₁.carrier := (denotTerm σ e).asLinMap V₀ V₁
      -- Basis.sof (.image b) = .img s₀ s₁ e via hsof.
      have h_sof_image : Basis.sof (Basis.image b) = .img s₀ s₁ e := by
        simp only [Basis.sof, hsof]

      revert h_basis h_atSpace
      -- vsList depends on Basis.sof b; we abstract it.
      revert vsList

      rw [hsof]

      intro vsList h_atSpace h_basis

      have h_denot :
          denotBasis σ (Basis.image b) =
            .vecs (HSpace.ofSubmodule V₁ (LinearMap.range f))
              (vsList.map fun w =>
                (⟨f (Subtype.val w), LinearMap.mem_range_self f _⟩ :
                   (HSpace.ofSubmodule V₁ (LinearMap.range f)).carrier)) := by
        show denotBasis σ (Basis.image b) = _
        unfold denotBasis
        split
        · rename_i s₀' s₁' e' h_match_sof
          -- h_match_sof : Basis.sof b = .coker s₀' s₁' e'.
          -- hsof : Basis.sof b = .coker s₀ s₁ e.
          have h_eq : (Space.coker s₀ s₁ e) = (Space.coker s₀' s₁' e') :=
            hsof.symm.trans h_match_sof
          injection h_eq with h_s₀ h_s₁ h_e
          subst h_s₀
          subst h_s₁
          subst h_e
          -- Goal: BasisDenot.vecs (V₁..range f) (List.map _ (atSpace V_coker (denotBasis σ b)))
          --     = BasisDenot.vecs (V₁..range f) (List.map _ vsList)
          -- where V_coker definitionally = denotSpace σ (.coker s₀ s₁ e).
          -- h_atSpace : atSpace (denotSpace σ (.coker s₀ s₁ e)) (denotBasis σ b) = vsList
          -- The two are definitionally the same atSpace; rfl after rw.
          show BasisDenot.vecs _ (List.map _
                (BasisDenot.atSpace (denotSpace σ (Space.coker s₀ s₁ e)) (denotBasis σ b)))
              = BasisDenot.vecs _ (List.map _ vsList)
          rw [h_atSpace]
        · rename_i h_neg
          exfalso
          exact h_neg s₀ s₁ e hsof
      rw [h_denot]
      show ∃ h : HSpace.ofSubmodule V₁ (LinearMap.range f)
                = denotSpace σ (Basis.image b).sof,
              IsListBasis (denotSpace σ (Basis.image b).sof)
                (h ▸ vsList.map fun w =>
                  (⟨f (Subtype.val w), LinearMap.mem_range_self f _⟩ :
                      (HSpace.ofSubmodule V₁ (LinearMap.range f)).carrier))
      refine ⟨?_, ?_⟩
      · rw [h_sof_image]; rfl
      · -- After the HSpace.eq cast (rfl), apply IsListBasis.image_of_inj_surj.
        convert IsListBasis.image_of_inj_surj f h_basis using 1
        · rw [h_sof_image]; rfl
        · -- HEq goal: (h ▸ L) ≍ L for L = List.map _ vsList.
          -- The cast `▸` is over a propositional eq witness; cast through
          -- both sides.
          simp
  | terms s es b =>
      -- Use the proved independence and span properties of `HSpace.lexInd`.
      -- The `.terms s es b` denotation is
      --   `.vecs V (V.lexInd (vs_terms ++ vs_back))`
      -- where `V = denotSpace σ s`, `vs_terms = es.map (atSpace V ∘ denotTerm σ)`,
      -- and `vs_back = (denotBasis σ b).atSpace V`.
      --
      -- Soundness reduces to:
      --   * `lexInd_linearly_independent`: the output list is LI.
      --   * `lexInd_span_eq`: span of output = span of input.
      --   * IH on `b`: vs_back is a basis of V (so spans ⊤).
      -- Hence span of input = span(vs_terms) ⊔ span(vs_back) ⊇ ⊤, so = ⊤.
      --
      -- `b` may take any constructor shape; we case-split to match the
      -- structure used by the `.dual` case (each sub-case threads the
      -- IH through `denotBasis_atSpace_ok` to extract `vsList`).
      -- The `.frame` sub-case is degenerate (Basis.sof (.frame _) = .empty,
      -- so V = HSpace.empty and lexInd produces `[]`).
      obtain ⟨hb_valid, h_sof, _hsval, _hes⟩ := hb.terms_inv
      -- Helper: build the IsListBasis witness from an extracted vsList
      -- and the LexInd interface obligations. Stated for an arbitrary
      -- `V : HSpace` so it composes cleanly across all sub-cases.
      have key : ∀ (V : HSpace) (vsList : List V.carrier)
          (extra_terms : List Term),
          IsListBasis V vsList →
          IsListBasis V
            (V.lexInd
              (extra_terms.map (fun e => (denotTerm σ e).atSpace V)
                ++ vsList)) := by
        intro V vsList extra_terms h_basis_vs
        refine ⟨?_, ?_⟩
        · exact HSpace.lexInd_linearly_independent _ _
        · rw [HSpace.lexInd_span_eq]
          rw [← HSpace.mem_setOf_eq_range_get]
          obtain ⟨_h_li, h_span⟩ := h_basis_vs
          rw [eq_top_iff]
          intro x _
          have h_vs_span : Submodule.span ℝ {w | w ∈ vsList} = ⊤ := by
            rw [HSpace.mem_setOf_eq_range_get]
            exact h_span
          have h_x_in_vs : x ∈ Submodule.span ℝ {w | w ∈ vsList} := by
            rw [h_vs_span]; trivial
          have h_sub : Submodule.span ℝ {w | w ∈ vsList} ≤
              Submodule.span ℝ {w | w ∈
                extra_terms.map (fun e => (denotTerm σ e).atSpace V) ++ vsList} := by
            apply Submodule.span_mono
            intro y hy
            show y ∈ extra_terms.map (fun e => (denotTerm σ e).atSpace V) ++ vsList
            rw [List.mem_append]; exact Or.inr hy
          exact h_sub h_x_in_vs

      subst h_sof

      cases b with
      | empty =>
          have h_sound := denotBasis_isBasis σ ε Basis.empty hb_valid _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          -- After `subst h_sof`, s = Basis.empty.sof.
          have h_denot :
              denotBasis σ (Basis.terms Basis.empty.sof es Basis.empty) =
                .vecs (denotSpace σ Basis.empty.sof)
                  ((denotSpace σ Basis.empty.sof).lexInd
                    (es.map (fun e => (denotTerm σ e).atSpace (denotSpace σ Basis.empty.sof))
                      ++ vsList)) := by
            show denotBasis σ _ = _
            unfold denotBasis
            simp only []
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : denotSpace σ Basis.empty.sof
                    = denotSpace σ (Basis.terms Basis.empty.sof es Basis.empty).sof,
              IsListBasis _ _
          exact ⟨rfl, key _ vsList es h_basis⟩
      | one =>
          have h_sound := denotBasis_isBasis σ ε Basis.one hb_valid _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.terms Basis.one.sof es Basis.one) =
                .vecs (denotSpace σ Basis.one.sof)
                  ((denotSpace σ Basis.one.sof).lexInd
                    (es.map (fun e => (denotTerm σ e).atSpace (denotSpace σ Basis.one.sof))
                      ++ vsList)) := by
            show denotBasis σ _ = _
            unfold denotBasis
            simp only []
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : denotSpace σ Basis.one.sof
                    = denotSpace σ (Basis.terms Basis.one.sof es Basis.one).sof,
              IsListBasis _ _
          exact ⟨rfl, key _ vsList es h_basis⟩
      | dual b' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.dual b') hb_valid _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.terms (Basis.dual b').sof es (Basis.dual b')) =
                .vecs (denotSpace σ (Basis.dual b').sof)
                  ((denotSpace σ (Basis.dual b').sof).lexInd
                    (es.map (fun e =>
                        (denotTerm σ e).atSpace (denotSpace σ (Basis.dual b').sof))
                      ++ vsList)) := by
            show denotBasis σ _ = _
            unfold denotBasis
            simp only []
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : denotSpace σ (Basis.dual b').sof
                    = denotSpace σ (Basis.terms (Basis.dual b').sof es (Basis.dual b')).sof,
              IsListBasis _ _
          exact ⟨rfl, key _ vsList es h_basis⟩
      | dsum b₀' b₁' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.dsum b₀' b₁') hb_valid _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.terms (Basis.dsum b₀' b₁').sof es (Basis.dsum b₀' b₁')) =
                .vecs (denotSpace σ (Basis.dsum b₀' b₁').sof)
                  ((denotSpace σ (Basis.dsum b₀' b₁').sof).lexInd
                    (es.map (fun e =>
                        (denotTerm σ e).atSpace (denotSpace σ (Basis.dsum b₀' b₁').sof))
                      ++ vsList)) := by
            show denotBasis σ _ = _
            unfold denotBasis
            simp only []
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : denotSpace σ (Basis.dsum b₀' b₁').sof
                    = denotSpace σ
                        (Basis.terms (Basis.dsum b₀' b₁').sof es (Basis.dsum b₀' b₁')).sof,
              IsListBasis _ _
          exact ⟨rfl, key _ vsList es h_basis⟩
      | tprod b₀' b₁' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.tprod b₀' b₁') hb_valid _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.terms (Basis.tprod b₀' b₁').sof es (Basis.tprod b₀' b₁')) =
                .vecs (denotSpace σ (Basis.tprod b₀' b₁').sof)
                  ((denotSpace σ (Basis.tprod b₀' b₁').sof).lexInd
                    (es.map (fun e =>
                        (denotTerm σ e).atSpace (denotSpace σ (Basis.tprod b₀' b₁').sof))
                      ++ vsList)) := by
            show denotBasis σ _ = _
            unfold denotBasis
            simp only []
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : denotSpace σ (Basis.tprod b₀' b₁').sof
                    = denotSpace σ
                        (Basis.terms (Basis.tprod b₀' b₁').sof es (Basis.tprod b₀' b₁')).sof,
              IsListBasis _ _
          exact ⟨rfl, key _ vsList es h_basis⟩
      | proj s' b₀' b₁' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.proj s' b₀' b₁') hb_valid _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ
                (Basis.terms (Basis.proj s' b₀' b₁').sof es (Basis.proj s' b₀' b₁')) =
                .vecs (denotSpace σ (Basis.proj s' b₀' b₁').sof)
                  ((denotSpace σ (Basis.proj s' b₀' b₁').sof).lexInd
                    (es.map (fun e =>
                        (denotTerm σ e).atSpace (denotSpace σ (Basis.proj s' b₀' b₁').sof))
                      ++ vsList)) := by
            show denotBasis σ _ = _
            unfold denotBasis
            simp only []
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : denotSpace σ (Basis.proj s' b₀' b₁').sof
                    = denotSpace σ
                        (Basis.terms (Basis.proj s' b₀' b₁').sof es
                          (Basis.proj s' b₀' b₁')).sof,
              IsListBasis _ _
          exact ⟨rfl, key _ vsList es h_basis⟩
      | image b' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.image b') hb_valid _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.terms (Basis.image b').sof es (Basis.image b')) =
                .vecs (denotSpace σ (Basis.image b').sof)
                  ((denotSpace σ (Basis.image b').sof).lexInd
                    (es.map (fun e =>
                        (denotTerm σ e).atSpace (denotSpace σ (Basis.image b').sof))
                      ++ vsList)) := by
            show denotBasis σ _ = _
            unfold denotBasis
            simp only []
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : denotSpace σ (Basis.image b').sof
                    = denotSpace σ (Basis.terms (Basis.image b').sof es (Basis.image b')).sof,
              IsListBasis _ _
          exact ⟨rfl, key _ vsList es h_basis⟩
      | terms s'' es'' b'' =>
          have h_sound := denotBasis_isBasis σ ε (Basis.terms s'' es'' b'') hb_valid _hctx _hσ
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)] at h_sound
          obtain ⟨vsList, h_atSpace, h_basis⟩ := denotBasis_atSpace_ok h_sound
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ
                (Basis.terms (Basis.terms s'' es'' b'').sof es (Basis.terms s'' es'' b'')) =
                .vecs (denotSpace σ (Basis.terms s'' es'' b'').sof)
                  ((denotSpace σ (Basis.terms s'' es'' b'').sof).lexInd
                    (es.map (fun e =>
                        (denotTerm σ e).atSpace (denotSpace σ (Basis.terms s'' es'' b'').sof))
                      ++ vsList)) := by
            show denotBasis σ _ = _
            unfold denotBasis
            simp only []
            rw [h_atSpace]
          rw [h_denot]
          show ∃ h : denotSpace σ (Basis.terms s'' es'' b'').sof
                    = denotSpace σ
                        (Basis.terms (Basis.terms s'' es'' b'').sof es
                          (Basis.terms s'' es'' b'')).sof,
              IsListBasis _ _
          exact ⟨rfl, key _ vsList es h_basis⟩
      | frame b₀ b₁ =>

          show SoundOfDenot (ExpectedSpace.ofBasis σ
            (Basis.terms (Basis.frame b₀ b₁).sof es (Basis.frame b₀ b₁))) _
          rw [ExpectedSpace.ofBasis_vecs_of_not_frame
                (by intros; exact Basis.noConfusion)]
          have h_denot :
              denotBasis σ (Basis.terms (Basis.frame b₀ b₁).sof es
                (Basis.frame b₀ b₁)) =
                .vecs HSpace.empty
                  (HSpace.empty.lexInd
                    (es.map (fun e => (denotTerm σ e).atSpace HSpace.empty)
                      ++ [])) := by
            -- denotBasis σ (.terms s es (.frame _)) =
            --   .vecs V (V.lexInd (vs_terms ++ atSpace V (denotBasis σ (.frame _)))).
            -- denotBasis σ (.frame _) is .frame-shaped, so atSpace gives [].
            show denotBasis σ _ = _
            unfold denotBasis
            simp only [Basis.sof, denotSpace]
            congr 1
            congr 1
            -- vs_terms ++ atSpace ... = vs_terms ++ [].
            -- The atSpace on `denotBasis σ (.frame ...)` reduces to [] because
            -- unfolding `denotBasis` on `.frame` exposes the `.frame T f` shape,
            -- on which `atSpace V (.frame T f) = []` (BasisDenot.atSpace_frame, rfl).
            -- However `simp` may not auto-reduce because `denotBasis σ (.frame ...)`
            -- is opaque to it. We explicitly unfold here.
            show es.map (fun e => DVal.atSpace HSpace.empty (denotTerm σ e)) ++
                  BasisDenot.atSpace HSpace.empty (denotBasis σ (Basis.frame b₀ b₁))
                = es.map (fun e => DVal.atSpace HSpace.empty (denotTerm σ e)) ++ []
            congr 1
            show BasisDenot.atSpace HSpace.empty (denotBasis σ (Basis.frame b₀ b₁)) = []
            -- Reduce by unfolding denotBasis on .frame, which exposes .frame T f shape.
            unfold denotBasis
            rfl
          rw [h_denot]
          -- After h_denot, the goal is:
          -- SoundOfDenot (.vecs (denotSpace σ (Basis.terms (Basis.frame ...).sof es _).sof))
          --              (.vecs HSpace.empty (HSpace.empty.lexInd (... ++ []))).
          -- The expected space simplifies: (Basis.terms (.frame ...).sof es (.frame ...)).sof
          -- = Basis.sof (.frame ...) = .empty, and denotSpace σ .empty = HSpace.empty.
          show ∃ h : HSpace.empty = denotSpace σ _, IsListBasis _ _
          refine ⟨rfl, ?_⟩
          -- Goal: IsListBasis HSpace.empty (HSpace.empty.lexInd (... ++ [])).
          -- HSpace.empty.carrier = PUnit (subsingleton); all entries equal 0.
          -- The greedy lexInd filter drops every vector (since 0 ∈ ⊥ = span ∅).
          -- Result: []. Hence isListBasis_empty.
          have h_lexInd_empty : ∀ vs : List HSpace.empty.carrier,
              HSpace.empty.lexInd vs = [] := by
            intro vs
            have h_li := HSpace.lexInd_linearly_independent HSpace.empty vs
            by_contra h_ne
            have h_len : 0 < (HSpace.empty.lexInd vs).length :=
              List.length_pos_iff.mpr h_ne
            have h0 : (HSpace.empty.lexInd vs).get ⟨0, h_len⟩ = 0 :=
              Subsingleton.elim _ _
            have h_ne0 : (HSpace.empty.lexInd vs).get ⟨0, h_len⟩ ≠ 0 :=
              h_li.ne_zero ⟨0, h_len⟩
            exact h_ne0 h0
          rw [h_lexInd_empty]
          exact isListBasis_empty
  | frame b₀ b₁ =>
      -- Well-founded LN frame case. Pick an opening name satisfying the cofinite validity
      -- premise and all environment-freshness requirements, recurse on the opened body (whose
      -- `Basis.size` is that of the strict subterm), then transport its denotation back to the
      -- canonical name chosen by `denotBasis` using `denotBasisOpenIrrel`.
      obtain ⟨hb₀, ⟨L, hbody⟩, k₀, k₁, ⟨hpi⟩⟩ := hb.frame_inv
      cases hpi with
      | piTy Lty hτ₀ hτ₁ =>
          obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
            (L ∪ ε.keys ∪ Ty.fv (Basis.tof b₀) ∪ Basis.fv b₁)
          simp only [Finset.mem_union, not_or] at hz
          rcases hz with ⟨⟨⟨hzL, hzεk⟩, hzτ₀⟩, hzb₁⟩
          have hzε : z ∉ ε := fun hzmem => hzεk (Finmap.mem_keys.mpr hzmem)
          have hctxz : CtxWF ∅ (Finmap.insert z (Basis.tof b₀) ε) :=
            _hctx.insert_nl Finmap.notMem_empty hzε hτ₀.fv_closure
          simp only [ExpectedSpace.ofBasis, denotBasis, SoundOfDenot]
          constructor
          · intro y
            have henvz : EnvWF
                (σ.bind z ((denotTy σ (Basis.tof b₀)).embed y)) ∅
                (Finmap.insert z (Basis.tof b₀) ε) :=
              _hσ.bind_nl _hctx Finmap.notMem_empty hzε hzτ₀ y
            have hsoundz := denotBasis_isBasis
              (σ.bind z ((denotTy σ (Basis.tof b₀)).embed y))
              (Finmap.insert z (Basis.tof b₀) ε) (Basis.openVar z b₁)
              (hbody z hzL) hctxz henvz
            rw [denotBasisOpenIrrel σ b₁ (Basis.freshFor b₁) z
              ((denotTy σ (Basis.tof b₀)).embed y) (Basis.freshFor_spec b₁) hzb₁]
            exact SoundOfDenot.to_ofDenot _ _ hsoundz
          · trivial
termination_by Basis.size b
decreasing_by
  all_goals simp_all [Basis.size, Basis.openVar, Basis.size_openVar] <;> omega

/-- Exact vector-list projection consumed by operational adequacy. Frame denotations have
`sof = empty` and expose the empty list through `atSpace`; every other constructor projects its
list-basis witness from `denotBasis_isBasis`. -/
theorem denotBasis_atSpace_isListBasis (σ : DEnv) (ε : NLCtx) (b : Basis)
    (hb : Basis.BasisValid ε b) (hctx : CtxWF ∅ ε) (hσ : EnvWF σ ∅ ε) :
    IsListBasis (denotSpace σ (Basis.sof b))
      ((denotBasis σ b).atSpace (denotSpace σ (Basis.sof b))) := by
  cases b with
  | frame b₀ b₁ =>
      simpa [Basis.sof, denotSpace, denotBasis, BasisDenot.atSpace_frame] using
        isListBasis_empty
  | empty | one | dual | dsum | tprod | proj | image | terms =>
      have hs := denotBasis_isBasis σ ε _ hb hctx hσ
      rw [ExpectedSpace.ofBasis_vecs_of_not_frame (by intros; exact Basis.noConfusion)] at hs
      obtain ⟨vs, hat, hbasis⟩ := denotBasis_atSpace_ok hs
      rw [hat]
      exact hbasis

/-- **Tier-2 base case: `.empty`.** The empty list at `HSpace.empty`
    is orthonormal under `HSpace.empty.innerProduct` — vacuously,
    since `Fin 0` is empty. This is the concrete instantiation of the
    `.empty` case of `denotBasis_orthonormal`; the connection comes
    via `denotBasis σ .empty = .vecs HSpace.empty []` and
    `BasisDenot.atSpace HSpace.empty (.vecs HSpace.empty []) = []`. -/
theorem denotBasis_orthonormal_empty :
    ∀ i j : Fin ([] : List HSpace.empty.carrier).length,
      HSpace.empty.innerProduct (([] : List HSpace.empty.carrier).get i)
        (([] : List HSpace.empty.carrier).get j) = if i = j then 1 else 0 := by
  intro i _; exact i.elim0

/-- **Tier-2 base case: `.one`.** The singleton list `[1]` at
    `HSpace.real` is orthonormal under `HSpace.real.innerProduct =
    LinearMap.mul ℝ ℝ`: the only index is `0`, and `1 * 1 = 1`. This
    is the concrete instantiation of the `.one` case of
    `denotBasis_orthonormal`; the connection comes via `denotBasis σ
    .one = .vecs HSpace.real [1]` and
    `BasisDenot.atSpace HSpace.real (.vecs HSpace.real [1]) = [1]`
    (the latter is `BasisDenot.atSpace_vecs_self`). -/
theorem denotBasis_orthonormal_one :
    ∀ i j : Fin ([(1 : ℝ)] : List HSpace.real.carrier).length,
      HSpace.real.innerProduct
          (([(1 : ℝ)] : List HSpace.real.carrier).get i)
          (([(1 : ℝ)] : List HSpace.real.carrier).get j) =
        if i = j then 1 else 0 := by
  intro i j
  -- vs.length = 1, so the only inhabitants of Fin 1 are ⟨0, _⟩.
  -- Use Fin.fin_one_eq_zero to reduce both to 0.
  fin_cases i
  fin_cases j
  -- Goal: HSpace.real.innerProduct (1:ℝ) (1:ℝ) = if (⟨0,_⟩ = ⟨0,_⟩) then 1 else 0
  simp [HSpace.real]

theorem denotBasis_orthonormal_dsum (σ : DEnv) (b₀ b₁ : Basis)
    (vs₀ : List (denotSpace σ (Basis.sof b₀)).carrier)
    (vs₁ : List (denotSpace σ (Basis.sof b₁)).carrier)
    (h_atSpace₀ : BasisDenot.atSpace
        (denotSpace σ (Basis.sof b₀)) (denotBasis σ b₀) = vs₀)
    (h_atSpace₁ : BasisDenot.atSpace
        (denotSpace σ (Basis.sof b₁)) (denotBasis σ b₁) = vs₁)
    (h_orth₀ : ∀ i j : Fin vs₀.length,
        (denotSpace σ (Basis.sof b₀)).innerProduct
          (vs₀.get i) (vs₀.get j) = if i = j then 1 else 0)
    (h_orth₁ : ∀ i j : Fin vs₁.length,
        (denotSpace σ (Basis.sof b₁)).innerProduct
          (vs₁.get i) (vs₁.get j) = if i = j then 1 else 0) :
    let V := denotSpace σ (Basis.sof (.dsum b₀ b₁))
    let vs := BasisDenot.atSpace V (denotBasis σ (.dsum b₀ b₁))
    ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0 := by

  have h_denot :
      denotBasis σ (.dsum b₀ b₁) =
        .vecs (HSpace.dsum (denotSpace σ (Basis.sof b₀))
                            (denotSpace σ (Basis.sof b₁)))
              (HSpace.dsumOfLists _ _ vs₀ vs₁) := by
    show denotBasis σ _ = _
    unfold denotBasis
    simp only []
    rw [h_atSpace₀, h_atSpace₁]
  -- Step 2: unfold the let-bindings in the goal.
  show ∀ i j : Fin (BasisDenot.atSpace
                      (denotSpace σ (Basis.sof (.dsum b₀ b₁)))
                      (denotBasis σ (.dsum b₀ b₁))).length,
            (denotSpace σ (Basis.sof (.dsum b₀ b₁))).innerProduct
              ((BasisDenot.atSpace _ (denotBasis σ (.dsum b₀ b₁))).get i)
              ((BasisDenot.atSpace _ (denotBasis σ (.dsum b₀ b₁))).get j) =
            if i = j then 1 else 0
  -- Step 3: rewrite via `h_denot` to expose the .vecs form.
  rw [h_denot]
  -- The outer atSpace then reduces via atSpace_vecs_self, but the
  -- HSpace on the inside matches denotSpace σ (Basis.sof (.dsum _ _))
  -- only by rfl-definitional equality. Use `show` to bridge.
  show ∀ i j : Fin (BasisDenot.atSpace
                      (HSpace.dsum (denotSpace σ (Basis.sof b₀))
                                   (denotSpace σ (Basis.sof b₁)))
                      (.vecs (HSpace.dsum _ _)
                             (HSpace.dsumOfLists _ _ vs₀ vs₁))).length,
            (HSpace.dsum (denotSpace σ (Basis.sof b₀))
                         (denotSpace σ (Basis.sof b₁))).innerProduct
              ((BasisDenot.atSpace _ _).get i)
              ((BasisDenot.atSpace _ _).get j) =
            if i = j then 1 else 0
  rw [BasisDenot.atSpace_vecs_self]
  -- After atSpace_vecs_self, the get accesses `HSpace.dsumOfLists ... vs₀ vs₁`.
  intro i j
  exact IsListBasis.dsum_orthonormal h_orth₀ h_orth₁ i j

theorem denotBasis_orthonormal_tprod (σ : DEnv) (b₀ b₁ : Basis)
    (ih₀ : let V₀ := denotSpace σ (Basis.sof b₀)
           let vs₀ := BasisDenot.atSpace V₀ (denotBasis σ b₀)
           ∀ i j : Fin vs₀.length,
             V₀.innerProduct (vs₀.get i) (vs₀.get j) = if i = j then 1 else 0)
    (ih₁ : let V₁ := denotSpace σ (Basis.sof b₁)
           let vs₁ := BasisDenot.atSpace V₁ (denotBasis σ b₁)
           ∀ i j : Fin vs₁.length,
             V₁.innerProduct (vs₁.get i) (vs₁.get j) = if i = j then 1 else 0) :
    let V := denotSpace σ (Basis.sof (Basis.tprod b₀ b₁))
    let vs := BasisDenot.atSpace V (denotBasis σ (Basis.tprod b₀ b₁))
    ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0 := by
  -- The key reduction is `atSpace V (.vecs V (tprodOfLists ...)) =
  -- tprodOfLists ...` via `atSpace_vecs_self`. We use the more
  -- explicit `BasisDenot.atSpace_vecs_self` *equation* to bridge the
  -- `Fin (atSpace ...).length` index type.
  have h_main : ∀ i j : Fin
      (HSpace.tprodOfLists (denotSpace σ (Basis.sof b₀))
                           (denotSpace σ (Basis.sof b₁))
                           ((denotBasis σ b₀).atSpace (denotSpace σ (Basis.sof b₀)))
                           ((denotBasis σ b₁).atSpace
                               (denotSpace σ (Basis.sof b₁)))).length,
      (HSpace.tprod (denotSpace σ (Basis.sof b₀))
                    (denotSpace σ (Basis.sof b₁))).innerProduct
        ((HSpace.tprodOfLists _ _ _ _).get i)
        ((HSpace.tprodOfLists _ _ _ _).get j) =
        if i = j then 1 else 0 :=
    IsListBasis.tprod_orthonormal ih₀ ih₁
  -- The list `atSpace V (denotBasis σ (.tprod b₀ b₁))` equals
  -- `tprodOfLists V₀ V₁ vs₀ vs₁` via the `BasisDenot.atSpace` reduction.
  -- Build the bridge lemma and convert.
  -- First: `denotBasis σ (.tprod _ _) = .vecs (HSpace.tprod V₀ V₁) (tprodOfLists ...)`.
  have h_denot_eq :
      denotBasis σ (Basis.tprod b₀ b₁) =
      .vecs (HSpace.tprod (denotSpace σ (Basis.sof b₀))
                          (denotSpace σ (Basis.sof b₁)))
            (HSpace.tprodOfLists (denotSpace σ (Basis.sof b₀))
                                  (denotSpace σ (Basis.sof b₁))
                                  ((denotBasis σ b₀).atSpace
                                      (denotSpace σ (Basis.sof b₀)))
                                  ((denotBasis σ b₁).atSpace
                                      (denotSpace σ (Basis.sof b₁)))) := by
    show denotBasis σ _ = _
    simp only [denotBasis]
  -- Then: `atSpace V (.vecs V vs) = vs`.
  have h_list_eq :
      BasisDenot.atSpace
          (HSpace.tprod (denotSpace σ (Basis.sof b₀))
                        (denotSpace σ (Basis.sof b₁)))
          (denotBasis σ (Basis.tprod b₀ b₁)) =
      HSpace.tprodOfLists (denotSpace σ (Basis.sof b₀))
                           (denotSpace σ (Basis.sof b₁))
                           ((denotBasis σ b₀).atSpace (denotSpace σ (Basis.sof b₀)))
                           ((denotBasis σ b₁).atSpace
                               (denotSpace σ (Basis.sof b₁))) := by
    rw [h_denot_eq]
    exact BasisDenot.atSpace_vecs_self _ _

  have hlen : (HSpace.tprodOfLists (denotSpace σ (Basis.sof b₀))
                                    (denotSpace σ (Basis.sof b₁))
                                    ((denotBasis σ b₀).atSpace
                                        (denotSpace σ (Basis.sof b₀)))
                                    ((denotBasis σ b₁).atSpace
                                        (denotSpace σ (Basis.sof b₁)))).length =
              (BasisDenot.atSpace
                  (HSpace.tprod (denotSpace σ (Basis.sof b₀))
                                (denotSpace σ (Basis.sof b₁)))
                  (denotBasis σ (Basis.tprod b₀ b₁))).length :=
    congrArg List.length h_list_eq.symm
  -- Bridge i, j via the length equality.
  intro V vs i j
  have hlen : vs.length =
              (HSpace.tprodOfLists
                  (denotSpace σ (Basis.sof b₀))
                  (denotSpace σ (Basis.sof b₁))
                  ((denotBasis σ b₀).atSpace (denotSpace σ (Basis.sof b₀)))
                  ((denotBasis σ b₁).atSpace
                      (denotSpace σ (Basis.sof b₁)))).length :=
    congrArg List.length h_list_eq
  let i' : Fin _ := Fin.cast hlen i
  let j' : Fin _ := Fin.cast hlen j
  -- `vs.get i = (tprodOfLists ...).get i'` via the list equality.
  -- Convert both to `getElem` at the same nat index i.1; lists are equal.
  have h_get_i : vs.get i =
      (HSpace.tprodOfLists
          (denotSpace σ (Basis.sof b₀))
          (denotSpace σ (Basis.sof b₁))
          ((denotBasis σ b₀).atSpace (denotSpace σ (Basis.sof b₀)))
          ((denotBasis σ b₁).atSpace
              (denotSpace σ (Basis.sof b₁)))).get i' := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact List.getElem_of_eq h_list_eq i.isLt
  have h_get_j : vs.get j =
      (HSpace.tprodOfLists
          (denotSpace σ (Basis.sof b₀))
          (denotSpace σ (Basis.sof b₁))
          ((denotBasis σ b₀).atSpace (denotSpace σ (Basis.sof b₀)))
          ((denotBasis σ b₁).atSpace
              (denotSpace σ (Basis.sof b₁)))).get j' := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    exact List.getElem_of_eq h_list_eq j.isLt
  show (HSpace.tprod (denotSpace σ (Basis.sof b₀))
                     (denotSpace σ (Basis.sof b₁))).innerProduct
       (vs.get i) (vs.get j) = if i = j then 1 else 0
  rw [h_get_i, h_get_j]
  -- Bridge the conditional via i' = j' ↔ i = j.
  have hij_iff : (i' = j') ↔ (i = j) := by
    constructor
    · intro h
      apply Fin.ext
      exact (Fin.mk.inj h)
    · intro h; subst h; rfl
  have h_main_ij := h_main i' j'
  by_cases hij : i = j
  · subst hij
    rw [h_main_ij]
    simp [hij_iff.mpr rfl]
  · rw [h_main_ij]
    have : i' ≠ j' := fun h => hij (hij_iff.mp h)
    simp [hij, this]

private theorem stdBasis_orthonormal_dual_step (σ : DEnv) (s : Space)
    (ih : let V := denotSpace σ s
           let vs := BasisDenot.atSpace V (denotBasis σ (Basis.stdSpace s))
           ∀ i j : Fin vs.length,
             V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0) :
    let V := denotSpace σ (.dual s)
    let vs := BasisDenot.atSpace V (denotBasis σ (Basis.stdSpace (.dual s)))
    ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0 := by
  -- Step 1: introduce the underlying space and its orthonormal basis (the IH carrier).
  set V := denotSpace σ s with hV
  -- Step 2: name the inner orthonormal list.
  set vs_inner := (denotBasis σ (Basis.stdSpace s)).atSpace V with hvs_inner
  -- Step 3: `denotBasis σ (Basis.stdSpace (.dual s)) = .vecs (HSpace.dual V) (V.dualOfList vs_inner)`.
  have h_denot_eq :
      denotBasis σ (Basis.stdSpace (.dual s))
        = BasisDenot.vecs (HSpace.dual V) (V.dualOfList vs_inner) := by
    -- `Basis.stdSpace (.dual s) = .dual (Basis.stdSpace s)` and the `.dual`
    -- arm of `denotBasis` builds `.vecs (HSpace.dual V') (V'.dualOfList _)`
    -- with `V' = denotSpace σ (Basis.sof (Basis.stdSpace s))`.
    -- `Basis.sof_stdSpace s` simplifies the inner `V'` to `denotSpace σ s = V`.
    have h_sof : Basis.sof (Basis.stdSpace s) = s := Basis.sof_stdSpace s
    show denotBasis σ (.dual (Basis.stdSpace s))
          = BasisDenot.vecs (HSpace.dual V) (V.dualOfList vs_inner)
    unfold denotBasis

    rw [h_sof]
  -- Step 4: `denotSpace σ (.dual s) = HSpace.dual V` (definitional).
  -- Step 5: After let-evaluation + h_denot_eq, the conclusion list becomes
  -- `BasisDenot.atSpace (HSpace.dual V) (.vecs (HSpace.dual V) (V.dualOfList vs_inner))`,
  -- which reduces to `V.dualOfList vs_inner` via `atSpace_vecs_self`.
  show ∀ i j : Fin (BasisDenot.atSpace (HSpace.dual V)
                    (denotBasis σ (Basis.stdSpace (.dual s)))).length,
      (HSpace.dual V).innerProduct
        ((BasisDenot.atSpace (HSpace.dual V)
            (denotBasis σ (Basis.stdSpace (.dual s)))).get i)
        ((BasisDenot.atSpace (HSpace.dual V)
            (denotBasis σ (Basis.stdSpace (.dual s)))).get j) =
        if i = j then 1 else 0
  rw [h_denot_eq, BasisDenot.atSpace_vecs_self]
  -- Step 6: Apply the dual orthonormality helper, with `vs_inner` orthonormal by IH.
  exact HSpace.dualOfList_orthonormal_of_orthonormal V vs_inner ih

private theorem stdBasis_orthonormal_dsum_step (σ : DEnv) (s₀ s₁ : Space)
    (ih₀ : let V₀ := denotSpace σ s₀
           let vs₀ := BasisDenot.atSpace V₀ (denotBasis σ (Basis.stdSpace s₀))
           ∀ i j : Fin vs₀.length,
             V₀.innerProduct (vs₀.get i) (vs₀.get j) = if i = j then 1 else 0)
    (ih₁ : let V₁ := denotSpace σ s₁
           let vs₁ := BasisDenot.atSpace V₁ (denotBasis σ (Basis.stdSpace s₁))
           ∀ i j : Fin vs₁.length,
             V₁.innerProduct (vs₁.get i) (vs₁.get j) = if i = j then 1 else 0) :
    let V := denotSpace σ (.dsum s₀ s₁)
    let vs := BasisDenot.atSpace V (denotBasis σ (Basis.stdSpace (.dsum s₀ s₁)))
    ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0 := by
  -- `Basis.stdSpace (.dsum s₀ s₁) = .dsum (Basis.stdSpace s₀) (Basis.stdSpace s₁)` is rfl.
  set b₀ : Basis := Basis.stdSpace s₀ with hb₀
  set b₁ : Basis := Basis.stdSpace s₁ with hb₁
  -- After `set`, the goal mentions `Basis.stdSpace (.dsum s₀ s₁)` (not unfolded).
  -- Rewrite the goal to use `.dsum b₀ b₁` via the structural identity.
  show let V := denotSpace σ (.dsum s₀ s₁)
       let vs := BasisDenot.atSpace V (denotBasis σ (.dsum b₀ b₁))
       ∀ i j : Fin vs.length,
         V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0
  have hsof₀ : Basis.sof b₀ = s₀ := by rw [hb₀]; exact Basis.sof_stdSpace s₀
  have hsof₁ : Basis.sof b₁ = s₁ := by rw [hb₁]; exact Basis.sof_stdSpace s₁
  clear_value b₀ b₁
  subst hsof₀
  subst hsof₁
  -- After subst, the goal's `denotSpace σ (.dsum s₀ s₁)` becomes
  -- `denotSpace σ (.dsum (Basis.sof b₀) (Basis.sof b₁))`, which matches
  -- the conclusion shape of `denotBasis_orthonormal_dsum`.
  exact denotBasis_orthonormal_dsum σ b₀ b₁
    (vs₀ := (denotBasis σ b₀).atSpace (denotSpace σ (Basis.sof b₀)))
    (vs₁ := (denotBasis σ b₁).atSpace (denotSpace σ (Basis.sof b₁)))
    (h_atSpace₀ := rfl)
    (h_atSpace₁ := rfl)
    (h_orth₀ := ih₀)
    (h_orth₁ := ih₁)

/-- `.tprod` per-case bridge for `stdBasis_orthonormal`. -/
private theorem stdBasis_orthonormal_tprod_step (σ : DEnv) (s₀ s₁ : Space)
    (ih₀ : let V₀ := denotSpace σ s₀
           let vs₀ := BasisDenot.atSpace V₀ (denotBasis σ (Basis.stdSpace s₀))
           ∀ i j : Fin vs₀.length,
             V₀.innerProduct (vs₀.get i) (vs₀.get j) = if i = j then 1 else 0)
    (ih₁ : let V₁ := denotSpace σ s₁
           let vs₁ := BasisDenot.atSpace V₁ (denotBasis σ (Basis.stdSpace s₁))
           ∀ i j : Fin vs₁.length,
             V₁.innerProduct (vs₁.get i) (vs₁.get j) = if i = j then 1 else 0) :
    let V := denotSpace σ (.tprod s₀ s₁)
    let vs := BasisDenot.atSpace V (denotBasis σ (Basis.stdSpace (.tprod s₀ s₁)))
    ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0 := by
  set b₀ : Basis := Basis.stdSpace s₀ with hb₀
  set b₁ : Basis := Basis.stdSpace s₁ with hb₁
  show let V := denotSpace σ (.tprod s₀ s₁)
       let vs := BasisDenot.atSpace V (denotBasis σ (.tprod b₀ b₁))
       ∀ i j : Fin vs.length,
         V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0
  have hsof₀ : Basis.sof b₀ = s₀ := by rw [hb₀]; exact Basis.sof_stdSpace s₀
  have hsof₁ : Basis.sof b₁ = s₁ := by rw [hb₁]; exact Basis.sof_stdSpace s₁
  clear_value b₀ b₁
  subst hsof₀
  subst hsof₁
  exact denotBasis_orthonormal_tprod σ b₀ b₁ ih₀ ih₁

/-! ### FSV-shape orthonormality helpers (Tier-2 for `.ker / .coker / .img / .coimg`).

For the four FFS-shaped spaces, `Basis.stdSpace` unfolds to a `.proj`,
whose `denotBasis` produces `.vecs (HSpace.ofSubmodule V K)
(liftToSubmodule K raw)` where `raw` is the FSV output. The IP on
`HSpace.ofSubmodule V K` is `LinearMap.BilinForm.restrict V.IP K`,
which evaluates pointwise as `V.IP x.val y.val`. Combined with
`HSpace.liftToSubmodule_get_val_of_subset` and FSV's orthonormality
contract (`fsv*_orthonormal`), the orthonormality of the lifted list
follows. -/

/-- Reduction equation: `denotBasis σ (Basis.stdSpace (.ker s₀ s₁ e))`
    unfolds to a `.vecs`-shaped denotation at `HSpace.ofSubmodule V₀ K`
    with the FSV-left list lifted into the kernel submodule. -/
theorem denotBasis_stdSpace_ker (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    denotBasis σ (Basis.stdSpace (.ker s₀ s₁ e)) =
      .vecs (HSpace.ofSubmodule (denotSpace σ s₀)
              (LinearMap.ker ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))))
            (HSpace.liftToSubmodule
              (LinearMap.ker ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)))
              (BasisFSV.fsvLeft (denotSpace σ s₀) (denotSpace σ s₁)
                ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
                (fun μ => decide (μ = 0))
                ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
                ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)))) := by
  simp only [Basis.stdSpace, denotBasis]

/-- Analogue for `.coker`. -/
theorem denotBasis_stdSpace_coker (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    denotBasis σ (Basis.stdSpace (.coker s₀ s₁ e)) =
      .vecs (HSpace.ofSubmodule (denotSpace σ s₀)
              (Submodule.orthRel (denotSpace σ s₀).innerProduct
                (LinearMap.ker ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)))))
            (HSpace.liftToSubmodule
              (Submodule.orthRel (denotSpace σ s₀).innerProduct
                (LinearMap.ker ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))))
              (BasisFSV.fsvLeft (denotSpace σ s₀) (denotSpace σ s₁)
                ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
                (fun μ => decide (μ ≠ 0))
                ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
                ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)))) := by
  simp only [Basis.stdSpace, denotBasis]

/-- Analogue for `.img`. -/
theorem denotBasis_stdSpace_img (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    denotBasis σ (Basis.stdSpace (.img s₀ s₁ e)) =
      .vecs (HSpace.ofSubmodule (denotSpace σ s₁)
              (LinearMap.range ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))))
            (HSpace.liftToSubmodule
              (LinearMap.range ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)))
              (BasisFSV.fsvRight (denotSpace σ s₀) (denotSpace σ s₁)
                ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
                (fun μ => decide (μ ≠ 0))
                ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
                ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)))) := by
  simp only [Basis.stdSpace, denotBasis]

/-- Analogue for `.coimg`. -/
theorem denotBasis_stdSpace_coimg (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    denotBasis σ (Basis.stdSpace (.coimg s₀ s₁ e)) =
      .vecs (HSpace.ofSubmodule (denotSpace σ s₁)
              (Submodule.orthRel (denotSpace σ s₁).innerProduct
                (LinearMap.range ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)))))
            (HSpace.liftToSubmodule
              (Submodule.orthRel (denotSpace σ s₁).innerProduct
                (LinearMap.range ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))))
              (BasisFSV.fsvRight (denotSpace σ s₀) (denotSpace σ s₁)
                ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
                (fun μ => decide (μ = 0))
                ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
                ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)))) := by
  simp only [Basis.stdSpace, denotBasis]

/-- Reduction equation for the denotSpace at `.ker` (just unfolding). -/
theorem denotSpace_ker (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    denotSpace σ (.ker s₀ s₁ e) =
      HSpace.ofSubmodule (denotSpace σ s₀)
        (LinearMap.ker ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))) :=
  rfl

theorem denotSpace_coker (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    denotSpace σ (.coker s₀ s₁ e) =
      HSpace.ofSubmodule (denotSpace σ s₀)
        (Submodule.orthRel (denotSpace σ s₀).innerProduct
          (LinearMap.ker ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)))) :=
  rfl

theorem denotSpace_img (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    denotSpace σ (.img s₀ s₁ e) =
      HSpace.ofSubmodule (denotSpace σ s₁)
        (LinearMap.range ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))) :=
  rfl

theorem denotSpace_coimg (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    denotSpace σ (.coimg s₀ s₁ e) =
      HSpace.ofSubmodule (denotSpace σ s₁)
        (Submodule.orthRel (denotSpace σ s₁).innerProduct
          (LinearMap.range ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)))) :=
  rfl

/-- **Left-side FSV-shape orthonormality.** For `.ker` and `.coker`
    shapes (both Left-side, with different `pred`s), the basis at
    `HSpace.ofSubmodule V₀ K` extracted from `Basis.stdSpace` is
    orthonormal. -/
private theorem stdBasis_orthonormal_proj_left (σ : DEnv)
    (s₀ s₁ : Space) (e : Term) (pred : ℝ → Bool)
    (K : Submodule ℝ (denotSpace σ s₀).carrier)
    (h_subset : ∀ v ∈ BasisFSV.fsvLeft (denotSpace σ s₀) (denotSpace σ s₁)
                      ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
                      pred
                      ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
                      ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)),
                v ∈ K) :
    ∀ i j : Fin (HSpace.liftToSubmodule K
                  (BasisFSV.fsvLeft (denotSpace σ s₀) (denotSpace σ s₁)
                    ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
                    pred
                    ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
                    ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)))).length,
      (HSpace.ofSubmodule (denotSpace σ s₀) K).innerProduct
        ((HSpace.liftToSubmodule K
            (BasisFSV.fsvLeft (denotSpace σ s₀) (denotSpace σ s₁)
              ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
              pred
              ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
              ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)))).get i)
        ((HSpace.liftToSubmodule K
            (BasisFSV.fsvLeft (denotSpace σ s₀) (denotSpace σ s₁)
              ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
              pred
              ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
              ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)))).get j) =
        if i = j then 1 else 0 := by
  -- Abbreviate the raw list as a local definition.
  let raw : List (denotSpace σ s₀).carrier :=
    BasisFSV.fsvLeft (denotSpace σ s₀) (denotSpace σ s₁)
      ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
      pred
      ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
      ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁))
  -- Restate the goal in terms of `raw`.
  show ∀ i j : Fin (HSpace.liftToSubmodule K raw).length,
        (HSpace.ofSubmodule (denotSpace σ s₀) K).innerProduct
          ((HSpace.liftToSubmodule K raw).get i)
          ((HSpace.liftToSubmodule K raw).get j) = if i = j then 1 else 0
  intro i j
  -- IP on ofSubmodule reduces to V₀.IP on .val (by definitional unfolding of
  -- `LinearMap.BilinForm.restrict`).
  show (LinearMap.BilinForm.restrict (denotSpace σ s₀).innerProduct K)
        ((HSpace.liftToSubmodule K raw).get i)
        ((HSpace.liftToSubmodule K raw).get j) = if i = j then 1 else 0
  show (denotSpace σ s₀).innerProduct
        ((HSpace.liftToSubmodule K raw).get i : (denotSpace σ s₀).carrier)
        ((HSpace.liftToSubmodule K raw).get j : (denotSpace σ s₀).carrier) =
        if i = j then 1 else 0
  have hvs_len : (HSpace.liftToSubmodule K raw).length = raw.length :=
    HSpace.liftToSubmodule_length_of_subset K raw h_subset
  have hi_lt : i.1 < raw.length := hvs_len ▸ i.isLt
  have hj_lt : j.1 < raw.length := hvs_len ▸ j.isLt
  -- Reduce ↑(...get i) to raw.get (cast i).
  rw [HSpace.liftToSubmodule_get_val_of_subset K raw h_subset i,
      HSpace.liftToSubmodule_get_val_of_subset K raw h_subset j]
  -- Apply FSV orthonormality at the casted indices.
  have h_orth := BasisFSV.fsvLeft_orthonormal (denotSpace σ s₀) (denotSpace σ s₁)
                  ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
                  pred
                  ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
                  ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁))
                  ⟨i.1, hi_lt⟩ ⟨j.1, hj_lt⟩
  rw [h_orth]
  -- Reduce conditional.
  by_cases hij : i = j
  · subst hij; simp
  · have hij' : (⟨i.1, hi_lt⟩ : Fin raw.length) ≠ ⟨j.1, hj_lt⟩ :=
      fun h => hij (by apply Fin.ext; exact Fin.mk.inj h)
    simp [hij, hij']

/-- **Right-side FSV-shape orthonormality.** Analogue of
    `stdBasis_orthonormal_proj_left`, for `.img` and `.coimg` shapes
    (both Right-side). -/
private theorem stdBasis_orthonormal_proj_right (σ : DEnv)
    (s₀ s₁ : Space) (e : Term) (pred : ℝ → Bool)
    (K : Submodule ℝ (denotSpace σ s₁).carrier)
    (h_subset : ∀ v ∈ BasisFSV.fsvRight (denotSpace σ s₀) (denotSpace σ s₁)
                      ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
                      pred
                      ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
                      ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)),
                v ∈ K) :
    ∀ i j : Fin (HSpace.liftToSubmodule K
                  (BasisFSV.fsvRight (denotSpace σ s₀) (denotSpace σ s₁)
                    ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
                    pred
                    ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
                    ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)))).length,
      (HSpace.ofSubmodule (denotSpace σ s₁) K).innerProduct
        ((HSpace.liftToSubmodule K
            (BasisFSV.fsvRight (denotSpace σ s₀) (denotSpace σ s₁)
              ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
              pred
              ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
              ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)))).get i)
        ((HSpace.liftToSubmodule K
            (BasisFSV.fsvRight (denotSpace σ s₀) (denotSpace σ s₁)
              ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
              pred
              ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
              ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁)))).get j) =
        if i = j then 1 else 0 := by
  let raw : List (denotSpace σ s₁).carrier :=
    BasisFSV.fsvRight (denotSpace σ s₀) (denotSpace σ s₁)
      ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
      pred
      ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
      ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁))
  show ∀ i j : Fin (HSpace.liftToSubmodule K raw).length,
        (HSpace.ofSubmodule (denotSpace σ s₁) K).innerProduct
          ((HSpace.liftToSubmodule K raw).get i)
          ((HSpace.liftToSubmodule K raw).get j) = if i = j then 1 else 0
  intro i j
  show (LinearMap.BilinForm.restrict (denotSpace σ s₁).innerProduct K)
        ((HSpace.liftToSubmodule K raw).get i)
        ((HSpace.liftToSubmodule K raw).get j) = if i = j then 1 else 0
  show (denotSpace σ s₁).innerProduct
        ((HSpace.liftToSubmodule K raw).get i : (denotSpace σ s₁).carrier)
        ((HSpace.liftToSubmodule K raw).get j : (denotSpace σ s₁).carrier) =
        if i = j then 1 else 0
  have hvs_len : (HSpace.liftToSubmodule K raw).length = raw.length :=
    HSpace.liftToSubmodule_length_of_subset K raw h_subset
  have hi_lt : i.1 < raw.length := hvs_len ▸ i.isLt
  have hj_lt : j.1 < raw.length := hvs_len ▸ j.isLt
  rw [HSpace.liftToSubmodule_get_val_of_subset K raw h_subset i,
      HSpace.liftToSubmodule_get_val_of_subset K raw h_subset j]
  have h_orth := BasisFSV.fsvRight_orthonormal (denotSpace σ s₀) (denotSpace σ s₁)
                  ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
                  pred
                  ((denotBasis σ (Basis.stdSpace s₀)).atSpace (denotSpace σ s₀))
                  ((denotBasis σ (Basis.stdSpace s₁)).atSpace (denotSpace σ s₁))
                  ⟨i.1, hi_lt⟩ ⟨j.1, hj_lt⟩
  rw [h_orth]
  by_cases hij : i = j
  · subst hij; simp
  · have hij' : (⟨i.1, hi_lt⟩ : Fin raw.length) ≠ ⟨j.1, hj_lt⟩ :=
      fun h => hij (by apply Fin.ext; exact Fin.mk.inj h)
    simp [hij, hij']

theorem stdBasis_orthonormal_space : ∀ (σ : DEnv) (ε : NLCtx) (s : Space)
    (_hs : SValid ε s) (_hσ : EnvWF σ ∅ ε),
    let V := denotSpace σ s
    let vs := BasisDenot.atSpace V (denotBasis σ (Basis.stdSpace s))
    ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0
  | σ, _, .empty, _, _ => by
      show ∀ i j : Fin (BasisDenot.atSpace (denotSpace σ (.empty : Space))
                          (denotBasis σ (Basis.stdSpace (.empty : Space)))).length,
            (denotSpace σ (.empty : Space)).innerProduct
              ((BasisDenot.atSpace _ (denotBasis σ (Basis.stdSpace (.empty : Space)))).get i)
              ((BasisDenot.atSpace _ (denotBasis σ (Basis.stdSpace (.empty : Space)))).get j) =
            if i = j then 1 else 0
      have h_db : denotBasis σ (Basis.stdSpace (.empty : Space)) =
                    .vecs HSpace.empty ([] : List HSpace.empty.carrier) := by
        simp [Basis.stdSpace, denotBasis]
      rw [show denotSpace σ (.empty : Space) = HSpace.empty from rfl,
          h_db, BasisDenot.atSpace_vecs_self]
      exact denotBasis_orthonormal_empty
  | σ, _, .real, _, _ => by
      show ∀ i j : Fin (BasisDenot.atSpace (denotSpace σ (.real : Space))
                          (denotBasis σ (Basis.stdSpace (.real : Space)))).length,
            (denotSpace σ (.real : Space)).innerProduct
              ((BasisDenot.atSpace _ (denotBasis σ (Basis.stdSpace (.real : Space)))).get i)
              ((BasisDenot.atSpace _ (denotBasis σ (Basis.stdSpace (.real : Space)))).get j) =
            if i = j then 1 else 0
      have h_db : denotBasis σ (Basis.stdSpace (.real : Space)) =
                    .vecs HSpace.real ([(1 : ℝ)] : List HSpace.real.carrier) := by
        simp [Basis.stdSpace, denotBasis]
      rw [show denotSpace σ (.real : Space) = HSpace.real from rfl,
          h_db, BasisDenot.atSpace_vecs_self]
      exact denotBasis_orthonormal_one
  | σ, ε, .dual s, hs, hσ =>
      match hs with
      | .dual hs' =>
          stdBasis_orthonormal_dual_step σ s
            (stdBasis_orthonormal_space σ ε s hs' hσ)
  | σ, ε, .dsum s₀ s₁, hs, hσ =>
      match hs with
      | .dsum hs₀ hs₁ =>
          stdBasis_orthonormal_dsum_step σ s₀ s₁
            (stdBasis_orthonormal_space σ ε s₀ hs₀ hσ)
            (stdBasis_orthonormal_space σ ε s₁ hs₁ hσ)
  | σ, ε, .tprod s₀ s₁, hs, hσ =>
      match hs with
      | .tprod hs₀ hs₁ =>
          stdBasis_orthonormal_tprod_step σ s₀ s₁
            (stdBasis_orthonormal_space σ ε s₀ hs₀ hσ)
            (stdBasis_orthonormal_space σ ε s₁ hs₁ hσ)
  | σ, _, .ker s₀ s₁ e, _, _ => by
      show ∀ i j : Fin (BasisDenot.atSpace (denotSpace σ (.ker s₀ s₁ e))
                          (denotBasis σ (Basis.stdSpace (.ker s₀ s₁ e)))).length,
        (denotSpace σ (.ker s₀ s₁ e)).innerProduct
          ((BasisDenot.atSpace (denotSpace σ (.ker s₀ s₁ e))
              (denotBasis σ (Basis.stdSpace (.ker s₀ s₁ e)))).get i)
          ((BasisDenot.atSpace (denotSpace σ (.ker s₀ s₁ e))
              (denotBasis σ (Basis.stdSpace (.ker s₀ s₁ e)))).get j) =
          if i = j then 1 else 0
      rw [show denotSpace σ (.ker s₀ s₁ e) =
            HSpace.ofSubmodule (denotSpace σ s₀)
              (LinearMap.ker ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)))
            from rfl,
          denotBasis_stdSpace_ker σ s₀ s₁ e, BasisDenot.atSpace_vecs_self]
      exact stdBasis_orthonormal_proj_left σ s₀ s₁ e
        (fun μ => decide (μ = 0)) (LinearMap.ker _)
        (BasisFSV.fsvLeft_subset_ker (denotSpace σ s₀) (denotSpace σ s₁) _ _ _)
  | σ, _, .coker s₀ s₁ e, _, _ => by
      show ∀ i j : Fin (BasisDenot.atSpace (denotSpace σ (.coker s₀ s₁ e))
                          (denotBasis σ (Basis.stdSpace (.coker s₀ s₁ e)))).length,
        (denotSpace σ (.coker s₀ s₁ e)).innerProduct
          ((BasisDenot.atSpace (denotSpace σ (.coker s₀ s₁ e))
              (denotBasis σ (Basis.stdSpace (.coker s₀ s₁ e)))).get i)
          ((BasisDenot.atSpace (denotSpace σ (.coker s₀ s₁ e))
              (denotBasis σ (Basis.stdSpace (.coker s₀ s₁ e)))).get j) =
          if i = j then 1 else 0
      rw [show denotSpace σ (.coker s₀ s₁ e) =
            HSpace.ofSubmodule (denotSpace σ s₀)
              (Submodule.orthRel (denotSpace σ s₀).innerProduct
                (LinearMap.ker ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))))
            from rfl,
          denotBasis_stdSpace_coker σ s₀ s₁ e, BasisDenot.atSpace_vecs_self]
      exact stdBasis_orthonormal_proj_left σ s₀ s₁ e
        (fun μ => decide (μ ≠ 0))
        (Submodule.orthRel (denotSpace σ s₀).innerProduct (LinearMap.ker _))
        (BasisFSV.fsvLeft_subset_coker (denotSpace σ s₀) (denotSpace σ s₁) _ _ _)
  | σ, _, .img s₀ s₁ e, _, _ => by
      show ∀ i j : Fin (BasisDenot.atSpace (denotSpace σ (.img s₀ s₁ e))
                          (denotBasis σ (Basis.stdSpace (.img s₀ s₁ e)))).length,
        (denotSpace σ (.img s₀ s₁ e)).innerProduct
          ((BasisDenot.atSpace (denotSpace σ (.img s₀ s₁ e))
              (denotBasis σ (Basis.stdSpace (.img s₀ s₁ e)))).get i)
          ((BasisDenot.atSpace (denotSpace σ (.img s₀ s₁ e))
              (denotBasis σ (Basis.stdSpace (.img s₀ s₁ e)))).get j) =
          if i = j then 1 else 0
      rw [show denotSpace σ (.img s₀ s₁ e) =
            HSpace.ofSubmodule (denotSpace σ s₁)
              (LinearMap.range ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)))
            from rfl,
          denotBasis_stdSpace_img σ s₀ s₁ e, BasisDenot.atSpace_vecs_self]
      exact stdBasis_orthonormal_proj_right σ s₀ s₁ e
        (fun μ => decide (μ ≠ 0)) (LinearMap.range _)
        (BasisFSV.fsvRight_subset_range (denotSpace σ s₀) (denotSpace σ s₁) _ _ _)
  | σ, _, .coimg s₀ s₁ e, _, _ => by
      show ∀ i j : Fin (BasisDenot.atSpace (denotSpace σ (.coimg s₀ s₁ e))
                          (denotBasis σ (Basis.stdSpace (.coimg s₀ s₁ e)))).length,
        (denotSpace σ (.coimg s₀ s₁ e)).innerProduct
          ((BasisDenot.atSpace (denotSpace σ (.coimg s₀ s₁ e))
              (denotBasis σ (Basis.stdSpace (.coimg s₀ s₁ e)))).get i)
          ((BasisDenot.atSpace (denotSpace σ (.coimg s₀ s₁ e))
              (denotBasis σ (Basis.stdSpace (.coimg s₀ s₁ e)))).get j) =
          if i = j then 1 else 0
      rw [show denotSpace σ (.coimg s₀ s₁ e) =
            HSpace.ofSubmodule (denotSpace σ s₁)
              (Submodule.orthRel (denotSpace σ s₁).innerProduct
                (LinearMap.range ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))))
            from rfl,
          denotBasis_stdSpace_coimg σ s₀ s₁ e, BasisDenot.atSpace_vecs_self]
      exact stdBasis_orthonormal_proj_right σ s₀ s₁ e
        (fun μ => decide (μ = 0))
        (Submodule.orthRel (denotSpace σ s₁).innerProduct (LinearMap.range _))
        (BasisFSV.fsvRight_subset_coimg (denotSpace σ s₀) (denotSpace σ s₁) _ _ _)
termination_by σ _ s _ _ => Space.size s
decreasing_by all_goals (simp [Space.size]; try omega)

/-- Every syntactically standard valid basis denotes an orthonormal list in its
actual source space. -/
theorem denotBasis_orthonormal_of_isStd (sigma : DEnv) (epsilon : NLCtx) (b : Basis)
    (hb : Basis.BasisValid epsilon b) (hstd : Basis.isStd b) :
    let V := denotSpace sigma (Basis.sof b)
    let vs := BasisDenot.atSpace V (denotBasis sigma b)
    ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0 := by
  induction b with
  | empty =>
      dsimp only
      rw [show denotSpace sigma (Basis.sof .empty) = HSpace.empty from rfl,
        show denotBasis sigma .empty = .vecs HSpace.empty [] by simp only [denotBasis],
        BasisDenot.atSpace_vecs_self]
      exact denotBasis_orthonormal_empty
  | one =>
      dsimp only
      rw [show denotSpace sigma (Basis.sof .one) = HSpace.real from rfl,
        show denotBasis sigma .one = .vecs HSpace.real [1] by simp only [denotBasis],
        BasisDenot.atSpace_vecs_self]
      exact denotBasis_orthonormal_one
  | dual b ih =>
      dsimp only
      have hb' := hb.dual_inv
      let V := denotSpace sigma (Basis.sof b)
      let vs := (denotBasis sigma b).atSpace V
      have hden : denotBasis sigma (.dual b) =
          .vecs (HSpace.dual V) (V.dualOfList vs) := by
        simp only [denotBasis]
        rfl
      rw [show denotSpace sigma (Basis.sof (.dual b)) = HSpace.dual V from rfl,
        hden, BasisDenot.atSpace_vecs_self]
      exact HSpace.dualOfList_orthonormal_of_orthonormal V vs (ih hb' hstd)
  | dsum b0 b1 ih0 ih1 =>
      dsimp only
      obtain ⟨hb0, hb1⟩ := hb.dsum_inv
      exact denotBasis_orthonormal_dsum sigma b0 b1 _ _ rfl rfl
        (ih0 hb0 hstd.1) (ih1 hb1 hstd.2)
  | tprod b0 b1 ih0 ih1 =>
      dsimp only
      obtain ⟨hb0, hb1⟩ := hb.tprod_inv
      exact denotBasis_orthonormal_tprod sigma b0 b1
        (ih0 hb0 hstd.1) (ih1 hb1 hstd.2)
  | proj s b0 b1 ih0 ih1 =>
      dsimp only
      cases s with
      | ker s0 s1 e =>
          let V0 := denotSpace sigma s0
          let V1 := denotSpace sigma s1
          let f := (denotTerm sigma e).asLinMap V0 V1
          let vs0 := (denotBasis sigma b0).atSpace V0
          let vs1 := (denotBasis sigma b1).atSpace V1
          let raw := BasisFSV.fsvLeft V0 V1 f (fun mu => decide (mu = 0)) vs0 vs1
          let K := LinearMap.ker f
          have hden : denotBasis sigma (.proj (.ker s0 s1 e) b0 b1) =
              .vecs (HSpace.ofSubmodule V0 K) (HSpace.liftToSubmodule K raw) := by
            simp only [denotBasis]
            rfl
          rw [show denotSpace sigma (Basis.sof (.proj (.ker s0 s1 e) b0 b1)) =
              HSpace.ofSubmodule V0 K from rfl, hden, BasisDenot.atSpace_vecs_self]
          exact HSpace.liftToSubmodule_orthonormal_of_subset V0 K raw
            (BasisFSV.fsvLeft_subset_ker V0 V1 f vs0 vs1)
            (BasisFSV.fsvLeft_orthonormal V0 V1 f (fun mu => decide (mu = 0)) vs0 vs1)
      | coker s0 s1 e =>
          let V0 := denotSpace sigma s0
          let V1 := denotSpace sigma s1
          let f := (denotTerm sigma e).asLinMap V0 V1
          let vs0 := (denotBasis sigma b0).atSpace V0
          let vs1 := (denotBasis sigma b1).atSpace V1
          let raw := BasisFSV.fsvLeft V0 V1 f (fun mu => decide (mu ≠ 0)) vs0 vs1
          let K := Submodule.orthRel V0.innerProduct (LinearMap.ker f)
          have hden : denotBasis sigma (.proj (.coker s0 s1 e) b0 b1) =
              .vecs (HSpace.ofSubmodule V0 K) (HSpace.liftToSubmodule K raw) := by
            simp only [denotBasis]
            rfl
          rw [show denotSpace sigma (Basis.sof (.proj (.coker s0 s1 e) b0 b1)) =
              HSpace.ofSubmodule V0 K from rfl, hden, BasisDenot.atSpace_vecs_self]
          exact HSpace.liftToSubmodule_orthonormal_of_subset V0 K raw
            (BasisFSV.fsvLeft_subset_coker V0 V1 f vs0 vs1)
            (BasisFSV.fsvLeft_orthonormal V0 V1 f (fun mu => decide (mu ≠ 0)) vs0 vs1)
      | img s0 s1 e =>
          let V0 := denotSpace sigma s0
          let V1 := denotSpace sigma s1
          let f := (denotTerm sigma e).asLinMap V0 V1
          let vs0 := (denotBasis sigma b0).atSpace V0
          let vs1 := (denotBasis sigma b1).atSpace V1
          let raw := BasisFSV.fsvRight V0 V1 f (fun mu => decide (mu ≠ 0)) vs0 vs1
          let K := LinearMap.range f
          have hden : denotBasis sigma (.proj (.img s0 s1 e) b0 b1) =
              .vecs (HSpace.ofSubmodule V1 K) (HSpace.liftToSubmodule K raw) := by
            simp only [denotBasis]
            rfl
          rw [show denotSpace sigma (Basis.sof (.proj (.img s0 s1 e) b0 b1)) =
              HSpace.ofSubmodule V1 K from rfl, hden, BasisDenot.atSpace_vecs_self]
          exact HSpace.liftToSubmodule_orthonormal_of_subset V1 K raw
            (BasisFSV.fsvRight_subset_range V0 V1 f vs0 vs1)
            (BasisFSV.fsvRight_orthonormal V0 V1 f (fun mu => decide (mu ≠ 0)) vs0 vs1)
      | coimg s0 s1 e =>
          let V0 := denotSpace sigma s0
          let V1 := denotSpace sigma s1
          let f := (denotTerm sigma e).asLinMap V0 V1
          let vs0 := (denotBasis sigma b0).atSpace V0
          let vs1 := (denotBasis sigma b1).atSpace V1
          let raw := BasisFSV.fsvRight V0 V1 f (fun mu => decide (mu = 0)) vs0 vs1
          let K := Submodule.orthRel V1.innerProduct (LinearMap.range f)
          have hden : denotBasis sigma (.proj (.coimg s0 s1 e) b0 b1) =
              .vecs (HSpace.ofSubmodule V1 K) (HSpace.liftToSubmodule K raw) := by
            simp only [denotBasis]
            rfl
          rw [show denotSpace sigma (Basis.sof (.proj (.coimg s0 s1 e) b0 b1)) =
              HSpace.ofSubmodule V1 K from rfl, hden, BasisDenot.atSpace_vecs_self]
          exact HSpace.liftToSubmodule_orthonormal_of_subset V1 K raw
            (BasisFSV.fsvRight_subset_coimg V0 V1 f vs0 vs1)
            (BasisFSV.fsvRight_orthonormal V0 V1 f (fun mu => decide (mu = 0)) vs0 vs1)
      | empty | real | dual _ | dsum _ _ | tprod _ _ =>
          cases hb
  | image b ih =>
      dsimp only
      exact False.elim hstd
  | terms s es b ih =>
      dsimp only
      exact False.elim hstd
  | frame b0 b1 ih0 ih1 =>
      dsimp only
      intro i
      have hempty : (denotBasis sigma (.frame b0 b1)).atSpace
          (denotSpace sigma (Basis.sof (.frame b0 b1))) = [] := by
        simp [denotBasis, BasisDenot.atSpace_frame]
      rw [hempty] at i
      exact i.elim0

/-- "Expected `HSpace`" for orthonormality at a `Ty`. On `.space s` it's
    `denotSpace σ s` (the carrier-aligned choice). On `.piTy x τ₀ τ₁`
    we return `HSpace.empty`; the denotation is frame-shaped so
    `BasisDenot.atSpace _ _ = []` for any choice. -/
private def BasisOrthonormalAt (V : HSpace) (d : BasisDenot) : Prop :=
  let vs := d.atSpace V
  ∀ i j : Fin vs.length,
    V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0

private theorem BasisOrthonormalAt.congr
    {V W : HSpace} {d e : BasisDenot} (hV : V = W) (hd : d = e) :
    BasisOrthonormalAt V d ↔ BasisOrthonormalAt W e := by
  subst W
  subst e
  rfl

private noncomputable def stdBasis_atSpace_orthonormal_expectedV
    (σ : DEnv) : Ty → HSpace
  | .space s   => denotSpace σ s
  | .piTy _ _  => HSpace.empty

theorem stdBasis_atSpace_orthonormal : ∀ (σ : DEnv) (ε : NLCtx) (τ : Ty) {k : Kind}
    (_hτ : TValid ε τ k) (_hσ : EnvWF σ ∅ ε),
    let V := stdBasis_atSpace_orthonormal_expectedV σ τ
    let vs := BasisDenot.atSpace V (denotBasis σ (Basis.std τ))
    ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0
  | σ, ε, .space s, _, hτ, hσ => by
      cases hτ with
      | space hs =>
          -- `Basis.std (.space s) = Basis.stdSpace s` and
          -- `stdBasis_atSpace_orthonormal_expectedV σ (.space s) = denotSpace σ s`.
          show ∀ i j, _
          exact stdBasis_orthonormal_space σ ε s hs hσ
  | σ, _, .piTy τ₀ τ₁, _, _, _ => by
      -- `Basis.std (.piTy τ₀ τ₁) = .frame (Basis.std τ₀) (Basis.std τ₁)`.
      -- `denotBasis σ (.frame b₀ b₁) = .frame T_outer.El (fun y => …)`,
      -- and `BasisDenot.atSpace V (.frame _ _) = []` for any `V`.
      intro V vs i
      have hempty : vs = [] := by
        show BasisDenot.atSpace _ (denotBasis σ (Basis.std (.piTy τ₀ τ₁))) = []
        simp [Basis.std, denotBasis, BasisDenot.atSpace_frame]
      rw [hempty] at i
      exact i.elim0

theorem stdBasis_atSpace_orthonormal_frame_fiber (σ : DEnv) (ε : NLCtx)
    (x : Name) (τ₀ τ₁ : Ty) {k₀ k₁ : Kind}
    (hτ : TValid ε (.piTy τ₀ τ₁) (.arrow k₀ k₁))
    (hx : x ∉ Ty.fv τ₁)
    (hctx : CtxWF ∅ ε)
    (hσ : EnvWF σ ∅ ε) :
    ∀ y : (denotTy σ τ₀).El,
      let σy := σ.bind x ((denotTy σ τ₀).embed y)
      let V_y := denotSpace σy (Basis.sof (Basis.openVar x (Basis.std τ₁)))
      let vs := BasisDenot.atSpace V_y (denotBasis σy (Basis.openVar x (Basis.std τ₁)))
      ∀ i j : Fin vs.length,
        V_y.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0 := by
  cases hτ with
  | piTy L hτ₀ hbody =>
      cases τ₁ with
      | space s =>
          simp only [Ty.fv] at hx
          obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
            (L ∪ ε.keys ∪ Ty.fv τ₀ ∪ Space.fv s)
          simp only [Finset.mem_union, not_or] at hz
          rcases hz with ⟨⟨⟨hzL, hzεk⟩, hzτ₀⟩, hzs⟩
          have hzε : z ∉ ε := fun hzmem => hzεk (Finmap.mem_keys.mpr hzmem)
          have hctxz : CtxWF ∅ (Finmap.insert z τ₀ ε) :=
            hctx.insert_nl Finmap.notMem_empty hzε hτ₀.fv_closure
          intro y
          have henvz : EnvWF (σ.bind z ((denotTy σ τ₀).embed y)) ∅
              (Finmap.insert z τ₀ ε) :=
            hσ.bind_nl hctx Finmap.notMem_empty hzε hzτ₀ y
          have horthz := stdBasis_atSpace_orthonormal
            (σ.bind z ((denotTy σ τ₀).embed y)) (Finmap.insert z τ₀ ε)
            (Ty.openVar z (.space s)) (hbody z hzL) henvz
          have hV := denotSpaceOpenIrrel σ s x z ((denotTy σ τ₀).embed y) hx hzs
          have hB := denotBasisOpenIrrel σ (Basis.stdSpace s) x z
            ((denotTy σ τ₀).embed y) (by simpa using hx) (by simpa using hzs)
          dsimp only
          have hsof_x : Basis.sof (Basis.openRec 0 (.var x) (Basis.stdSpace s)) =
              Space.openRec 0 (.var x) s := by
            rw [Basis.sof_openRec, Basis.sof_stdSpace]
          have hsof_z : Basis.sof (Basis.openRec 0 (.var z) (Basis.stdSpace s)) =
              Space.openRec 0 (.var z) s := by
            rw [Basis.sof_openRec, Basis.sof_stdSpace]
          have hV' : denotSpace (σ.bind x ((denotTy σ τ₀).embed y))
                (Basis.sof (Basis.openRec 0 (.var x) (Basis.stdSpace s))) =
              denotSpace (σ.bind z ((denotTy σ τ₀).embed y))
                (Basis.sof (Basis.openRec 0 (.var z) (Basis.stdSpace s))) := by
            rw [hsof_x, hsof_z]
            exact hV
          apply (BasisOrthonormalAt.congr hV' hB).mpr
          have horthz' : BasisOrthonormalAt
              (denotSpace (σ.bind z ((denotTy σ τ₀).embed y))
                (Space.openRec 0 (.var z) s))
              (denotBasis (σ.bind z ((denotTy σ τ₀).embed y))
                (Basis.stdSpace (Space.openRec 0 (.var z) s))) := by
            simpa [BasisOrthonormalAt, stdBasis_atSpace_orthonormal_expectedV, Ty.openVar,
              Ty.openRec, Basis.std] using horthz
          have hVz : denotSpace (σ.bind z ((denotTy σ τ₀).embed y))
                (Space.openRec 0 (.var z) s) =
              denotSpace (σ.bind z ((denotTy σ τ₀).embed y))
                (Basis.sof (Basis.openRec 0 (.var z) (Basis.stdSpace s))) :=
            congrArg (denotSpace (σ.bind z ((denotTy σ τ₀).embed y))) hsof_z.symm
          have hBz : denotBasis (σ.bind z ((denotTy σ τ₀).embed y))
                (Basis.stdSpace (Space.openRec 0 (.var z) s)) =
              denotBasis (σ.bind z ((denotTy σ τ₀).embed y))
                (Basis.openRec 0 (.var z) (Basis.stdSpace s)) :=
            congrArg (denotBasis (σ.bind z ((denotTy σ τ₀).embed y)))
              (Basis.stdSpace_openRec 0 (.var z) s)
          exact (BasisOrthonormalAt.congr hVz hBz).mp horthz'
      | piTy a b =>
          intro y
          dsimp only
          intro i
          have hempty : BasisDenot.atSpace
              (denotSpace (σ.bind x ((denotTy σ τ₀).embed y))
                (Basis.sof (Basis.openVar x (Basis.std (.piTy a b)))))
              (denotBasis (σ.bind x ((denotTy σ τ₀).embed y))
                (Basis.openVar x (Basis.std (.piTy a b)))) = [] := by
            simp [Basis.std, Basis.openVar, Basis.openRec, denotBasis,
              BasisDenot.atSpace_frame]
          rw [hempty] at i
          exact i.elim0

section AdequacyFacing

open Basis (BasisValid)

/-- The type of the residual field `AdequacyResidual.denotBasis_isListBasis`
    (`Adequacy/Master.lean`), verbatim: a valid non-frame basis denotes a list basis of
    `⟦sof b⟧σ`. This is `denotBasis_isBasis` read at its `.vecs` shape
    (`denotBasis_atSpace_isListBasis`); the `hnf` hypothesis is not consumed (frames are
    handled degenerately there). -/
theorem denotBasis_isListBasis : ∀ {σ : DEnv} {Γ : NLCtx} {b : Basis}
      (hb : BasisValid Γ b) (hctx : CtxWF ∅ Γ) (hσ : EnvWF σ ∅ Γ)
      (hnf : ∀ b₀ b₁, b ≠ .frame b₀ b₁),
      IsListBasis (denotSpace σ (Basis.sof b))
        ((denotBasis σ b).atSpace (denotSpace σ (Basis.sof b))) :=
  fun hb hctx hσ _ => denotBasis_atSpace_isListBasis _ _ _ hb hctx hσ

/-- `lem:stdBasisOrthonormal` at a fixed context, in the shape of the `hstd` hypothesis of
    `arm_term_inner_std` minus its `dof` clause: the denoted list of a valid standard basis is
    a list basis of `⟦sof b⟧σ` whose Gram matrix is the identity. -/
theorem denotBasis_std_orthonormal_core {σ : DEnv} {Γ : NLCtx} {b : Basis}
    (hb : BasisValid Γ b) (hctx : CtxWF ∅ Γ) (hσ : EnvWF σ ∅ Γ) (hstd : Basis.isStd b) :
    IsListBasis (denotSpaceAux σ [] (Basis.sof b))
      ((denotBasis σ b).atSpace (denotSpaceAux σ [] (Basis.sof b))) ∧
    (∀ i j : Fin ((denotBasis σ b).atSpace (denotSpaceAux σ [] (Basis.sof b))).length,
      (denotSpaceAux σ [] (Basis.sof b)).innerProduct
        (((denotBasis σ b).atSpace (denotSpaceAux σ [] (Basis.sof b))).get i)
        (((denotBasis σ b).atSpace (denotSpaceAux σ [] (Basis.sof b))).get j) =
        if i = j then 1 else 0) :=
  ⟨denotBasis_atSpace_isListBasis σ Γ b hb hctx hσ,
   denotBasis_orthonormal_of_isStd σ Γ b hb hstd⟩

end AdequacyFacing

end GLang
