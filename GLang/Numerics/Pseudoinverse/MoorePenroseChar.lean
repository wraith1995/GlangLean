

import GLang.Annotated.Denotation

namespace GLang

namespace LinearMap

variable {V₀ V₁ : Type}
    [AddCommGroup V₀] [Module ℝ V₀] [FiniteDimensional ℝ V₀]
    [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    {B₀ : V₀ →ₗ[ℝ] V₀ →ₗ[ℝ] ℝ} (h₀ : IsInnerProduct B₀)
    {B₁ : V₁ →ₗ[ℝ] V₁ →ₗ[ℝ] ℝ} (h₁ : IsInnerProduct B₁)
    (f : V₀ →ₗ[ℝ] V₁)

/-- Auxiliary: for any subspace `K ≤ V₀` and `R ≤ V₁` with `f`
    restricting to a bijection `K → R`, applying `f` to the subtype-
    embedding of `(ofBijective …).symm y` gives `y.val`. -/
private lemma f_restrict_symm_apply
    {U₀ U₁ : Type*} [AddCommGroup U₀] [Module ℝ U₀]
    [AddCommGroup U₁] [Module ℝ U₁]
    (K : Submodule ℝ U₀) (R : Submodule ℝ U₁) (g : U₀ →ₗ[ℝ] U₁)
    (h_in : ∀ x, x ∈ K → g x ∈ R)
    (hbij : Function.Bijective
      (LinearMap.codRestrict R (g ∘ₗ K.subtype) (fun x => h_in x.1 x.2)))
    (y : R) :
    g (K.subtype
        ((LinearEquiv.ofBijective
            (LinearMap.codRestrict R (g ∘ₗ K.subtype) (fun x => h_in x.1 x.2))
            hbij).symm y))
      = y.val := by
  -- `LinearMap.codRestrict_apply` + `LinearEquiv.apply_symm_apply`, both rfl.
  exact congrArg Subtype.val
    (LinearEquiv.apply_symm_apply
      (LinearEquiv.ofBijective
        (LinearMap.codRestrict R (g ∘ₗ K.subtype) (fun x => h_in x.1 x.2))
        hbij) y)

/-- `mooreInv h₀ h₁ f v` lies in `(ker f)ᗮ`. -/
lemma mooreInv_mem_ker_orthogonal (v : V₁) :
    letI _ := h₀.toIPSCore
    letI _ := h₁.toIPSCore
    letI _ : NormedAddCommGroup V₀ :=
      (h₀.toIPSCore).toNormedAddCommGroup
    letI _ : NormedAddCommGroup V₁ :=
      (h₁.toIPSCore).toNormedAddCommGroup
    letI _ : InnerProductSpace ℝ V₀ :=
      InnerProductSpace.ofCore inferInstance
    letI _ : InnerProductSpace ℝ V₁ :=
      InnerProductSpace.ofCore inferInstance
    LinearMap.mooreInv h₀ h₁ f v ∈ (LinearMap.ker f)ᗮ := by
  letI := h₀.toIPSCore
  letI := h₁.toIPSCore
  letI : NormedAddCommGroup V₀ :=
    (h₀.toIPSCore).toNormedAddCommGroup
  letI : NormedAddCommGroup V₁ :=
    (h₁.toIPSCore).toNormedAddCommGroup
  letI : InnerProductSpace ℝ V₀ := InnerProductSpace.ofCore inferInstance
  letI : InnerProductSpace ℝ V₁ := InnerProductSpace.ofCore inferInstance
  show ((LinearMap.ker f)ᗮ.subtype _ : V₀) ∈ (LinearMap.ker f)ᗮ
  exact Submodule.coe_mem _

/-- Under valid inner products, `f (mooreInv f v)` equals the orthogonal
    projection of `v` onto `range f`. -/
lemma mooreInv_image_eq_starProjection (v : V₁) :
    letI _ := h₀.toIPSCore
    letI _ := h₁.toIPSCore
    letI _ : NormedAddCommGroup V₀ :=
      (h₀.toIPSCore).toNormedAddCommGroup
    letI _ : NormedAddCommGroup V₁ :=
      (h₁.toIPSCore).toNormedAddCommGroup
    letI _ : InnerProductSpace ℝ V₀ :=
      InnerProductSpace.ofCore inferInstance
    letI _ : InnerProductSpace ℝ V₁ :=
      InnerProductSpace.ofCore inferInstance
    f (LinearMap.mooreInv h₀ h₁ f v) =
      (LinearMap.range f).starProjection v := by
  letI := h₀.toIPSCore
  letI := h₁.toIPSCore
  letI : NormedAddCommGroup V₀ :=
    (h₀.toIPSCore).toNormedAddCommGroup
  letI : NormedAddCommGroup V₁ :=
    (h₁.toIPSCore).toNormedAddCommGroup
  letI : InnerProductSpace ℝ V₀ := InnerProductSpace.ofCore inferInstance
  letI : InnerProductSpace ℝ V₁ := InnerProductSpace.ofCore inferInstance
  -- Unfold mooreInv and reduce, then apply the helper lemma.
  unfold LinearMap.mooreInv
  simp only [LinearMap.comp_apply, Submodule.starProjection_apply]
  exact f_restrict_symm_apply
    (LinearMap.ker f)ᗮ (LinearMap.range f) f
    (fun _ _ => ⟨_, rfl⟩) _ _

/-- **Residual minimisation.** `mooreInv h₀ h₁ f v` minimises the
    `B₁`-norm-squared of `f w − v` over all `w : V₀`. -/
theorem mooreInv_minimisesResidual (v : V₁) (w : V₀) :
    B₁ (f (LinearMap.mooreInv h₀ h₁ f v) - v)
       (f (LinearMap.mooreInv h₀ h₁ f v) - v) ≤
    B₁ (f w - v) (f w - v) := by
  letI := h₀.toIPSCore
  letI := h₁.toIPSCore
  letI : NormedAddCommGroup V₀ :=
    (h₀.toIPSCore).toNormedAddCommGroup
  letI : NormedAddCommGroup V₁ :=
    (h₁.toIPSCore).toNormedAddCommGroup
  letI : InnerProductSpace ℝ V₀ := InnerProductSpace.ofCore inferInstance
  letI : InnerProductSpace ℝ V₁ := InnerProductSpace.ofCore inferInstance
  -- f g = P v where g := mooreInv ... v and P := R.starProjection
  have hfg : f (LinearMap.mooreInv h₀ h₁ f v) =
      (LinearMap.range f).starProjection v :=
    mooreInv_image_eq_starProjection h₀ h₁ f v
  -- Pythagorean decomposition: ‖f w − v‖² = ‖f w − Pv‖² + ‖Pv − v‖².
  have h_in_R : f w - (LinearMap.range f).starProjection v ∈ LinearMap.range f :=
    Submodule.sub_mem _ (LinearMap.mem_range_self f w)
      (Submodule.starProjection_apply_mem _ _)
  have h_in_perp : (LinearMap.range f).starProjection v - v ∈
      (LinearMap.range f)ᗮ := by
    have hsub := Submodule.sub_starProjection_mem_orthogonal
                  (K := LinearMap.range f) v
    have : (LinearMap.range f).starProjection v - v =
           -(v - (LinearMap.range f).starProjection v) := by abel
    rw [this]; exact neg_mem hsub
  -- The inner product of an R element with an R⊥ element is 0.
  have h_inner_zero :
      @inner ℝ _ _ (f w - (LinearMap.range f).starProjection v)
        ((LinearMap.range f).starProjection v - v) = 0 := by
    exact (Submodule.mem_orthogonal _ _).mp h_in_perp _ h_in_R
  -- Pythagorean: ‖(a) + (b)‖² = ‖a‖² + ‖b‖² when ⟨a, b⟩ = 0.
  have h_alg : (f w - (LinearMap.range f).starProjection v) +
      ((LinearMap.range f).starProjection v - v) = f w - v := by abel
  have h_pyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (f w - (LinearMap.range f).starProjection v)
      ((LinearMap.range f).starProjection v - v) h_inner_zero
  rw [h_alg] at h_pyth

  have norm_sq_eq : ∀ x : V₁, B₁ x x = ‖x‖^2 := fun x => by
    have hinner : B₁ x x = @inner ℝ V₁ _ x x := rfl
    rw [hinner, real_inner_self_eq_norm_sq]
  rw [norm_sq_eq, norm_sq_eq, hfg]

  simp only [pow_two]
  rw [h_pyth]
  -- Goal: ‖Pv − v‖ * ‖Pv − v‖ ≤ ‖f w − Pv‖ * ‖f w − Pv‖ + ‖Pv − v‖ * ‖Pv − v‖
  have hnn : 0 ≤ ‖f w - (LinearMap.range f).starProjection v‖ *
                 ‖f w - (LinearMap.range f).starProjection v‖ :=
    mul_self_nonneg _
  linarith

/-- **Norm minimisation among minimisers.** Any `w : V₀` that also
    minimises the residual `B₁ (f w − v) (f w − v)` has `B₀`-norm at
    least that of `mooreInv h₀ h₁ f v`. -/
theorem mooreInv_minNormAmongMinimisers (v : V₁) (w : V₀)
    (hw_min : ∀ w'', B₁ (f w - v) (f w - v) ≤ B₁ (f w'' - v) (f w'' - v)) :
    B₀ (LinearMap.mooreInv h₀ h₁ f v) (LinearMap.mooreInv h₀ h₁ f v) ≤
    B₀ w w := by
  letI := h₀.toIPSCore
  letI := h₁.toIPSCore
  letI : NormedAddCommGroup V₀ :=
    (h₀.toIPSCore).toNormedAddCommGroup
  letI : NormedAddCommGroup V₁ :=
    (h₁.toIPSCore).toNormedAddCommGroup
  letI : InnerProductSpace ℝ V₀ := InnerProductSpace.ofCore inferInstance
  letI : InnerProductSpace ℝ V₁ := InnerProductSpace.ofCore inferInstance
  -- Bridge: B₀ x x = ‖x‖² (real IPS).
  have norm_sq_eq₀ : ∀ x : V₀, B₀ x x = ‖x‖^2 := fun x => by
    have : B₀ x x = @inner ℝ V₀ _ x x := rfl
    rw [this, real_inner_self_eq_norm_sq]
  have norm_sq_eq₁ : ∀ x : V₁, B₁ x x = ‖x‖^2 := fun x => by
    have : B₁ x x = @inner ℝ V₁ _ x x := rfl
    rw [this, real_inner_self_eq_norm_sq]
  -- mooreInv v minimises the residual too, so equality holds with w.
  have hmin_eq : B₁ (f w - v) (f w - v) =
      B₁ (f (LinearMap.mooreInv h₀ h₁ f v) - v)
         (f (LinearMap.mooreInv h₀ h₁ f v) - v) := by
    apply le_antisymm
    · exact hw_min _
    · exact mooreInv_minimisesResidual h₀ h₁ f v w
  -- By Pythagorean, f w = f (mooreInv v) (both equal P_R v).
  have hfg : f (LinearMap.mooreInv h₀ h₁ f v) =
      (LinearMap.range f).starProjection v :=
    mooreInv_image_eq_starProjection h₀ h₁ f v
  -- Squared residuals translated to norms.
  rw [norm_sq_eq₁, norm_sq_eq₁, hfg] at hmin_eq
  -- Apply Pythagorean to `f w - v = (f w − Pv) + (Pv − v)` and use equality.
  have h_in_R : f w - (LinearMap.range f).starProjection v ∈ LinearMap.range f :=
    Submodule.sub_mem _ (LinearMap.mem_range_self f w)
      (Submodule.starProjection_apply_mem _ _)
  have h_in_perp : (LinearMap.range f).starProjection v - v ∈
      (LinearMap.range f)ᗮ := by
    have hsub := Submodule.sub_starProjection_mem_orthogonal
                  (K := LinearMap.range f) v
    have : (LinearMap.range f).starProjection v - v =
           -(v - (LinearMap.range f).starProjection v) := by abel
    rw [this]; exact neg_mem hsub
  have h_inner_zero :
      @inner ℝ _ _ (f w - (LinearMap.range f).starProjection v)
        ((LinearMap.range f).starProjection v - v) = 0 :=
    (Submodule.mem_orthogonal _ _).mp h_in_perp _ h_in_R
  have h_alg : (f w - (LinearMap.range f).starProjection v) +
      ((LinearMap.range f).starProjection v - v) = f w - v := by abel
  have h_pyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (f w - (LinearMap.range f).starProjection v)
      ((LinearMap.range f).starProjection v - v) h_inner_zero
  rw [h_alg] at h_pyth
  -- hmin_eq says ‖f w − v‖² = ‖Pv − v‖² (using `pow_two` matches what h_pyth uses).
  rw [show (‖f w - v‖^2 = ‖f w - v‖ * ‖f w - v‖) from sq ‖f w - v‖,
      show (‖(LinearMap.range f).starProjection v - v‖^2 =
            ‖(LinearMap.range f).starProjection v - v‖ *
            ‖(LinearMap.range f).starProjection v - v‖) from
        sq ‖(LinearMap.range f).starProjection v - v‖,
      h_pyth] at hmin_eq

  have hfw_norm : ‖f w - (LinearMap.range f).starProjection v‖ *
      ‖f w - (LinearMap.range f).starProjection v‖ = 0 := by linarith
  have hfweq : f w = (LinearMap.range f).starProjection v := by
    have h_nn := mul_self_nonneg ‖f w - (LinearMap.range f).starProjection v‖
    have : ‖f w - (LinearMap.range f).starProjection v‖ = 0 := by
      rcases mul_self_eq_zero.mp hfw_norm with h
      exact h
    have hsub : f w - (LinearMap.range f).starProjection v = 0 :=
      norm_eq_zero.mp this
    exact sub_eq_zero.mp hsub
  -- f w = f (mooreInv v): so w - mooreInv v ∈ ker f.
  have h_diff_in_ker : w - LinearMap.mooreInv h₀ h₁ f v ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hfweq, hfg, sub_self]
  -- mooreInv v ∈ (ker f)ᗮ.
  have h_g_in_perp : LinearMap.mooreInv h₀ h₁ f v ∈ (LinearMap.ker f)ᗮ :=
    mooreInv_mem_ker_orthogonal h₀ h₁ f v
  -- Inner product zero between ker f and (ker f)ᗮ.
  have h_inner_zero_dom :
      @inner ℝ _ _ (w - LinearMap.mooreInv h₀ h₁ f v)
        (LinearMap.mooreInv h₀ h₁ f v) = 0 :=
    (Submodule.mem_orthogonal _ _).mp h_g_in_perp _ h_diff_in_ker
  -- Pythagorean in V₀.
  have h_alg' : (w - LinearMap.mooreInv h₀ h₁ f v) +
      LinearMap.mooreInv h₀ h₁ f v = w := by abel
  have h_pyth' :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (w - LinearMap.mooreInv h₀ h₁ f v)
      (LinearMap.mooreInv h₀ h₁ f v) h_inner_zero_dom
  rw [h_alg'] at h_pyth'
  -- h_pyth' : ‖w‖² = ‖w − g‖² + ‖g‖²  (mul form).
  rw [norm_sq_eq₀, norm_sq_eq₀]
  simp only [pow_two]
  rw [h_pyth']
  have hnn : 0 ≤ ‖w - LinearMap.mooreInv h₀ h₁ f v‖ *
                 ‖w - LinearMap.mooreInv h₀ h₁ f v‖ :=
    mul_self_nonneg _
  linarith

theorem mooreInv_isPaperPinv (v : V₁) :
    (∀ w, B₁ (f (LinearMap.mooreInv h₀ h₁ f v) - v)
           (f (LinearMap.mooreInv h₀ h₁ f v) - v)
         ≤ B₁ (f w - v) (f w - v)) ∧
    (∀ w, (∀ w', B₁ (f w - v) (f w - v) ≤ B₁ (f w' - v) (f w' - v)) →
      B₀ (LinearMap.mooreInv h₀ h₁ f v) (LinearMap.mooreInv h₀ h₁ f v) ≤
      B₀ w w) :=
  ⟨mooreInv_minimisesResidual h₀ h₁ f v,
   mooreInv_minNormAmongMinimisers h₀ h₁ f v⟩

end LinearMap

end GLang
