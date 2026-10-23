

import GLang.Proofs.Source.Soundness
import GLang.Proofs.Basis.BasisSoundness

namespace GLang

open scoped BigOperators

open DEnv (AgreeOn)

/-- The denoted FFS witness map `f = ⟦e⟧σ`, packaged. -/
private noncomputable def imageF (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    (denotSpace σ s₀).carrier →ₗ[ℝ] (denotSpace σ s₁).carrier :=
  (denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)

/-- Corestriction of `f` to `CoKer → Img`. -/
private noncomputable def imageRestrict (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    (denotSpace σ (Space.coker s₀ s₁ e)).carrier →ₗ[ℝ]
      ↥(LinearMap.range (imageF σ s₀ s₁ e)) :=
  LinearMap.codRestrict (LinearMap.range (imageF σ s₀ s₁ e))
    ((imageF σ s₀ s₁ e).comp
      (Submodule.subtype
        (Submodule.orthRel (denotSpace σ s₀).innerProduct
          (LinearMap.ker (imageF σ s₀ s₁ e)))))
    (fun _ => LinearMap.mem_range_self _ _)

/-- `denotBasis` at `.image b` with `sof b = CoKer(e)` known. -/
private theorem denotBasis_image_unfold (σ : DEnv) (b : Basis) {s₀ s₁ : Space}
    {e : Term} (hsof : Basis.sof b = .coker s₀ s₁ e) :
    denotBasis σ (.image b)
      = .vecs
          (HSpace.ofSubmodule (denotSpace σ s₁)
            (LinearMap.range (imageF σ s₀ s₁ e)))
          (((denotBasis σ b).atSpace
              (denotSpace σ (.coker s₀ s₁ e))).map
            (imageRestrict σ s₀ s₁ e)) := by
  conv_lhs => rw [denotBasis]
  split
  · rename_i s₀' s₁' e' hmatch
    have heq : Space.coker s₀ s₁ e = Space.coker s₀' s₁' e' :=
      hsof.symm.trans hmatch
    injection heq with h0 h1 h2
    subst h0; subst h1; subst h2
    rfl
  · rename_i hneg
    exact absurd hsof (hneg s₀ s₁ e)

/-- If `σ₁ ≈ σ₂` on `Basis.fv b`, then `denotBasis σ₁ b = denotBasis σ₂ b`.

    Mirrors `FVIrrelevance.lean`'s `denotSpaceAux_agree`: every recursive
    position is a congruence; the leaf reads (`denotSpace`/`denotTerm`/
    `denotTy` of `sof`/`tof`/embedded terms) use the closed-term agreement
    corollaries, and the `.frame` arm opens at the SAME canonical fresh
    name on both sides, extending `AgreeOn` by `bind_erase`. -/
theorem denotBasis_agree :
    ∀ (b : Basis) {σ₁ σ₂ : DEnv}, σ₁.AgreeOn σ₂ (Basis.fv b) →
      denotBasis σ₁ b = denotBasis σ₂ b
  | .empty, _, _, _ => by simp only [denotBasis]
  | .one, _, _, _ => by simp only [denotBasis]
  | .dual b, σ₁, σ₂, h => by
      unfold Basis.fv at h
      have hsof : denotSpace σ₁ (Basis.sof b) = denotSpace σ₂ (Basis.sof b) :=
        denotSpace_agree _ (h.mono (Basis.fv_sof_subset b))
      have hb := denotBasis_agree b h
      -- opaque-function factoring: dependent positions hide behind `F`.
      let F : (V : HSpace) → BasisDenot → BasisDenot :=
        fun V d => .vecs (HSpace.dual V) (V.dualOfList (d.atSpace V))
      have hL : denotBasis σ₁ (.dual b) = F (denotSpace σ₁ (Basis.sof b)) (denotBasis σ₁ b) := by
        simp only [denotBasis, F]
      have hR : denotBasis σ₂ (.dual b) = F (denotSpace σ₂ (Basis.sof b)) (denotBasis σ₂ b) := by
        simp only [denotBasis, F]
      rw [hL, hR, hsof, hb]
  | .dsum b₀ b₁, σ₁, σ₂, h => by
      unfold Basis.fv at h
      have h₀ := h.of_union_left
      have h₁ := h.of_union_right
      have hs₀ := denotSpace_agree (Basis.sof b₀) (h₀.mono (Basis.fv_sof_subset b₀))
      have hs₁ := denotSpace_agree (Basis.sof b₁) (h₁.mono (Basis.fv_sof_subset b₁))
      have hb₀ := denotBasis_agree b₀ h₀
      have hb₁ := denotBasis_agree b₁ h₁
      let F : (V₀ V₁ : HSpace) → BasisDenot → BasisDenot → BasisDenot :=
        fun V₀ V₁ d₀ d₁ =>
          .vecs (HSpace.dsum V₀ V₁) (HSpace.dsumOfLists V₀ V₁ (d₀.atSpace V₀) (d₁.atSpace V₁))
      have hL : denotBasis σ₁ (.dsum b₀ b₁)
          = F (denotSpace σ₁ (Basis.sof b₀)) (denotSpace σ₁ (Basis.sof b₁))
              (denotBasis σ₁ b₀) (denotBasis σ₁ b₁) := by
            simp only [denotBasis, F]
      have hR : denotBasis σ₂ (.dsum b₀ b₁)
          = F (denotSpace σ₂ (Basis.sof b₀)) (denotSpace σ₂ (Basis.sof b₁))
              (denotBasis σ₂ b₀) (denotBasis σ₂ b₁) := by
            simp only [denotBasis, F]
      rw [hL, hR, hs₀, hs₁, hb₀, hb₁]
  | .tprod b₀ b₁, σ₁, σ₂, h => by
      unfold Basis.fv at h
      have h₀ := h.of_union_left
      have h₁ := h.of_union_right
      have hs₀ := denotSpace_agree (Basis.sof b₀) (h₀.mono (Basis.fv_sof_subset b₀))
      have hs₁ := denotSpace_agree (Basis.sof b₁) (h₁.mono (Basis.fv_sof_subset b₁))
      have hb₀ := denotBasis_agree b₀ h₀
      have hb₁ := denotBasis_agree b₁ h₁
      let F : (V₀ V₁ : HSpace) → BasisDenot → BasisDenot → BasisDenot :=
        fun V₀ V₁ d₀ d₁ =>
          .vecs (HSpace.tprod V₀ V₁) (HSpace.tprodOfLists V₀ V₁ (d₀.atSpace V₀) (d₁.atSpace V₁))
      have hL : denotBasis σ₁ (.tprod b₀ b₁)
          = F (denotSpace σ₁ (Basis.sof b₀)) (denotSpace σ₁ (Basis.sof b₁))
              (denotBasis σ₁ b₀) (denotBasis σ₁ b₁) := by
            simp only [denotBasis, F]
      have hR : denotBasis σ₂ (.tprod b₀ b₁)
          = F (denotSpace σ₂ (Basis.sof b₀)) (denotSpace σ₂ (Basis.sof b₁))
              (denotBasis σ₂ b₀) (denotBasis σ₂ b₁) := by
            simp only [denotBasis, F]
      rw [hL, hR, hs₀, hs₁, hb₀, hb₁]
  | .proj s b₀ b₁, σ₁, σ₂, h => by
      unfold Basis.fv at h
      have hs : σ₁.AgreeOn σ₂ (Space.fv s) := h.of_union_left.of_union_left
      have h₀ : σ₁.AgreeOn σ₂ (Basis.fv b₀) := h.of_union_left.of_union_right
      have h₁ : σ₁.AgreeOn σ₂ (Basis.fv b₁) := h.of_union_right
      have hb₀ := denotBasis_agree b₀ h₀
      have hb₁ := denotBasis_agree b₁ h₁
      cases s with
      | empty =>
          simp only [denotBasis]; exact congrArg (BasisDenot.vecs · []) (denotSpace_agree _ hs)
      | real =>
          simp only [denotBasis]; exact congrArg (BasisDenot.vecs · []) (denotSpace_agree _ hs)
      | dual _ =>
          simp only [denotBasis]; exact congrArg (BasisDenot.vecs · []) (denotSpace_agree _ hs)
      | dsum _ _ =>
          simp only [denotBasis]; exact congrArg (BasisDenot.vecs · []) (denotSpace_agree _ hs)
      | tprod _ _ =>
          simp only [denotBasis]; exact congrArg (BasisDenot.vecs · []) (denotSpace_agree _ hs)
      | ker s₀ s₁ e =>
          unfold Space.fv at hs
          have hd₀ := denotSpace_agree s₀ hs.of_union_left.of_union_left
          have hd₁ := denotSpace_agree s₁ hs.of_union_left.of_union_right
          have he := denotTerm_agree e hs.of_union_right
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvLeft V₀ V₁ f (fun μ => decide (μ = 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₀ (LinearMap.ker f)) (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ₁ (.proj (.ker s₀ s₁ e) b₀ b₁)
              = F (denotSpace σ₁ s₀) (denotSpace σ₁ s₁) (denotTerm σ₁ e)
                  (denotBasis σ₁ b₀) (denotBasis σ₁ b₁) := by
            simp only [denotBasis, F]
          have hR : denotBasis σ₂ (.proj (.ker s₀ s₁ e) b₀ b₁)
              = F (denotSpace σ₂ s₀) (denotSpace σ₂ s₁) (denotTerm σ₂ e)
                  (denotBasis σ₂ b₀) (denotBasis σ₂ b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
      | coker s₀ s₁ e =>
          unfold Space.fv at hs
          have hd₀ := denotSpace_agree s₀ hs.of_union_left.of_union_left
          have hd₁ := denotSpace_agree s₁ hs.of_union_left.of_union_right
          have he := denotTerm_agree e hs.of_union_right
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvLeft V₀ V₁ f (fun μ => decide (μ ≠ 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₀ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)))
                (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ₁ (.proj (.coker s₀ s₁ e) b₀ b₁)
              = F (denotSpace σ₁ s₀) (denotSpace σ₁ s₁) (denotTerm σ₁ e)
                  (denotBasis σ₁ b₀) (denotBasis σ₁ b₁) := by
            simp only [denotBasis, F]
          have hR : denotBasis σ₂ (.proj (.coker s₀ s₁ e) b₀ b₁)
              = F (denotSpace σ₂ s₀) (denotSpace σ₂ s₁) (denotTerm σ₂ e)
                  (denotBasis σ₂ b₀) (denotBasis σ₂ b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
      | img s₀ s₁ e =>
          unfold Space.fv at hs
          have hd₀ := denotSpace_agree s₀ hs.of_union_left.of_union_left
          have hd₁ := denotSpace_agree s₁ hs.of_union_left.of_union_right
          have he := denotTerm_agree e hs.of_union_right
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvRight V₀ V₁ f (fun μ => decide (μ ≠ 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₁ (LinearMap.range f)) (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ₁ (.proj (.img s₀ s₁ e) b₀ b₁)
              = F (denotSpace σ₁ s₀) (denotSpace σ₁ s₁) (denotTerm σ₁ e)
                  (denotBasis σ₁ b₀) (denotBasis σ₁ b₁) := by
            simp only [denotBasis, F]
          have hR : denotBasis σ₂ (.proj (.img s₀ s₁ e) b₀ b₁)
              = F (denotSpace σ₂ s₀) (denotSpace σ₂ s₁) (denotTerm σ₂ e)
                  (denotBasis σ₂ b₀) (denotBasis σ₂ b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
      | coimg s₀ s₁ e =>
          unfold Space.fv at hs
          have hd₀ := denotSpace_agree s₀ hs.of_union_left.of_union_left
          have hd₁ := denotSpace_agree s₁ hs.of_union_left.of_union_right
          have he := denotTerm_agree e hs.of_union_right
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvRight V₀ V₁ f (fun μ => decide (μ = 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₁ (Submodule.orthRel V₁.innerProduct (LinearMap.range f)))
                (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ₁ (.proj (.coimg s₀ s₁ e) b₀ b₁)
              = F (denotSpace σ₁ s₀) (denotSpace σ₁ s₁) (denotTerm σ₁ e)
                  (denotBasis σ₁ b₀) (denotBasis σ₁ b₁) := by
            simp only [denotBasis, F]
          have hR : denotBasis σ₂ (.proj (.coimg s₀ s₁ e) b₀ b₁)
              = F (denotSpace σ₂ s₀) (denotSpace σ₂ s₁) (denotTerm σ₂ e)
                  (denotBasis σ₂ b₀) (denotBasis σ₂ b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
  | .image b, σ₁, σ₂, h => by
      unfold Basis.fv at h
      have hb := denotBasis_agree b h
      have hsof : σ₁.AgreeOn σ₂ (Space.fv (Basis.sof b)) := h.mono (Basis.fv_sof_subset b)
      have hsofimg : denotSpace σ₁ (Basis.sof (.image b)) = denotSpace σ₂ (Basis.sof (.image b)) :=
        denotSpace_agree _ (h.mono (Basis.fv_sof_subset (.image b)))
      -- the non-coker fallback is `.vecs (denotSpace σ (sof (.image b))) []`,
      -- handled uniformly by `.vecs · []` congruence at `hsofimg`.
      let G : HSpace → BasisDenot := fun V => BasisDenot.vecs V []
      cases hsofeq : Basis.sof b with
      | empty =>
          have e₁ : denotBasis σ₁ (.image b) = G (denotSpace σ₁ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          have e₂ : denotBasis σ₂ (.image b) = G (denotSpace σ₂ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          rw [e₁, e₂]; exact congrArg G hsofimg
      | real =>
          have e₁ : denotBasis σ₁ (.image b) = G (denotSpace σ₁ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          have e₂ : denotBasis σ₂ (.image b) = G (denotSpace σ₂ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          rw [e₁, e₂]; exact congrArg G hsofimg
      | dual _ =>
          have e₁ : denotBasis σ₁ (.image b) = G (denotSpace σ₁ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          have e₂ : denotBasis σ₂ (.image b) = G (denotSpace σ₂ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          rw [e₁, e₂]; exact congrArg G hsofimg
      | dsum _ _ =>
          have e₁ : denotBasis σ₁ (.image b) = G (denotSpace σ₁ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          have e₂ : denotBasis σ₂ (.image b) = G (denotSpace σ₂ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          rw [e₁, e₂]; exact congrArg G hsofimg
      | tprod _ _ =>
          have e₁ : denotBasis σ₁ (.image b) = G (denotSpace σ₁ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          have e₂ : denotBasis σ₂ (.image b) = G (denotSpace σ₂ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          rw [e₁, e₂]; exact congrArg G hsofimg
      | ker _ _ _ =>
          have e₁ : denotBasis σ₁ (.image b) = G (denotSpace σ₁ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          have e₂ : denotBasis σ₂ (.image b) = G (denotSpace σ₂ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          rw [e₁, e₂]; exact congrArg G hsofimg
      | coker s₀ s₁ e =>
          rw [hsofeq] at hsof
          unfold Space.fv at hsof
          have hd₀ := denotSpace_agree s₀ hsof.of_union_left.of_union_left
          have hd₁ := denotSpace_agree s₁ hsof.of_union_left.of_union_right
          have he := denotTerm_agree e hsof.of_union_right
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d =>
              BasisDenot.vecs (V₁.ofSubmodule (DVal.asLinMap V₀ V₁ c).range)
                ((BasisDenot.atSpace (V₀.ofSubmodule
                    (Submodule.orthRel V₀.innerProduct (DVal.asLinMap V₀ V₁ c).ker)) d).map
                  (fun w => ⟨(DVal.asLinMap V₀ V₁ c) (Subtype.val w),
                    LinearMap.mem_range_self _ _⟩))
          have hL : denotBasis σ₁ (.image b)
              = F (denotSpace σ₁ s₀) (denotSpace σ₁ s₁) (denotTerm σ₁ e) (denotBasis σ₁ b) := by
            simp only [denotBasis, F]; rw [hsofeq]
          have hR : denotBasis σ₂ (.image b)
              = F (denotSpace σ₂ s₀) (denotSpace σ₂ s₁) (denotTerm σ₂ e) (denotBasis σ₂ b) := by
            simp only [denotBasis, F]; rw [hsofeq]
          rw [hL, hR, hd₀, hd₁, he, hb]
      | img _ _ _ =>
          have e₁ : denotBasis σ₁ (.image b) = G (denotSpace σ₁ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          have e₂ : denotBasis σ₂ (.image b) = G (denotSpace σ₂ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          rw [e₁, e₂]; exact congrArg G hsofimg
      | coimg _ _ _ =>
          have e₁ : denotBasis σ₁ (.image b) = G (denotSpace σ₁ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          have e₂ : denotBasis σ₂ (.image b) = G (denotSpace σ₂ (Basis.sof (.image b))) := by
            simp only [denotBasis, G]; rw [hsofeq]
          rw [e₁, e₂]; exact congrArg G hsofimg
  | .terms s es b, σ₁, σ₂, h => by
      unfold Basis.fv at h
      have hs : σ₁.AgreeOn σ₂ (Space.fv s) := h.of_union_left.of_union_left
      have hbfv : σ₁.AgreeOn σ₂ (Basis.fv b) := h.of_union_left.of_union_right
      have hes : σ₁.AgreeOn σ₂ (Term.fvList es) := h.of_union_right
      have hd := denotSpace_agree s hs
      have hb := denotBasis_agree b hbfv
      have hesmap : (es.map (fun e => denotTerm σ₁ e)) = (es.map (fun e => denotTerm σ₂ e)) := by
        apply List.map_congr_left
        intro e hmem
        exact denotTerm_agree e (hes.mono (fun a ha => Term.mem_fvList.mpr ⟨e, hmem, ha⟩))
      let F : (V : HSpace) → List DVal → BasisDenot → BasisDenot :=
        fun V terms d =>
          .vecs V (V.lexInd ((terms.map (fun t => t.atSpace V)) ++ (d.atSpace V)))
      have hL : denotBasis σ₁ (.terms s es b)
          = F (denotSpace σ₁ s) (es.map (fun e => denotTerm σ₁ e)) (denotBasis σ₁ b) := by
        simp only [denotBasis, F, List.map_map, Function.comp_def]
      have hR : denotBasis σ₂ (.terms s es b)
          = F (denotSpace σ₂ s) (es.map (fun e => denotTerm σ₂ e)) (denotBasis σ₂ b) := by
        simp only [denotBasis, F, List.map_map, Function.comp_def]
      rw [hL, hR, hd, hesmap, hb]
  | .frame b₀ b₁, σ₁, σ₂, h => by
      unfold Basis.fv at h
      have h₀ : σ₁.AgreeOn σ₂ (Basis.fv b₀) := h.of_union_left
      have h₁ : σ₁.AgreeOn σ₂ (Basis.fv b₁) := h.of_union_right
      have htof : denotTy σ₁ (Basis.tof b₀) = denotTy σ₂ (Basis.tof b₀) :=
        denotTy_agree _ (h₀.mono (Basis.fv_tof_subset b₀))
      -- the per-fiber bodies agree (same fresh open name, AgreeOn extended).
      have hbody : ∀ y, denotBasis (σ₁.bind (Basis.freshFor b₁)
            ((denotTy σ₁ (Basis.tof b₀)).embed y)) (Basis.openVar (Basis.freshFor b₁) b₁)
          = denotBasis (σ₂.bind (Basis.freshFor b₁)
            ((denotTy σ₁ (Basis.tof b₀)).embed y)) (Basis.openVar (Basis.freshFor b₁) b₁) :=
        fun y => denotBasis_agree (Basis.openVar (Basis.freshFor b₁) b₁)
          ((h₁.mono (Basis.fv_openVar_erase_subset (Basis.freshFor b₁) b₁)).bind_erase _)
      -- domain bases agree (recursive FV-irrelevance on `b₀`).
      have hdom : denotBasis σ₁ b₀ = denotBasis σ₂ b₀ := denotBasis_agree b₀ h₀
      let F : (T : HType) → BasisDenot → ((y : T.El) → BasisDenot) → BasisDenot :=
        fun T domB fam => BasisDenot.frame T.El domB (fun y => fam y)
      have hL : denotBasis σ₁ (.frame b₀ b₁)
          = F (denotTy σ₁ (Basis.tof b₀)) (denotBasis σ₁ b₀) (fun y =>
              denotBasis (σ₁.bind (Basis.freshFor b₁) ((denotTy σ₁ (Basis.tof b₀)).embed y))
                (Basis.openVar (Basis.freshFor b₁) b₁)) := by simp only [denotBasis, F]
      have hR : denotBasis σ₂ (.frame b₀ b₁)
          = F (denotTy σ₂ (Basis.tof b₀)) (denotBasis σ₂ b₀) (fun y =>
              denotBasis (σ₂.bind (Basis.freshFor b₁) ((denotTy σ₂ (Basis.tof b₀)).embed y))
                (Basis.openVar (Basis.freshFor b₁) b₁)) := by simp only [denotBasis, F]
      rw [hL, hR, ← htof, ← hdom]
      exact congrArg (F (denotTy σ₁ (Basis.tof b₀)) (denotBasis σ₁ b₀)) (funext hbody)
  termination_by b => Basis.size b
  decreasing_by
    all_goals first
      | (simp only [Basis.size]; omega)
      | (simp only [Basis.size_openVar]; simp only [Basis.size]; omega)

/-! ### `size`-preservation under variable-for-variable substitution.

`Basis.subst x (.var w)` swaps the free name `x` for the free name `w`; both
are `size`-1 leaves, so the measure is preserved. This backs the
`Basis.size`-recursion of `denotBasis_subst` (whose `.frame` arm recurses on a
`subst`-then-`openVar`'d sub-basis). -/

mutual
private theorem Space.size_subst_var (x w : Name) :
    ∀ s : Space, Space.size (Space.subst x (.var w) s) = Space.size s
  | .empty => rfl
  | .real => rfl
  | .dual s => by simp [Space.subst, Space.size, Space.size_subst_var x w s]
  | .dsum s₀ s₁ => by
      simp [Space.subst, Space.size, Space.size_subst_var x w s₀,
        Space.size_subst_var x w s₁]
  | .tprod s₀ s₁ => by
      simp [Space.subst, Space.size, Space.size_subst_var x w s₀,
        Space.size_subst_var x w s₁]
  | .ker s₀ s₁ e => by
      simp [Space.subst, Space.size, Space.size_subst_var x w s₀,
        Space.size_subst_var x w s₁, Term.size_subst_var x w e]
  | .coker s₀ s₁ e => by
      simp [Space.subst, Space.size, Space.size_subst_var x w s₀,
        Space.size_subst_var x w s₁, Term.size_subst_var x w e]
  | .img s₀ s₁ e => by
      simp [Space.subst, Space.size, Space.size_subst_var x w s₀,
        Space.size_subst_var x w s₁, Term.size_subst_var x w e]
  | .coimg s₀ s₁ e => by
      simp [Space.subst, Space.size, Space.size_subst_var x w s₀,
        Space.size_subst_var x w s₁, Term.size_subst_var x w e]

private theorem Ty.size_subst_var (x w : Name) :
    ∀ τ : Ty, Ty.size (Ty.subst x (.var w) τ) = Ty.size τ
  | .space s => by simp [Ty.subst, Ty.size, Space.size_subst_var x w s]
  | .piTy τ₀ τ₁ => by
      simp [Ty.subst, Ty.size, Ty.size_subst_var x w τ₀, Ty.size_subst_var x w τ₁]

private theorem Term.size_subst_var (x w : Name) :
    ∀ e : Term, Term.size (Term.subst x (.var w) e) = Term.size e
  | .bvar _ => rfl
  | .var y => by
      by_cases h : x = y <;> simp [Term.subst, Term.size, h]
  | .real _ => rfl
  | .zero s => by simp [Term.subst, Term.size, Space.size_subst_var x w s]
  | .add e₀ e₁ => by
      simp [Term.subst, Term.size, Term.size_subst_var x w e₀, Term.size_subst_var x w e₁]
  | .smul e₀ e₁ => by
      simp [Term.subst, Term.size, Term.size_subst_var x w e₀, Term.size_subst_var x w e₁]
  | .dsumE e₀ e₁ => by
      simp [Term.subst, Term.size, Term.size_subst_var x w e₀, Term.size_subst_var x w e₁]
  | .tprodE e₀ e₁ => by
      simp [Term.subst, Term.size, Term.size_subst_var x w e₀, Term.size_subst_var x w e₁]
  | .inner s => by simp [Term.subst, Term.size, Space.size_subst_var x w s]
  | .embed s => by simp [Term.subst, Term.size, Space.size_subst_var x w s]
  | .pinvT s₀ s₁ e => by
      simp [Term.subst, Term.size, Space.size_subst_var x w s₀,
        Space.size_subst_var x w s₁, Term.size_subst_var x w e]
  | .pinvD s e => by
      simp [Term.subst, Term.size, Space.size_subst_var x w s, Term.size_subst_var x w e]
  | .llam s₀ s e => by
      simp [Term.subst, Term.size, Space.size_subst_var x w s₀,
        Space.size_subst_var x w s, Term.size_subst_var x w e]
  | .nllam τ e => by
      simp [Term.subst, Term.size, Ty.size_subst_var x w τ, Term.size_subst_var x w e]
  | .appL s₀ s₁ e₀ e₁ => by
      simp [Term.subst, Term.size, Space.size_subst_var x w s₀,
        Space.size_subst_var x w s₁, Term.size_subst_var x w e₀, Term.size_subst_var x w e₁]
  | .appI s e₀ e₁ => by
      simp [Term.subst, Term.size, Space.size_subst_var x w s,
        Term.size_subst_var x w e₀, Term.size_subst_var x w e₁]
  | .appN e₀ e₁ => by
      simp [Term.subst, Term.size, Term.size_subst_var x w e₀, Term.size_subst_var x w e₁]
end

private theorem Basis.size_subst_var (x w : Name) :
    ∀ b : Basis, Basis.size (Basis.subst x (.var w) b) = Basis.size b
  | .empty => rfl
  | .one => rfl
  | .dual b => by simp [Basis.subst, Basis.size, Basis.size_subst_var x w b]
  | .dsum b₀ b₁ => by
      simp [Basis.subst, Basis.size, Basis.size_subst_var x w b₀, Basis.size_subst_var x w b₁]
  | .tprod b₀ b₁ => by
      simp [Basis.subst, Basis.size, Basis.size_subst_var x w b₀, Basis.size_subst_var x w b₁]
  | .proj s b₀ b₁ => by
      simp [Basis.subst, Basis.size, Space.size_subst_var x w s,
        Basis.size_subst_var x w b₀, Basis.size_subst_var x w b₁]
  | .image b => by simp [Basis.subst, Basis.size, Basis.size_subst_var x w b]
  | .terms s es b => by
      simp only [Basis.subst, Basis.size, Space.size_subst_var x w s,
        Basis.size_subst_var x w b]
      have hmap : (es.map (Term.subst x (.var w))).map Term.size = es.map Term.size :=
        by rw [List.map_map]; exact List.map_congr_left (fun e _ => Term.size_subst_var x w e)
      rw [hmap]
  | .frame b₀ b₁ => by
      simp [Basis.subst, Basis.size, Basis.size_subst_var x w b₀, Basis.size_subst_var x w b₁]

/-! ### Forward `fv` membership under `subst x (.var w)`.

If `x` was free, the replacement name `w` becomes free after substitution. -/

mutual
private theorem Space.mem_fv_subst_var {x w : Name} :
    ∀ {s : Space}, x ∈ Space.fv s → w ∈ Space.fv (Space.subst x (.var w) s)
  | .empty, h => by simp only [Space.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .real, h => by simp only [Space.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .dual s, h => by
      simp only [Space.fv] at h; simpa [Space.subst, Space.fv] using Space.mem_fv_subst_var h
  | .dsum s₀ s₁, h => by
      simp only [Space.fv, Finset.mem_union] at h
      rcases h with h | h
      · exact Finset.mem_union_left _ (Space.mem_fv_subst_var (s := s₀) h)
      · exact Finset.mem_union_right _ (Space.mem_fv_subst_var (s := s₁) h)
  | .tprod s₀ s₁, h => by
      simp only [Space.fv, Finset.mem_union] at h
      rcases h with h | h
      · exact Finset.mem_union_left _ (Space.mem_fv_subst_var (s := s₀) h)
      · exact Finset.mem_union_right _ (Space.mem_fv_subst_var (s := s₁) h)
  | .ker s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union] at h
      simp only [Space.subst, Space.fv, Finset.mem_union]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.mem_fv_subst_var (s := s₀) h))
      · exact Or.inl (Or.inr (Space.mem_fv_subst_var (s := s₁) h))
      · exact Or.inr (Term.mem_fv_subst_var (e := e) h)
  | .coker s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union] at h
      simp only [Space.subst, Space.fv, Finset.mem_union]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.mem_fv_subst_var (s := s₀) h))
      · exact Or.inl (Or.inr (Space.mem_fv_subst_var (s := s₁) h))
      · exact Or.inr (Term.mem_fv_subst_var (e := e) h)
  | .img s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union] at h
      simp only [Space.subst, Space.fv, Finset.mem_union]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.mem_fv_subst_var (s := s₀) h))
      · exact Or.inl (Or.inr (Space.mem_fv_subst_var (s := s₁) h))
      · exact Or.inr (Term.mem_fv_subst_var (e := e) h)
  | .coimg s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union] at h
      simp only [Space.subst, Space.fv, Finset.mem_union]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.mem_fv_subst_var (s := s₀) h))
      · exact Or.inl (Or.inr (Space.mem_fv_subst_var (s := s₁) h))
      · exact Or.inr (Term.mem_fv_subst_var (e := e) h)

private theorem Term.mem_fv_subst_var {x w : Name} :
    ∀ {e : Term}, x ∈ Term.fv e → w ∈ Term.fv (Term.subst x (.var w) e)
  | .bvar _, h => by simp only [Term.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .var y, h => by
      simp only [Term.fv, Finset.mem_singleton] at h; subst h
      simp [Term.subst, Term.fv]
  | .real _, h => by simp only [Term.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .zero s, h => by simp only [Term.fv] at h; simpa [Term.subst, Term.fv] using Space.mem_fv_subst_var (s := s) h
  | .inner s, h => by simp only [Term.fv] at h; simpa [Term.subst, Term.fv] using Space.mem_fv_subst_var (s := s) h
  | .embed s, h => by simp only [Term.fv] at h; simpa [Term.subst, Term.fv] using Space.mem_fv_subst_var (s := s) h
  | .add e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Term.mem_fv_subst_var (e := e₀) h)
      · exact Or.inr (Term.mem_fv_subst_var (e := e₁) h)
  | .smul e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Term.mem_fv_subst_var (e := e₀) h)
      · exact Or.inr (Term.mem_fv_subst_var (e := e₁) h)
  | .dsumE e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Term.mem_fv_subst_var (e := e₀) h)
      · exact Or.inr (Term.mem_fv_subst_var (e := e₁) h)
  | .tprodE e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Term.mem_fv_subst_var (e := e₀) h)
      · exact Or.inr (Term.mem_fv_subst_var (e := e₁) h)
  | .appN e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Term.mem_fv_subst_var (e := e₀) h)
      · exact Or.inr (Term.mem_fv_subst_var (e := e₁) h)
  | .pinvD s e, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Space.mem_fv_subst_var (s := s) h)
      · exact Or.inr (Term.mem_fv_subst_var (e := e) h)
  | .pinvT s₀ s₁ e, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.mem_fv_subst_var (s := s₀) h))
      · exact Or.inl (Or.inr (Space.mem_fv_subst_var (s := s₁) h))
      · exact Or.inr (Term.mem_fv_subst_var (e := e) h)
  | .llam s₀ s e, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.mem_fv_subst_var (s := s₀) h))
      · exact Or.inl (Or.inr (Space.mem_fv_subst_var (s := s) h))
      · exact Or.inr (Term.mem_fv_subst_var (e := e) h)
  | .nllam τ e, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Ty.mem_fv_subst_var (τ := τ) h)
      · exact Or.inr (Term.mem_fv_subst_var (e := e) h)
  | .appL s₀ s₁ e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Space.mem_fv_subst_var (s := s₀) h)))
      · exact Or.inl (Or.inl (Or.inr (Space.mem_fv_subst_var (s := s₁) h)))
      · exact Or.inl (Or.inr (Term.mem_fv_subst_var (e := e₀) h))
      · exact Or.inr (Term.mem_fv_subst_var (e := e₁) h)
  | .appI s e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.mem_fv_subst_var (s := s) h))
      · exact Or.inl (Or.inr (Term.mem_fv_subst_var (e := e₀) h))
      · exact Or.inr (Term.mem_fv_subst_var (e := e₁) h)

private theorem Ty.mem_fv_subst_var {x w : Name} :
    ∀ {τ : Ty}, x ∈ Ty.fv τ → w ∈ Ty.fv (Ty.subst x (.var w) τ)
  | .space s, h => by simp only [Ty.fv] at h; simpa [Ty.subst, Ty.fv] using Space.mem_fv_subst_var (s := s) h
  | .piTy τ₀ τ₁, h => by
      simp only [Ty.fv, Finset.mem_union] at h
      simp only [Ty.subst, Ty.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Ty.mem_fv_subst_var (τ := τ₀) h)
      · exact Or.inr (Ty.mem_fv_subst_var (τ := τ₁) h)
end

private theorem Term.mem_fvList_subst_var {x w : Name} :
    ∀ {es : List Term}, x ∈ Term.fvList es →
      w ∈ Term.fvList (es.map (Term.subst x (.var w)))
  | e :: es, h => by
      simp only [Term.fvList, Finset.mem_union] at h
      simp only [List.map_cons, Term.fvList, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Term.mem_fv_subst_var (e := e) h)
      · exact Or.inr (Term.mem_fvList_subst_var (es := es) h)

private theorem Basis.mem_fv_subst_var {x w : Name} :
    ∀ {b : Basis}, x ∈ Basis.fv b → w ∈ Basis.fv (Basis.subst x (.var w) b)
  | .empty, h => by simp only [Basis.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .one, h => by simp only [Basis.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .dual b, h => by
      simp only [Basis.fv] at h; simpa [Basis.subst, Basis.fv] using Basis.mem_fv_subst_var (b := b) h
  | .image b, h => by
      simp only [Basis.fv] at h; simpa [Basis.subst, Basis.fv] using Basis.mem_fv_subst_var (b := b) h
  | .dsum b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union] at h
      simp only [Basis.subst, Basis.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Basis.mem_fv_subst_var (b := b₀) h)
      · exact Or.inr (Basis.mem_fv_subst_var (b := b₁) h)
  | .tprod b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union] at h
      simp only [Basis.subst, Basis.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Basis.mem_fv_subst_var (b := b₀) h)
      · exact Or.inr (Basis.mem_fv_subst_var (b := b₁) h)
  | .frame b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union] at h
      simp only [Basis.subst, Basis.fv, Finset.mem_union]
      rcases h with h | h
      · exact Or.inl (Basis.mem_fv_subst_var (b := b₀) h)
      · exact Or.inr (Basis.mem_fv_subst_var (b := b₁) h)
  | .proj s b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union] at h
      simp only [Basis.subst, Basis.fv, Finset.mem_union]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.mem_fv_subst_var (s := s) h))
      · exact Or.inl (Or.inr (Basis.mem_fv_subst_var (b := b₀) h))
      · exact Or.inr (Basis.mem_fv_subst_var (b := b₁) h)
  | .terms s es b, h => by
      simp only [Basis.fv, Finset.mem_union] at h
      simp only [Basis.subst, Basis.fv, Finset.mem_union]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.mem_fv_subst_var (s := s) h))
      · exact Or.inl (Or.inr (Basis.mem_fv_subst_var (b := b) h))
      · exact Or.inr (Term.mem_fvList_subst_var (es := es) h)

/-! ### A free name `≠ x` survives `subst x (.var w)`. -/

mutual
private theorem Space.mem_fv_subst_var_of_ne {x w p : Name} (hpx : p ≠ x) :
    ∀ {s : Space}, p ∈ Space.fv s → p ∈ Space.fv (Space.subst x (.var w) s)
  | .empty, h => by simp only [Space.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .real, h => by simp only [Space.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .dual s, h => by
      simp only [Space.fv] at h
      simpa [Space.subst, Space.fv] using Space.mem_fv_subst_var_of_ne hpx (s := s) h
  | .dsum s₀ s₁, h => by
      simp only [Space.fv, Finset.mem_union] at h
      simp only [Space.subst, Space.fv, Finset.mem_union]
      exact h.imp (Space.mem_fv_subst_var_of_ne hpx (s := s₀))
        (Space.mem_fv_subst_var_of_ne hpx (s := s₁))
  | .tprod s₀ s₁, h => by
      simp only [Space.fv, Finset.mem_union] at h
      simp only [Space.subst, Space.fv, Finset.mem_union]
      exact h.imp (Space.mem_fv_subst_var_of_ne hpx (s := s₀))
        (Space.mem_fv_subst_var_of_ne hpx (s := s₁))
  | .ker s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union] at h
      simp only [Space.subst, Space.fv, Finset.mem_union]
      exact (h.imp (·.imp (Space.mem_fv_subst_var_of_ne hpx (s := s₀))
        (Space.mem_fv_subst_var_of_ne hpx (s := s₁))) (Term.mem_fv_subst_var_of_ne hpx (e := e)))
  | .coker s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union] at h
      simp only [Space.subst, Space.fv, Finset.mem_union]
      exact (h.imp (·.imp (Space.mem_fv_subst_var_of_ne hpx (s := s₀))
        (Space.mem_fv_subst_var_of_ne hpx (s := s₁))) (Term.mem_fv_subst_var_of_ne hpx (e := e)))
  | .img s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union] at h
      simp only [Space.subst, Space.fv, Finset.mem_union]
      exact (h.imp (·.imp (Space.mem_fv_subst_var_of_ne hpx (s := s₀))
        (Space.mem_fv_subst_var_of_ne hpx (s := s₁))) (Term.mem_fv_subst_var_of_ne hpx (e := e)))
  | .coimg s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union] at h
      simp only [Space.subst, Space.fv, Finset.mem_union]
      exact (h.imp (·.imp (Space.mem_fv_subst_var_of_ne hpx (s := s₀))
        (Space.mem_fv_subst_var_of_ne hpx (s := s₁))) (Term.mem_fv_subst_var_of_ne hpx (e := e)))

private theorem Term.mem_fv_subst_var_of_ne {x w p : Name} (hpx : p ≠ x) :
    ∀ {e : Term}, p ∈ Term.fv e → p ∈ Term.fv (Term.subst x (.var w) e)
  | .bvar _, h => by simp only [Term.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .var y, h => by
      simp only [Term.fv, Finset.mem_singleton] at h; subst h
      rw [Term.subst, if_neg (fun he => hpx he.symm)]; simp [Term.fv]
  | .real _, h => by simp only [Term.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .zero s, h => by simp only [Term.fv] at h
                     simpa [Term.subst, Term.fv] using Space.mem_fv_subst_var_of_ne hpx (s := s) h
  | .inner s, h => by simp only [Term.fv] at h
                      simpa [Term.subst, Term.fv] using Space.mem_fv_subst_var_of_ne hpx (s := s) h
  | .embed s, h => by simp only [Term.fv] at h
                      simpa [Term.subst, Term.fv] using Space.mem_fv_subst_var_of_ne hpx (s := s) h
  | .add e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact h.imp (Term.mem_fv_subst_var_of_ne hpx (e := e₀)) (Term.mem_fv_subst_var_of_ne hpx (e := e₁))
  | .smul e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact h.imp (Term.mem_fv_subst_var_of_ne hpx (e := e₀)) (Term.mem_fv_subst_var_of_ne hpx (e := e₁))
  | .dsumE e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact h.imp (Term.mem_fv_subst_var_of_ne hpx (e := e₀)) (Term.mem_fv_subst_var_of_ne hpx (e := e₁))
  | .tprodE e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact h.imp (Term.mem_fv_subst_var_of_ne hpx (e := e₀)) (Term.mem_fv_subst_var_of_ne hpx (e := e₁))
  | .appN e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact h.imp (Term.mem_fv_subst_var_of_ne hpx (e := e₀)) (Term.mem_fv_subst_var_of_ne hpx (e := e₁))
  | .pinvD s e, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact h.imp (Space.mem_fv_subst_var_of_ne hpx (s := s)) (Term.mem_fv_subst_var_of_ne hpx (e := e))
  | .pinvT s₀ s₁ e, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact (h.imp (·.imp (Space.mem_fv_subst_var_of_ne hpx (s := s₀))
        (Space.mem_fv_subst_var_of_ne hpx (s := s₁))) (Term.mem_fv_subst_var_of_ne hpx (e := e)))
  | .llam s₀ s e, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact (h.imp (·.imp (Space.mem_fv_subst_var_of_ne hpx (s := s₀))
        (Space.mem_fv_subst_var_of_ne hpx (s := s))) (Term.mem_fv_subst_var_of_ne hpx (e := e)))
  | .nllam τ e, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact h.imp (Ty.mem_fv_subst_var_of_ne hpx (τ := τ)) (Term.mem_fv_subst_var_of_ne hpx (e := e))
  | .appL s₀ s₁ e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact (h.imp (·.imp (·.imp (Space.mem_fv_subst_var_of_ne hpx (s := s₀))
        (Space.mem_fv_subst_var_of_ne hpx (s := s₁))) (Term.mem_fv_subst_var_of_ne hpx (e := e₀)))
        (Term.mem_fv_subst_var_of_ne hpx (e := e₁)))
  | .appI s e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union] at h
      simp only [Term.subst, Term.fv, Finset.mem_union]
      exact (h.imp (·.imp (Space.mem_fv_subst_var_of_ne hpx (s := s))
        (Term.mem_fv_subst_var_of_ne hpx (e := e₀))) (Term.mem_fv_subst_var_of_ne hpx (e := e₁)))

private theorem Ty.mem_fv_subst_var_of_ne {x w p : Name} (hpx : p ≠ x) :
    ∀ {τ : Ty}, p ∈ Ty.fv τ → p ∈ Ty.fv (Ty.subst x (.var w) τ)
  | .space s, h => by simp only [Ty.fv] at h
                      simpa [Ty.subst, Ty.fv] using Space.mem_fv_subst_var_of_ne hpx (s := s) h
  | .piTy τ₀ τ₁, h => by
      simp only [Ty.fv, Finset.mem_union] at h
      simp only [Ty.subst, Ty.fv, Finset.mem_union]
      exact h.imp (Ty.mem_fv_subst_var_of_ne hpx (τ := τ₀)) (Ty.mem_fv_subst_var_of_ne hpx (τ := τ₁))
end

private theorem Term.mem_fvList_subst_var_of_ne {x w p : Name} (hpx : p ≠ x) :
    ∀ {es : List Term}, p ∈ Term.fvList es →
      p ∈ Term.fvList (es.map (Term.subst x (.var w)))
  | e :: es, h => by
      simp only [Term.fvList, Finset.mem_union] at h
      simp only [List.map_cons, Term.fvList, Finset.mem_union]
      exact h.imp (Term.mem_fv_subst_var_of_ne hpx (e := e))
        (Term.mem_fvList_subst_var_of_ne hpx (es := es))

private theorem Basis.mem_fv_subst_var_of_ne {x w p : Name} (hpx : p ≠ x) :
    ∀ {b : Basis}, p ∈ Basis.fv b → p ∈ Basis.fv (Basis.subst x (.var w) b)
  | .empty, h => by simp only [Basis.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .one, h => by simp only [Basis.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .dual b, h => by
      simp only [Basis.fv] at h
      simpa [Basis.subst, Basis.fv] using Basis.mem_fv_subst_var_of_ne hpx (b := b) h
  | .image b, h => by
      simp only [Basis.fv] at h
      simpa [Basis.subst, Basis.fv] using Basis.mem_fv_subst_var_of_ne hpx (b := b) h
  | .dsum b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union] at h
      simp only [Basis.subst, Basis.fv, Finset.mem_union]
      exact h.imp (Basis.mem_fv_subst_var_of_ne hpx (b := b₀)) (Basis.mem_fv_subst_var_of_ne hpx (b := b₁))
  | .tprod b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union] at h
      simp only [Basis.subst, Basis.fv, Finset.mem_union]
      exact h.imp (Basis.mem_fv_subst_var_of_ne hpx (b := b₀)) (Basis.mem_fv_subst_var_of_ne hpx (b := b₁))
  | .frame b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union] at h
      simp only [Basis.subst, Basis.fv, Finset.mem_union]
      exact h.imp (Basis.mem_fv_subst_var_of_ne hpx (b := b₀)) (Basis.mem_fv_subst_var_of_ne hpx (b := b₁))
  | .proj s b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union] at h
      simp only [Basis.subst, Basis.fv, Finset.mem_union]
      exact (h.imp (·.imp (Space.mem_fv_subst_var_of_ne hpx (s := s))
        (Basis.mem_fv_subst_var_of_ne hpx (b := b₀))) (Basis.mem_fv_subst_var_of_ne hpx (b := b₁)))
  | .terms s es b, h => by
      simp only [Basis.fv, Finset.mem_union] at h
      simp only [Basis.subst, Basis.fv, Finset.mem_union]
      exact (h.imp (·.imp (Space.mem_fv_subst_var_of_ne hpx (s := s))
        (Basis.mem_fv_subst_var_of_ne hpx (b := b))) (Term.mem_fvList_subst_var_of_ne hpx (es := es)))

/-- `σ.bind x v` lookup of `x` gives `v`.  This adequacy-local utility is public because later
    transport and operational modules use the same environment computation. -/
theorem denotTerm_bind_self (σ : DEnv) (x : Name) (v : DVal) :
    denotTerm (σ.bind x v) (.var x) = v := by
  show ((σ.bind x v).vars.lookup x).getD DVal.default = v
  unfold DEnv.bind
  simp [Finmap.lookup_insert]

/-- Two binds at names fresh for `S` leave variable-lookups on `S` unchanged. -/
private theorem DEnv.AgreeOn.bind2_left_of_not_mem {σ : DEnv} {S : Finset Name}
    {z a : Name} {w₁ w₂ : DVal} (hz : z ∉ S) (ha : a ∉ S) :
    ((σ.bind z w₁).bind a w₂).AgreeOn σ S where
  vars y hy := by
    have hy_a : y ≠ a := fun heq => ha (heq ▸ hy)
    have hy_z : y ≠ z := fun heq => hz (heq ▸ hy)
    simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hy_a,
      Finmap.lookup_insert_of_ne _ hy_z]

/-- `denotBasis` at `.image b` when `sof b` is NOT a `.coker`: the dependent
    `match _h_sof : Basis.sof b` collapses to the constant fallback. -/
private theorem denotBasis_image_noncoker (σ : DEnv) (b : Basis)
    (hsof : ∀ s₀ s₁ e, Basis.sof b ≠ .coker s₀ s₁ e) :
    denotBasis σ (.image b) = .vecs (denotSpace σ (Basis.sof (.image b))) [] := by
  conv_lhs => rw [denotBasis]
  split
  · rename_i s₀ s₁ e hmatch
    exact absurd hmatch (hsof s₀ s₁ e)
  · rfl

/-- `denotBasis` commutes with `Basis.subst`-by-an-`lc` term through the env:
    substituting `u` for `x` inside the basis equals binding `x ↦ ⟦u⟧σ` in `σ`.

    Factored from `denotSpaceAux_subst`/`denotTyAux_subst`/`denotTermAux_subst`
    (`GLang/Proofs/Source/Substitution.lean`). Every recursive position is a congruence under
    the opaque-`F` device (so the dependent `.proj`/`.image` casts hide behind a
    top-level function), with the leaf reads rewritten by `denotSpace_subst`/
    `denotTy_subst`/`denotTerm_subst` plus `Basis.sof_subst`/`Basis.tof_subst`.

    The `.image` arm reduces the dependent `match _h_sof : Basis.sof b` via
    `denotBasis_image_unfold` (no `rw`/`simp` on the resistant `match`); the
    `.frame` arm reconciles the two distinct canonical fresh names
    (`freshFor (subst x u b₁)` vs `freshFor b₁`) by renaming BOTH opened fibers
    to a common fully-fresh `a` through two size-decreasing recursive
    `denotBasis_subst` calls (each on `openVar _ b₁`, `size b₁ < size (frame …)`),
    then closing the residual env mismatch with `denotBasis_agree`. -/
private theorem denotBasis_subst (x w : Name) :
    ∀ (b : Basis) (σ : DEnv),
      denotBasis σ (Basis.subst x (.var w) b)
        = denotBasis (σ.bind x (denotTerm σ (.var w))) b
  | .empty, _ => by simp only [Basis.subst, denotBasis]
  | .one, _ => by simp only [Basis.subst, denotBasis]
  | .dual b, σ => by
      have hb := denotBasis_subst x w b σ
      have hsof : denotSpace σ (Basis.sof (Basis.subst x (.var w) b))
          = denotSpace (σ.bind x (denotTerm σ (.var w))) (Basis.sof b) := by
        rw [Basis.sof_subst, denotSpace_subst (x := x) (u := .var w) Term.lc.var]
      let F : (V : HSpace) → BasisDenot → BasisDenot :=
        fun V d => .vecs (HSpace.dual V) (V.dualOfList (d.atSpace V))
      have hL : denotBasis σ (Basis.subst x (.var w) (.dual b))
          = F (denotSpace σ (Basis.sof (Basis.subst x (.var w) b)))
              (denotBasis σ (Basis.subst x (.var w) b)) := by
        simp only [Basis.subst, denotBasis, F]
      have hR : denotBasis (σ.bind x (denotTerm σ (.var w))) (.dual b)
          = F (denotSpace (σ.bind x (denotTerm σ (.var w))) (Basis.sof b))
              (denotBasis (σ.bind x (denotTerm σ (.var w))) b) := by
        simp only [denotBasis, F]
      rw [hL, hR, hsof, hb]
  | .dsum b₀ b₁, σ => by
      have hb₀ := denotBasis_subst x w b₀ σ
      have hb₁ := denotBasis_subst x w b₁ σ
      have hs₀ : denotSpace σ (Basis.sof (Basis.subst x (.var w) b₀))
          = denotSpace (σ.bind x (denotTerm σ (.var w))) (Basis.sof b₀) := by
        rw [Basis.sof_subst, denotSpace_subst (x := x) (u := .var w) Term.lc.var]
      have hs₁ : denotSpace σ (Basis.sof (Basis.subst x (.var w) b₁))
          = denotSpace (σ.bind x (denotTerm σ (.var w))) (Basis.sof b₁) := by
        rw [Basis.sof_subst, denotSpace_subst (x := x) (u := .var w) Term.lc.var]
      let F : (V₀ V₁ : HSpace) → BasisDenot → BasisDenot → BasisDenot :=
        fun V₀ V₁ d₀ d₁ =>
          .vecs (HSpace.dsum V₀ V₁) (HSpace.dsumOfLists V₀ V₁ (d₀.atSpace V₀) (d₁.atSpace V₁))
      have hL : denotBasis σ (Basis.subst x (.var w) (.dsum b₀ b₁))
          = F (denotSpace σ (Basis.sof (Basis.subst x (.var w) b₀)))
              (denotSpace σ (Basis.sof (Basis.subst x (.var w) b₁)))
              (denotBasis σ (Basis.subst x (.var w) b₀)) (denotBasis σ (Basis.subst x (.var w) b₁)) := by
        simp only [Basis.subst, denotBasis, F]
      have hR : denotBasis (σ.bind x (denotTerm σ (.var w))) (.dsum b₀ b₁)
          = F (denotSpace (σ.bind x (denotTerm σ (.var w))) (Basis.sof b₀))
              (denotSpace (σ.bind x (denotTerm σ (.var w))) (Basis.sof b₁))
              (denotBasis (σ.bind x (denotTerm σ (.var w))) b₀)
              (denotBasis (σ.bind x (denotTerm σ (.var w))) b₁) := by
        simp only [denotBasis, F]
      rw [hL, hR, hs₀, hs₁, hb₀, hb₁]
  | .tprod b₀ b₁, σ => by
      have hb₀ := denotBasis_subst x w b₀ σ
      have hb₁ := denotBasis_subst x w b₁ σ
      have hs₀ : denotSpace σ (Basis.sof (Basis.subst x (.var w) b₀))
          = denotSpace (σ.bind x (denotTerm σ (.var w))) (Basis.sof b₀) := by
        rw [Basis.sof_subst, denotSpace_subst (x := x) (u := .var w) Term.lc.var]
      have hs₁ : denotSpace σ (Basis.sof (Basis.subst x (.var w) b₁))
          = denotSpace (σ.bind x (denotTerm σ (.var w))) (Basis.sof b₁) := by
        rw [Basis.sof_subst, denotSpace_subst (x := x) (u := .var w) Term.lc.var]
      let F : (V₀ V₁ : HSpace) → BasisDenot → BasisDenot → BasisDenot :=
        fun V₀ V₁ d₀ d₁ =>
          .vecs (HSpace.tprod V₀ V₁) (HSpace.tprodOfLists V₀ V₁ (d₀.atSpace V₀) (d₁.atSpace V₁))
      have hL : denotBasis σ (Basis.subst x (.var w) (.tprod b₀ b₁))
          = F (denotSpace σ (Basis.sof (Basis.subst x (.var w) b₀)))
              (denotSpace σ (Basis.sof (Basis.subst x (.var w) b₁)))
              (denotBasis σ (Basis.subst x (.var w) b₀)) (denotBasis σ (Basis.subst x (.var w) b₁)) := by
        simp only [Basis.subst, denotBasis, F]
      have hR : denotBasis (σ.bind x (denotTerm σ (.var w))) (.tprod b₀ b₁)
          = F (denotSpace (σ.bind x (denotTerm σ (.var w))) (Basis.sof b₀))
              (denotSpace (σ.bind x (denotTerm σ (.var w))) (Basis.sof b₁))
              (denotBasis (σ.bind x (denotTerm σ (.var w))) b₀)
              (denotBasis (σ.bind x (denotTerm σ (.var w))) b₁) := by
        simp only [denotBasis, F]
      rw [hL, hR, hs₀, hs₁, hb₀, hb₁]
  | .proj s b₀ b₁, σ => by
      have hb₀ := denotBasis_subst x w b₀ σ
      have hb₁ := denotBasis_subst x w b₁ σ
      cases s with
      | empty =>
          simp only [Basis.subst, denotBasis, Space.subst]
          exact congrArg (BasisDenot.vecs · []) (denotSpace_subst (x := x) (u := .var w) Term.lc.var σ .empty)
      | real =>
          simp only [Basis.subst, denotBasis, Space.subst]
          exact congrArg (BasisDenot.vecs · []) (denotSpace_subst (x := x) (u := .var w) Term.lc.var σ .real)
      | dual s' =>
          simp only [Basis.subst, denotBasis, Space.subst]
          exact congrArg (BasisDenot.vecs · []) (denotSpace_subst (x := x) (u := .var w) Term.lc.var σ (.dual s'))
      | dsum s' s'' =>
          simp only [Basis.subst, denotBasis, Space.subst]
          exact congrArg (BasisDenot.vecs · []) (denotSpace_subst (x := x) (u := .var w) Term.lc.var σ (.dsum s' s''))
      | tprod s' s'' =>
          simp only [Basis.subst, denotBasis, Space.subst]
          exact congrArg (BasisDenot.vecs · []) (denotSpace_subst (x := x) (u := .var w) Term.lc.var σ (.tprod s' s''))
      | ker s₀ s₁ e =>
          have hd₀ := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s₀
          have hd₁ := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s₁
          have he := denotTerm_subst (x := x) (u := .var w) Term.lc.var σ e
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvLeft V₀ V₁ f (fun μ => decide (μ = 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₀ (LinearMap.ker f)) (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ (Basis.subst x (.var w) (.proj (.ker s₀ s₁ e) b₀ b₁))
              = F (denotSpace σ (Space.subst x (.var w) s₀)) (denotSpace σ (Space.subst x (.var w) s₁))
                  (denotTerm σ (Term.subst x (.var w) e))
                  (denotBasis σ (Basis.subst x (.var w) b₀)) (denotBasis σ (Basis.subst x (.var w) b₁)) := by
            simp only [Basis.subst, Space.subst, denotBasis, F]
          have hR : denotBasis (σ.bind x (denotTerm σ (.var w))) (.proj (.ker s₀ s₁ e) b₀ b₁)
              = F (denotSpace (σ.bind x (denotTerm σ (.var w))) s₀)
                  (denotSpace (σ.bind x (denotTerm σ (.var w))) s₁)
                  (denotTerm (σ.bind x (denotTerm σ (.var w))) e)
                  (denotBasis (σ.bind x (denotTerm σ (.var w))) b₀)
                  (denotBasis (σ.bind x (denotTerm σ (.var w))) b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
      | coker s₀ s₁ e =>
          have hd₀ := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s₀
          have hd₁ := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s₁
          have he := denotTerm_subst (x := x) (u := .var w) Term.lc.var σ e
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvLeft V₀ V₁ f (fun μ => decide (μ ≠ 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₀ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)))
                (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ (Basis.subst x (.var w) (.proj (.coker s₀ s₁ e) b₀ b₁))
              = F (denotSpace σ (Space.subst x (.var w) s₀)) (denotSpace σ (Space.subst x (.var w) s₁))
                  (denotTerm σ (Term.subst x (.var w) e))
                  (denotBasis σ (Basis.subst x (.var w) b₀)) (denotBasis σ (Basis.subst x (.var w) b₁)) := by
            simp only [Basis.subst, Space.subst, denotBasis, F]
          have hR : denotBasis (σ.bind x (denotTerm σ (.var w))) (.proj (.coker s₀ s₁ e) b₀ b₁)
              = F (denotSpace (σ.bind x (denotTerm σ (.var w))) s₀)
                  (denotSpace (σ.bind x (denotTerm σ (.var w))) s₁)
                  (denotTerm (σ.bind x (denotTerm σ (.var w))) e)
                  (denotBasis (σ.bind x (denotTerm σ (.var w))) b₀)
                  (denotBasis (σ.bind x (denotTerm σ (.var w))) b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
      | img s₀ s₁ e =>
          have hd₀ := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s₀
          have hd₁ := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s₁
          have he := denotTerm_subst (x := x) (u := .var w) Term.lc.var σ e
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvRight V₀ V₁ f (fun μ => decide (μ ≠ 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₁ (LinearMap.range f)) (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ (Basis.subst x (.var w) (.proj (.img s₀ s₁ e) b₀ b₁))
              = F (denotSpace σ (Space.subst x (.var w) s₀)) (denotSpace σ (Space.subst x (.var w) s₁))
                  (denotTerm σ (Term.subst x (.var w) e))
                  (denotBasis σ (Basis.subst x (.var w) b₀)) (denotBasis σ (Basis.subst x (.var w) b₁)) := by
            simp only [Basis.subst, Space.subst, denotBasis, F]
          have hR : denotBasis (σ.bind x (denotTerm σ (.var w))) (.proj (.img s₀ s₁ e) b₀ b₁)
              = F (denotSpace (σ.bind x (denotTerm σ (.var w))) s₀)
                  (denotSpace (σ.bind x (denotTerm σ (.var w))) s₁)
                  (denotTerm (σ.bind x (denotTerm σ (.var w))) e)
                  (denotBasis (σ.bind x (denotTerm σ (.var w))) b₀)
                  (denotBasis (σ.bind x (denotTerm σ (.var w))) b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
      | coimg s₀ s₁ e =>
          have hd₀ := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s₀
          have hd₁ := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s₁
          have he := denotTerm_subst (x := x) (u := .var w) Term.lc.var σ e
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvRight V₀ V₁ f (fun μ => decide (μ = 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₁ (Submodule.orthRel V₁.innerProduct (LinearMap.range f)))
                (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ (Basis.subst x (.var w) (.proj (.coimg s₀ s₁ e) b₀ b₁))
              = F (denotSpace σ (Space.subst x (.var w) s₀)) (denotSpace σ (Space.subst x (.var w) s₁))
                  (denotTerm σ (Term.subst x (.var w) e))
                  (denotBasis σ (Basis.subst x (.var w) b₀)) (denotBasis σ (Basis.subst x (.var w) b₁)) := by
            simp only [Basis.subst, Space.subst, denotBasis, F]
          have hR : denotBasis (σ.bind x (denotTerm σ (.var w))) (.proj (.coimg s₀ s₁ e) b₀ b₁)
              = F (denotSpace (σ.bind x (denotTerm σ (.var w))) s₀)
                  (denotSpace (σ.bind x (denotTerm σ (.var w))) s₁)
                  (denotTerm (σ.bind x (denotTerm σ (.var w))) e)
                  (denotBasis (σ.bind x (denotTerm σ (.var w))) b₀)
                  (denotBasis (σ.bind x (denotTerm σ (.var w))) b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
  | .image b, σ => by
      have hb := denotBasis_subst x w b σ
      -- Dispatch on whether `sof b` is a `.coker` (the only `.image` arm that
      -- isn't the constant fallback). `sof (subst b)` matches `subst (sof b)`.
      by_cases hcoker : ∃ s₀ s₁ e, Basis.sof b = .coker s₀ s₁ e
      · obtain ⟨s₀, s₁, e, hsof⟩ := hcoker
        have hsofL : Basis.sof (Basis.subst x (.var w) b)
            = .coker (Space.subst x (.var w) s₀) (Space.subst x (.var w) s₁)
                (Term.subst x (.var w) e) := by
          rw [Basis.sof_subst, hsof, Space.subst]
        have hd₀ := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s₀
        have hd₁ := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s₁
        have he := denotTerm_subst (x := x) (u := .var w) Term.lc.var σ e
        -- Use the `.image`/`.coker` unfold lemma on both sides, then push the
        -- substituted reads to the bound-env form through the `F`-device.
        let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot :=
          fun V₀ V₁ c d =>
            BasisDenot.vecs (V₁.ofSubmodule (DVal.asLinMap V₀ V₁ c).range)
              ((BasisDenot.atSpace (V₀.ofSubmodule
                  (Submodule.orthRel V₀.innerProduct (DVal.asLinMap V₀ V₁ c).ker)) d).map
                (fun w' => ⟨(DVal.asLinMap V₀ V₁ c) (Subtype.val w'),
                  LinearMap.mem_range_self _ _⟩))
        have hL : denotBasis σ (Basis.subst x (.var w) (.image b))
            = F (denotSpace σ (Space.subst x (.var w) s₀))
                (denotSpace σ (Space.subst x (.var w) s₁))
                (denotTerm σ (Term.subst x (.var w) e))
                (denotBasis σ (Basis.subst x (.var w) b)) := by
          rw [show Basis.subst x (.var w) (.image b)
                = .image (Basis.subst x (.var w) b) from rfl,
            denotBasis_image_unfold σ (Basis.subst x (.var w) b) hsofL]
          simp only [F, imageF, imageRestrict]
          rfl
        have hR : denotBasis (σ.bind x (denotTerm σ (.var w))) (.image b)
            = F (denotSpace (σ.bind x (denotTerm σ (.var w))) s₀)
                (denotSpace (σ.bind x (denotTerm σ (.var w))) s₁)
                (denotTerm (σ.bind x (denotTerm σ (.var w))) e)
                (denotBasis (σ.bind x (denotTerm σ (.var w))) b) := by
          rw [denotBasis_image_unfold (σ.bind x (denotTerm σ (.var w))) b hsof]
          simp only [F, imageF, imageRestrict]
          rfl
        rw [hL, hR, hd₀, hd₁, he, hb]
      · -- `sof b` not a coker: both sides reduce to the constant fallback.
        simp only [not_exists] at hcoker
        have hsofL : ∀ s₀ s₁ e, Basis.sof (Basis.subst x (.var w) b)
            ≠ .coker s₀ s₁ e := by
          intro s₀ s₁ e hc
          rw [Basis.sof_subst] at hc
          -- a substituted `sof b` is a coker only if `sof b` was a coker
          cases hb' : Basis.sof b with
          | coker a₀ a₁ a => exact (hcoker a₀ a₁ a hb').elim
          | empty => rw [hb'] at hc; simp [Space.subst] at hc
          | real => rw [hb'] at hc; simp [Space.subst] at hc
          | dual _ => rw [hb'] at hc; simp [Space.subst] at hc
          | dsum _ _ => rw [hb'] at hc; simp [Space.subst] at hc
          | tprod _ _ => rw [hb'] at hc; simp [Space.subst] at hc
          | ker _ _ _ => rw [hb'] at hc; simp [Space.subst] at hc
          | img _ _ _ => rw [hb'] at hc; simp [Space.subst] at hc
          | coimg _ _ _ => rw [hb'] at hc; simp [Space.subst] at hc
        rw [show Basis.subst x (.var w) (.image b)
              = .image (Basis.subst x (.var w) b) from rfl,
          denotBasis_image_noncoker σ (Basis.subst x (.var w) b) hsofL,
          denotBasis_image_noncoker (σ.bind x (denotTerm σ (.var w))) b hcoker]
        -- both `sof (.image _)` collapse to `.empty` (non-coker), so the
        -- carrier denotations agree trivially.
        refine congrArg (BasisDenot.vecs · []) ?_
        have hsiL : Basis.sof (.image (Basis.subst x (.var w) b)) = .empty := by
          rw [Basis.sof]; split
          · rename_i s₀ s₁ e hm; exact absurd hm (hsofL s₀ s₁ e)
          · rfl
        have hsiR : Basis.sof (.image b) = .empty := by
          rw [Basis.sof]; split
          · rename_i s₀ s₁ e hm; exact absurd hm (hcoker _ _ _)
          · rfl
        rw [hsiL, hsiR]
        rfl
  | .terms s es b, σ => by
      have hb := denotBasis_subst x w b σ
      have hd := denotSpace_subst (x := x) (u := .var w) Term.lc.var σ s
      have hesmap : ((es.map (Term.subst x (.var w))).map (fun e => denotTerm σ e))
          = (es.map (fun e => denotTerm (σ.bind x (denotTerm σ (.var w))) e)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro e _
        exact denotTerm_subst (x := x) (u := .var w) Term.lc.var σ e
      let F : (V : HSpace) → List DVal → BasisDenot → BasisDenot :=
        fun V terms d =>
          .vecs V (V.lexInd ((terms.map (fun t => t.atSpace V)) ++ (d.atSpace V)))
      have hL : denotBasis σ (Basis.subst x (.var w) (.terms s es b))
          = F (denotSpace σ (Space.subst x (.var w) s))
              ((es.map (Term.subst x (.var w))).map (fun e => denotTerm σ e))
              (denotBasis σ (Basis.subst x (.var w) b)) := by
        simp only [Basis.subst, denotBasis, F, List.map_map, Function.comp_def]
      have hR : denotBasis (σ.bind x (denotTerm σ (.var w))) (.terms s es b)
          = F (denotSpace (σ.bind x (denotTerm σ (.var w))) s)
              (es.map (fun e => denotTerm (σ.bind x (denotTerm σ (.var w))) e))
              (denotBasis (σ.bind x (denotTerm σ (.var w))) b) := by
        simp only [denotBasis, F, List.map_map, Function.comp_def]
      rw [hL, hR, hd, hesmap, hb]
  | .frame b₀ b₁, σ => by
      -- Carriers agree via `tof_subst` + `denotTy_subst`.
      have htof : denotTy σ (Basis.tof (Basis.subst x (.var w) b₀))
          = denotTy (σ.bind x (denotTerm σ (.var w))) (Basis.tof b₀) := by
        rw [Basis.tof_subst, denotTy_subst (x := x) (u := .var w) Term.lc.var]
      -- Abbreviations.
      set σ' := σ.bind x (denotTerm σ (.var w)) with hσ'
      set T : HType := denotTy σ (Basis.tof (Basis.subst x (.var w) b₀)) with hT
      -- Pick a name `a` fresh for everything in play.
      obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset
        (Basis.fv b₁ ∪ Basis.fv (Basis.subst x (.var w) b₁) ∪ Term.fv (.var w)
          ∪ {x, Basis.freshFor b₁, Basis.freshFor (Basis.subst x (.var w) b₁)})
      simp only [Finset.notMem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or] at ha
      obtain ⟨⟨⟨ha_b₁, ha_sub⟩, ha_u⟩, ha_x, ha_z₂, ha_z₁⟩ := ha
      set z₁ := Basis.freshFor (Basis.subst x (.var w) b₁) with hz₁
      set z₂ := Basis.freshFor b₁ with hz₂
      have hz₁_spec : z₁ ∉ Basis.fv (Basis.subst x (.var w) b₁) := Basis.freshFor_spec _
      have hz₂_spec : z₂ ∉ Basis.fv b₁ := Basis.freshFor_spec _
      -- domain bases agree (recursive subst-irrelevance on `b₀`).
      have hdom : denotBasis σ (Basis.subst x (.var w) b₀) = denotBasis σ' b₀ :=
        denotBasis_subst x w b₀ σ
      let F : (T₀ : HType) → BasisDenot → ((y : T₀.El) → BasisDenot) → BasisDenot :=
        fun T₀ domB fam => BasisDenot.frame T₀.El domB (fun y => fam y)
      have hL : denotBasis σ (Basis.subst x (.var w) (.frame b₀ b₁))
          = F T (denotBasis σ (Basis.subst x (.var w) b₀)) (fun y =>
              denotBasis (σ.bind z₁ (T.embed y))
                (Basis.openVar z₁ (Basis.subst x (.var w) b₁))) := by
        show denotBasis σ (.frame (Basis.subst x (.var w) b₀) (Basis.subst x (.var w) b₁)) = _
        rw [denotBasis]
      have hR : denotBasis σ' (.frame b₀ b₁)
          = F (denotTy σ' (Basis.tof b₀)) (denotBasis σ' b₀) (fun y =>
              denotBasis (σ'.bind z₂ ((denotTy σ' (Basis.tof b₀)).embed y))
                (Basis.openVar z₂ b₁)) := by
        rw [denotBasis]
      rw [hL, hR, ← htof, ← hdom]
      refine congrArg (F T (denotBasis σ (Basis.subst x (.var w) b₀))) ?_
      funext y
      set wv : DVal := T.embed y with hwv
      -- Rename z₁ → a on the LHS fiber, then peel the `subst x u`.
      have hL_rename : Basis.openVar z₁ (Basis.subst x (.var w) b₁)
          = Basis.subst a (.var z₁) (Basis.openVar a (Basis.subst x (.var w) b₁)) :=
        Basis.subst_intro a (.var z₁) (Basis.subst x (.var w) b₁) ha_sub 0
      -- `openVar a (subst x u b₁) = subst x u (openVar a b₁)` (a ≠ x, lc u).
      have hcomm : Basis.openVar a (Basis.subst x (.var w) b₁)
          = Basis.subst x (.var w) (Basis.openVar a b₁) := by
        show Basis.openRec 0 (.var a) (Basis.subst x (.var w) b₁) = _
        rw [Basis.subst_openRec x (.var w) (Term.lc.var) b₁ 0 (.var a)]
        congr 1
        simp only [Term.subst]
        rw [if_neg (Ne.symm ha_x)]
      have eL : denotBasis (σ.bind z₁ wv) (Basis.openVar z₁ (Basis.subst x (.var w) b₁))
          = denotBasis
              (((σ.bind z₁ wv).bind a wv).bind x
                (denotTerm ((σ.bind z₁ wv).bind a wv) (.var w)))
              (Basis.openVar a b₁) := by
        rw [hL_rename,
          denotBasis_subst a z₁ (Basis.openVar a (Basis.subst x (.var w) b₁)) (σ.bind z₁ wv),
          denotTerm_bind_self, hcomm,
          denotBasis_subst x w (Basis.openVar a b₁) ((σ.bind z₁ wv).bind a wv)]
      -- Rename z₂ → a on the RHS fiber.
      have hR_rename : Basis.openVar z₂ b₁
          = Basis.subst a (.var z₂) (Basis.openVar a b₁) :=
        Basis.subst_intro a (.var z₂) b₁ ha_b₁ 0
      have eR : denotBasis (σ'.bind z₂ wv) (Basis.openVar z₂ b₁)
          = denotBasis ((σ'.bind z₂ wv).bind a wv) (Basis.openVar a b₁) := by
        rw [hR_rename,
          denotBasis_subst a z₂ (Basis.openVar a b₁) (σ'.bind z₂ wv),
          denotTerm_bind_self]
      -- The two reconciled envs agree on `fv (openVar a b₁)`.
      have hagree : (((σ.bind z₁ wv).bind a wv).bind x
            (denotTerm ((σ.bind z₁ wv).bind a wv) (.var w))).AgreeOn
          ((σ'.bind z₂ wv).bind a wv) (Basis.fv (Basis.openVar a b₁)) := by
        refine ⟨fun p hp => ?_⟩
        have hp' : p ∈ Basis.fv b₁ ∪ Term.fv (.var a) :=
          Basis.fv_openRec_subset 0 (.var a) b₁ hp
        rw [Finset.mem_union] at hp'
        by_cases hpa : p = a
        · subst hpa
          simp [DEnv.bind, hσ', Finmap.lookup_insert,
            Finmap.lookup_insert_of_ne _ ha_x]
        -- `p ∈ fv b₁` (the `Term.fv (.var a)` alternative is `p = a`, excluded).
        have hpb₁ : p ∈ Basis.fv b₁ := by
          rcases hp' with h | h
          · exact h
          · simp only [Term.fv, Finset.mem_singleton] at h; exact absurd h hpa
        have hpz₂ : p ≠ z₂ := fun heq => hz₂_spec (heq ▸ hpb₁)
        by_cases hpx : p = x
        · -- `p = x ∈ fv b₁` ⟹ `w ∈ fv (subst x (.var w) b₁)` ⟹ `z₁ ≠ w`; also
          -- `z₂ ≠ x` (`z₂ ∉ fv b₁ ∋ x`). The `x`-bound value collapses to
          -- `denotTerm σ (.var w)` on both sides.
          subst hpx
          have hwmem : w ∈ Basis.fv (Basis.subst p (.var w) b₁) :=
            Basis.mem_fv_subst_var (b := b₁) hpb₁
          have hwz₁ : w ≠ z₁ := fun heq => hz₁_spec (heq ▸ hwmem)
          have hwa : w ≠ a := fun heq => ha_u (by simp [Term.fv, heq])
          have hpz₂' : p ≠ z₂ := hpz₂
          have hpa' : p ≠ a := hpa
          have hbridge : denotTerm ((σ.bind z₁ wv).bind a wv) (.var w) = denotTerm σ (.var w) :=
            denotTerm_agree (.var w) (DEnv.AgreeOn.bind2_left_of_not_mem
              (S := Term.fv (.var w))
              (by simp [Term.fv]; exact fun h => hwz₁ h.symm)
              (by simp [Term.fv]; exact fun h => hwa h.symm))
          simp only [DEnv.bind] at hbridge ⊢
          simp [hσ', DEnv.bind, Finmap.lookup_insert,
            Finmap.lookup_insert_of_ne _ hpa', Finmap.lookup_insert_of_ne _ hpz₂',
            hbridge]
        · have hpz₁ : p ≠ z₁ := fun heq =>
            hz₁_spec (heq ▸ Basis.mem_fv_subst_var_of_ne hpx hpb₁)
          simp [DEnv.bind, hσ',
            Finmap.lookup_insert_of_ne _ hpa, Finmap.lookup_insert_of_ne _ hpx,
            Finmap.lookup_insert_of_ne _ hpz₁, Finmap.lookup_insert_of_ne _ hpz₂]
      rw [eL, eR]
      exact denotBasis_agree (Basis.openVar a b₁) hagree
  termination_by b => Basis.size b
  decreasing_by
    all_goals first
      | (simp only [Basis.size]; omega)
      | (simp only [Basis.openVar, Basis.size_openVar, Basis.size_subst_var];
         simp only [Basis.size]; omega)

/-- Fresh opening-name irrelevance for `denotBasis`'s `.frame` binder: opening
    `b` at `x` (bound to `v`) equals opening at `y` (bound to `v`), for `x,y`
    fresh for `b`. Route: `Basis.subst_intro` re-aligns to a common `openVar x b`,
    `denotBasis_subst` commutes the var-subst through the env, `denotBasis_agree`
    closes the residual env mismatch. -/
theorem denotSpaceOpenIrrel (σ : DEnv) (s : Space) (x y : Name) (v : DVal)
    (hx : x ∉ Space.fv s) (hy : y ∉ Space.fv s) :
    denotSpace (σ.bind x v) (Space.openRec 0 (.var x) s) =
      denotSpace (σ.bind y v) (Space.openRec 0 (.var y) s) := by
  have hreidx : Space.openRec 0 (.var y) s =
      Space.subst x (.var y) (Space.openRec 0 (.var x) s) :=
    Space.subst_intro x (.var y) s hx 0
  rw [hreidx, denotSpace_subst Term.lc.var, denotTerm_bind_self]
  refine denotSpace_agree (Space.openRec 0 (.var x) s) ⟨fun p hp => ?_⟩
  have hp' : p ∈ Space.fv s ∪ Term.fv (.var x) :=
    Space.fv_openRec_subset 0 (.var x) s hp
  rw [Finset.mem_union] at hp'
  by_cases hpx : p = x
  · subst hpx
    simp [DEnv.bind, Finmap.lookup_insert]
  · have hps : p ∈ Space.fv s := by
      rcases hp' with h | h
      · exact h
      · simp only [Term.fv, Finset.mem_singleton] at h
        exact absurd h hpx
    have hpy : p ≠ y := fun heq => hy (heq ▸ hps)
    simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hpx,
      Finmap.lookup_insert_of_ne _ hpy]

theorem denotBasisOpenIrrel (σ : DEnv) (b : Basis) (x y : Name) (v : DVal)
    (hx : x ∉ Basis.fv b) (hy : y ∉ Basis.fv b) :
    denotBasis (σ.bind x v) (Basis.openVar x b)
      = denotBasis (σ.bind y v) (Basis.openVar y b) := by
  have hreidx : Basis.openVar y b
      = Basis.subst x (.var y) (Basis.openVar x b) :=
    Basis.subst_intro x (.var y) b hx 0
  rw [hreidx,
    denotBasis_subst x y (Basis.openVar x b) (σ.bind y v),
    denotTerm_bind_self]
  refine denotBasis_agree (Basis.openVar x b) ⟨fun p hp => ?_⟩
  have hp' : p ∈ Basis.fv b ∪ Term.fv (.var x) :=
    Basis.fv_openRec_subset 0 (.var x) b hp
  rw [Finset.mem_union] at hp'
  by_cases hpx : p = x
  · subst hpx; simp [DEnv.bind, Finmap.lookup_insert]
  · have hpb : p ∈ Basis.fv b := by
      rcases hp' with h | h
      · exact h
      · simp only [Term.fv, Finset.mem_singleton] at h; exact absurd h hpx
    have hpy : p ≠ y := fun heq => hy (heq ▸ hpb)
    simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hpx,
      Finmap.lookup_insert_of_ne _ hpy]

end GLang
