import GLang.Proofs.Adequacy.Foundations.OpenBridgeCore
import GLang.Proofs.Source.Soundness

/-!
# Source-side bridges for ordinary nonlinear application

This module promotes the source application equation and the basis-instantiation
equation below the adequacy development.  It depends only on source semantics,
substitution, and the live basis opening bridge.
-/

namespace GLang

/-- Source nonlinear application is the current `DVal.applyEl` operation at
the argument extracted through the (sound) domain type. -/
theorem denotTerm_appN_applyEl {sigma : DEnv} {n0 n1 : Term} {T0 : HType}
    {g : T0.El -> DVal}
    (hpi : denotTerm sigma n0 = .pi T0.El g)
    (hshape : (denotTerm sigma n1).matchesShape T0) :
    denotTerm sigma (.appN n0 n1) =
      (denotTerm sigma n0).applyEl (T0.extract (denotTerm sigma n1)) := by
  have hsource : denotTerm sigma (.appN n0 n1) =
      (denotTerm sigma n0).applyAsPi (denotTerm sigma n1) := rfl
  rw [hsource, hpi]
  simp only [DVal.applyAsPi, DVal.asPi]
  rw [show (denotTerm sigma n1).shape = T0 from hshape, dif_pos rfl]
  simp only [DVal.applyEl_pi]

/- `BasisSoundnessLive` keeps these implementation lemmas private. -/

private noncomputable def imageF (sigma : DEnv) (s0 s1 : Space) (e : Term) :
    (denotSpace sigma s0).carrier →ₗ[ℝ] (denotSpace sigma s1).carrier :=
  (denotTerm sigma e).asLinMap (denotSpace sigma s0) (denotSpace sigma s1)

private noncomputable def imageRestrict (sigma : DEnv) (s0 s1 : Space) (e : Term) :
    (denotSpace sigma (Space.coker s0 s1 e)).carrier →ₗ[ℝ]
      ↥(LinearMap.range (imageF sigma s0 s1 e)) :=
  LinearMap.codRestrict (LinearMap.range (imageF sigma s0 s1 e))
    ((imageF sigma s0 s1 e).comp
      (Submodule.subtype
        (Submodule.orthRel (denotSpace sigma s0).innerProduct
          (LinearMap.ker (imageF sigma s0 s1 e)))))
    (fun _ => LinearMap.mem_range_self _ _)

theorem denotBasis_image_unfold (sigma : DEnv) (b : Basis) {s0 s1 : Space}
    {e : Term} (hsof : Basis.sof b = .coker s0 s1 e) :
    denotBasis sigma (.image b)
      = .vecs
          (HSpace.ofSubmodule (denotSpace sigma s1)
            (LinearMap.range (imageF sigma s0 s1 e)))
          (((denotBasis sigma b).atSpace
              (denotSpace sigma (.coker s0 s1 e))).map
            (imageRestrict sigma s0 s1 e)) := by
  conv_lhs => rw [denotBasis]
  split
  · rename_i s0' s1' e' hmatch
    have heq : Space.coker s0 s1 e = Space.coker s0' s1' e' :=
      hsof.symm.trans hmatch
    injection heq with h0 h1 h2
    subst h0; subst h1; subst h2
    rfl
  · rename_i hneg
    exact absurd hsof (hneg s0 s1 e)

theorem denotBasis_image_noncoker (sigma : DEnv) (b : Basis)
    (hsof : forall s0 s1 e, Basis.sof b ≠ .coker s0 s1 e) :
    denotBasis sigma (.image b) =
      .vecs (denotSpace sigma (Basis.sof (.image b))) [] := by
  conv_lhs => rw [denotBasis]
  split
  · rename_i s0 s1 e hmatch
    exact absurd hmatch (hsof s0 s1 e)
  · rfl

theorem denotBasis_subst_lc_raw (x : Name) (u : Term) (hu : Term.lc u) :
    ∀ (b : Basis) (σ : DEnv),
      denotBasis σ (Basis.subst x u b)
        = denotBasis (σ.bind x (denotTerm σ u)) b
  | .empty, _ => by simp only [Basis.subst, denotBasis]
  | .one, _ => by simp only [Basis.subst, denotBasis]
  | .dual b, σ => by
      have hb := denotBasis_subst_lc_raw x u hu b σ
      have hsof : denotSpace σ (Basis.sof (Basis.subst x u b))
          = denotSpace (σ.bind x (denotTerm σ u)) (Basis.sof b) := by
        rw [Basis.sof_subst, denotSpace_subst (x := x) (u := u) hu]
      let F : (V : HSpace) → BasisDenot → BasisDenot :=
        fun V d => .vecs (HSpace.dual V) (V.dualOfList (d.atSpace V))
      have hL : denotBasis σ (Basis.subst x u (.dual b))
          = F (denotSpace σ (Basis.sof (Basis.subst x u b)))
              (denotBasis σ (Basis.subst x u b)) := by
        simp only [Basis.subst, denotBasis, F]
      have hR : denotBasis (σ.bind x (denotTerm σ u)) (.dual b)
          = F (denotSpace (σ.bind x (denotTerm σ u)) (Basis.sof b))
              (denotBasis (σ.bind x (denotTerm σ u)) b) := by
        simp only [denotBasis, F]
      rw [hL, hR, hsof, hb]
  | .dsum b₀ b₁, σ => by
      have hb₀ := denotBasis_subst_lc_raw x u hu b₀ σ
      have hb₁ := denotBasis_subst_lc_raw x u hu b₁ σ
      have hs₀ : denotSpace σ (Basis.sof (Basis.subst x u b₀))
          = denotSpace (σ.bind x (denotTerm σ u)) (Basis.sof b₀) := by
        rw [Basis.sof_subst, denotSpace_subst (x := x) (u := u) hu]
      have hs₁ : denotSpace σ (Basis.sof (Basis.subst x u b₁))
          = denotSpace (σ.bind x (denotTerm σ u)) (Basis.sof b₁) := by
        rw [Basis.sof_subst, denotSpace_subst (x := x) (u := u) hu]
      let F : (V₀ V₁ : HSpace) → BasisDenot → BasisDenot → BasisDenot :=
        fun V₀ V₁ d₀ d₁ =>
          .vecs (HSpace.dsum V₀ V₁) (HSpace.dsumOfLists V₀ V₁ (d₀.atSpace V₀) (d₁.atSpace V₁))
      have hL : denotBasis σ (Basis.subst x u (.dsum b₀ b₁))
          = F (denotSpace σ (Basis.sof (Basis.subst x u b₀)))
              (denotSpace σ (Basis.sof (Basis.subst x u b₁)))
              (denotBasis σ (Basis.subst x u b₀)) (denotBasis σ (Basis.subst x u b₁)) := by
        simp only [Basis.subst, denotBasis, F]
      have hR : denotBasis (σ.bind x (denotTerm σ u)) (.dsum b₀ b₁)
          = F (denotSpace (σ.bind x (denotTerm σ u)) (Basis.sof b₀))
              (denotSpace (σ.bind x (denotTerm σ u)) (Basis.sof b₁))
              (denotBasis (σ.bind x (denotTerm σ u)) b₀)
              (denotBasis (σ.bind x (denotTerm σ u)) b₁) := by
        simp only [denotBasis, F]
      rw [hL, hR, hs₀, hs₁, hb₀, hb₁]
  | .tprod b₀ b₁, σ => by
      have hb₀ := denotBasis_subst_lc_raw x u hu b₀ σ
      have hb₁ := denotBasis_subst_lc_raw x u hu b₁ σ
      have hs₀ : denotSpace σ (Basis.sof (Basis.subst x u b₀))
          = denotSpace (σ.bind x (denotTerm σ u)) (Basis.sof b₀) := by
        rw [Basis.sof_subst, denotSpace_subst (x := x) (u := u) hu]
      have hs₁ : denotSpace σ (Basis.sof (Basis.subst x u b₁))
          = denotSpace (σ.bind x (denotTerm σ u)) (Basis.sof b₁) := by
        rw [Basis.sof_subst, denotSpace_subst (x := x) (u := u) hu]
      let F : (V₀ V₁ : HSpace) → BasisDenot → BasisDenot → BasisDenot :=
        fun V₀ V₁ d₀ d₁ =>
          .vecs (HSpace.tprod V₀ V₁) (HSpace.tprodOfLists V₀ V₁ (d₀.atSpace V₀) (d₁.atSpace V₁))
      have hL : denotBasis σ (Basis.subst x u (.tprod b₀ b₁))
          = F (denotSpace σ (Basis.sof (Basis.subst x u b₀)))
              (denotSpace σ (Basis.sof (Basis.subst x u b₁)))
              (denotBasis σ (Basis.subst x u b₀)) (denotBasis σ (Basis.subst x u b₁)) := by
        simp only [Basis.subst, denotBasis, F]
      have hR : denotBasis (σ.bind x (denotTerm σ u)) (.tprod b₀ b₁)
          = F (denotSpace (σ.bind x (denotTerm σ u)) (Basis.sof b₀))
              (denotSpace (σ.bind x (denotTerm σ u)) (Basis.sof b₁))
              (denotBasis (σ.bind x (denotTerm σ u)) b₀)
              (denotBasis (σ.bind x (denotTerm σ u)) b₁) := by
        simp only [denotBasis, F]
      rw [hL, hR, hs₀, hs₁, hb₀, hb₁]
  | .proj s b₀ b₁, σ => by
      have hb₀ := denotBasis_subst_lc_raw x u hu b₀ σ
      have hb₁ := denotBasis_subst_lc_raw x u hu b₁ σ
      cases s with
      | empty =>
          simp only [Basis.subst, denotBasis, Space.subst]
          exact congrArg (BasisDenot.vecs · []) (denotSpace_subst (x := x) (u := u) hu σ .empty)
      | real =>
          simp only [Basis.subst, denotBasis, Space.subst]
          exact congrArg (BasisDenot.vecs · []) (denotSpace_subst (x := x) (u := u) hu σ .real)
      | dual s' =>
          simp only [Basis.subst, denotBasis, Space.subst]
          exact congrArg (BasisDenot.vecs · []) (denotSpace_subst (x := x) (u := u) hu σ (.dual s'))
      | dsum s' s'' =>
          simp only [Basis.subst, denotBasis, Space.subst]
          exact congrArg (BasisDenot.vecs · []) (denotSpace_subst (x := x) (u := u) hu σ (.dsum s' s''))
      | tprod s' s'' =>
          simp only [Basis.subst, denotBasis, Space.subst]
          exact congrArg (BasisDenot.vecs · []) (denotSpace_subst (x := x) (u := u) hu σ (.tprod s' s''))
      | ker s₀ s₁ e =>
          have hd₀ := denotSpace_subst (x := x) (u := u) hu σ s₀
          have hd₁ := denotSpace_subst (x := x) (u := u) hu σ s₁
          have he := denotTerm_subst (x := x) (u := u) hu σ e
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvLeft V₀ V₁ f (fun μ => decide (μ = 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₀ (LinearMap.ker f)) (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ (Basis.subst x u (.proj (.ker s₀ s₁ e) b₀ b₁))
              = F (denotSpace σ (Space.subst x u s₀)) (denotSpace σ (Space.subst x u s₁))
                  (denotTerm σ (Term.subst x u e))
                  (denotBasis σ (Basis.subst x u b₀)) (denotBasis σ (Basis.subst x u b₁)) := by
            simp only [Basis.subst, Space.subst, denotBasis, F]
          have hR : denotBasis (σ.bind x (denotTerm σ u)) (.proj (.ker s₀ s₁ e) b₀ b₁)
              = F (denotSpace (σ.bind x (denotTerm σ u)) s₀)
                  (denotSpace (σ.bind x (denotTerm σ u)) s₁)
                  (denotTerm (σ.bind x (denotTerm σ u)) e)
                  (denotBasis (σ.bind x (denotTerm σ u)) b₀)
                  (denotBasis (σ.bind x (denotTerm σ u)) b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
      | coker s₀ s₁ e =>
          have hd₀ := denotSpace_subst (x := x) (u := u) hu σ s₀
          have hd₁ := denotSpace_subst (x := x) (u := u) hu σ s₁
          have he := denotTerm_subst (x := x) (u := u) hu σ e
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvLeft V₀ V₁ f (fun μ => decide (μ ≠ 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₀ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)))
                (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ (Basis.subst x u (.proj (.coker s₀ s₁ e) b₀ b₁))
              = F (denotSpace σ (Space.subst x u s₀)) (denotSpace σ (Space.subst x u s₁))
                  (denotTerm σ (Term.subst x u e))
                  (denotBasis σ (Basis.subst x u b₀)) (denotBasis σ (Basis.subst x u b₁)) := by
            simp only [Basis.subst, Space.subst, denotBasis, F]
          have hR : denotBasis (σ.bind x (denotTerm σ u)) (.proj (.coker s₀ s₁ e) b₀ b₁)
              = F (denotSpace (σ.bind x (denotTerm σ u)) s₀)
                  (denotSpace (σ.bind x (denotTerm σ u)) s₁)
                  (denotTerm (σ.bind x (denotTerm σ u)) e)
                  (denotBasis (σ.bind x (denotTerm σ u)) b₀)
                  (denotBasis (σ.bind x (denotTerm σ u)) b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
      | img s₀ s₁ e =>
          have hd₀ := denotSpace_subst (x := x) (u := u) hu σ s₀
          have hd₁ := denotSpace_subst (x := x) (u := u) hu σ s₁
          have he := denotTerm_subst (x := x) (u := u) hu σ e
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvRight V₀ V₁ f (fun μ => decide (μ ≠ 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₁ (LinearMap.range f)) (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ (Basis.subst x u (.proj (.img s₀ s₁ e) b₀ b₁))
              = F (denotSpace σ (Space.subst x u s₀)) (denotSpace σ (Space.subst x u s₁))
                  (denotTerm σ (Term.subst x u e))
                  (denotBasis σ (Basis.subst x u b₀)) (denotBasis σ (Basis.subst x u b₁)) := by
            simp only [Basis.subst, Space.subst, denotBasis, F]
          have hR : denotBasis (σ.bind x (denotTerm σ u)) (.proj (.img s₀ s₁ e) b₀ b₁)
              = F (denotSpace (σ.bind x (denotTerm σ u)) s₀)
                  (denotSpace (σ.bind x (denotTerm σ u)) s₁)
                  (denotTerm (σ.bind x (denotTerm σ u)) e)
                  (denotBasis (σ.bind x (denotTerm σ u)) b₀)
                  (denotBasis (σ.bind x (denotTerm σ u)) b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
      | coimg s₀ s₁ e =>
          have hd₀ := denotSpace_subst (x := x) (u := u) hu σ s₀
          have hd₁ := denotSpace_subst (x := x) (u := u) hu σ s₁
          have he := denotTerm_subst (x := x) (u := u) hu σ e
          let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot → BasisDenot :=
            fun V₀ V₁ c d₀ d₁ =>
              let f := (c.asLinMap V₀ V₁)
              let raw := BasisFSV.fsvRight V₀ V₁ f (fun μ => decide (μ = 0))
                (d₀.atSpace V₀) (d₁.atSpace V₁)
              .vecs (HSpace.ofSubmodule V₁ (Submodule.orthRel V₁.innerProduct (LinearMap.range f)))
                (HSpace.liftToSubmodule _ raw)
          have hL : denotBasis σ (Basis.subst x u (.proj (.coimg s₀ s₁ e) b₀ b₁))
              = F (denotSpace σ (Space.subst x u s₀)) (denotSpace σ (Space.subst x u s₁))
                  (denotTerm σ (Term.subst x u e))
                  (denotBasis σ (Basis.subst x u b₀)) (denotBasis σ (Basis.subst x u b₁)) := by
            simp only [Basis.subst, Space.subst, denotBasis, F]
          have hR : denotBasis (σ.bind x (denotTerm σ u)) (.proj (.coimg s₀ s₁ e) b₀ b₁)
              = F (denotSpace (σ.bind x (denotTerm σ u)) s₀)
                  (denotSpace (σ.bind x (denotTerm σ u)) s₁)
                  (denotTerm (σ.bind x (denotTerm σ u)) e)
                  (denotBasis (σ.bind x (denotTerm σ u)) b₀)
                  (denotBasis (σ.bind x (denotTerm σ u)) b₁) := by
            simp only [denotBasis, F]
          rw [hL, hR, hd₀, hd₁, he, hb₀, hb₁]
  | .image b, σ => by
      have hb := denotBasis_subst_lc_raw x u hu b σ
      by_cases hcoker : ∃ s₀ s₁ e, Basis.sof b = .coker s₀ s₁ e
      · obtain ⟨s₀, s₁, e, hsof⟩ := hcoker
        have hsofL : Basis.sof (Basis.subst x u b)
            = .coker (Space.subst x u s₀) (Space.subst x u s₁)
                (Term.subst x u e) := by
          rw [Basis.sof_subst, hsof, Space.subst]
        have hd₀ := denotSpace_subst (x := x) (u := u) hu σ s₀
        have hd₁ := denotSpace_subst (x := x) (u := u) hu σ s₁
        have he := denotTerm_subst (x := x) (u := u) hu σ e
        let F : (V₀ V₁ : HSpace) → DVal → BasisDenot → BasisDenot :=
          fun V₀ V₁ c d =>
            BasisDenot.vecs (V₁.ofSubmodule (DVal.asLinMap V₀ V₁ c).range)
              ((BasisDenot.atSpace (V₀.ofSubmodule
                  (Submodule.orthRel V₀.innerProduct (DVal.asLinMap V₀ V₁ c).ker)) d).map
                (fun w' => ⟨(DVal.asLinMap V₀ V₁ c) (Subtype.val w'),
                  LinearMap.mem_range_self _ _⟩))
        have hL : denotBasis σ (Basis.subst x u (.image b))
            = F (denotSpace σ (Space.subst x u s₀))
                (denotSpace σ (Space.subst x u s₁))
                (denotTerm σ (Term.subst x u e))
                (denotBasis σ (Basis.subst x u b)) := by
          rw [show Basis.subst x u (.image b)
                = .image (Basis.subst x u b) from rfl,
            denotBasis_image_unfold σ (Basis.subst x u b) hsofL]
          simp only [F, imageF, imageRestrict]
          rfl
        have hR : denotBasis (σ.bind x (denotTerm σ u)) (.image b)
            = F (denotSpace (σ.bind x (denotTerm σ u)) s₀)
                (denotSpace (σ.bind x (denotTerm σ u)) s₁)
                (denotTerm (σ.bind x (denotTerm σ u)) e)
                (denotBasis (σ.bind x (denotTerm σ u)) b) := by
          rw [denotBasis_image_unfold (σ.bind x (denotTerm σ u)) b hsof]
          simp only [F, imageF, imageRestrict]
          rfl
        rw [hL, hR, hd₀, hd₁, he, hb]
      · simp only [not_exists] at hcoker
        have hsofL : ∀ s₀ s₁ e, Basis.sof (Basis.subst x u b)
            ≠ .coker s₀ s₁ e := by
          intro s₀ s₁ e hc
          rw [Basis.sof_subst] at hc
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
        rw [show Basis.subst x u (.image b)
              = .image (Basis.subst x u b) from rfl,
          denotBasis_image_noncoker σ (Basis.subst x u b) hsofL,
          denotBasis_image_noncoker (σ.bind x (denotTerm σ u)) b hcoker]
        refine congrArg (BasisDenot.vecs · []) ?_
        have hsiL : Basis.sof (.image (Basis.subst x u b)) = .empty := by
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
      have hb := denotBasis_subst_lc_raw x u hu b σ
      have hd := denotSpace_subst (x := x) (u := u) hu σ s
      have hesmap : ((es.map (Term.subst x u)).map (fun e => denotTerm σ e))
          = (es.map (fun e => denotTerm (σ.bind x (denotTerm σ u)) e)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro e _
        exact denotTerm_subst (x := x) (u := u) hu σ e
      let F : (V : HSpace) → List DVal → BasisDenot → BasisDenot :=
        fun V terms d =>
          .vecs V (V.lexInd ((terms.map (fun t => t.atSpace V)) ++ (d.atSpace V)))
      have hL : denotBasis σ (Basis.subst x u (.terms s es b))
          = F (denotSpace σ (Space.subst x u s))
              ((es.map (Term.subst x u)).map (fun e => denotTerm σ e))
              (denotBasis σ (Basis.subst x u b)) := by
        simp only [Basis.subst, denotBasis, F, List.map_map, Function.comp_def]
      have hR : denotBasis (σ.bind x (denotTerm σ u)) (.terms s es b)
          = F (denotSpace (σ.bind x (denotTerm σ u)) s)
              (es.map (fun e => denotTerm (σ.bind x (denotTerm σ u)) e))
              (denotBasis (σ.bind x (denotTerm σ u)) b) := by
        simp only [denotBasis, F, List.map_map, Function.comp_def]
      rw [hL, hR, hd, hesmap, hb]
  | .frame b₀ b₁, σ => by
      -- Carriers agree via `tof_subst` + `denotTy_subst`.
      have htof : denotTy σ (Basis.tof (Basis.subst x u b₀))
          = denotTy (σ.bind x (denotTerm σ u)) (Basis.tof b₀) := by
        rw [Basis.tof_subst, denotTy_subst (x := x) (u := u) hu]
      set σ' := σ.bind x (denotTerm σ u) with hσ'
      set T : HType := denotTy σ (Basis.tof (Basis.subst x u b₀)) with hT
      set z₁ := Basis.freshFor (Basis.subst x u b₁) with hz₁
      set z₂ := Basis.freshFor b₁ with hz₂
      -- domain bases agree (recursive subst-irrelevance on `b₀`).
      have hdom : denotBasis σ (Basis.subst x u b₀) = denotBasis σ' b₀ :=
        denotBasis_subst_lc_raw x u hu b₀ σ
      let F : (T₀ : HType) → BasisDenot → ((y : T₀.El) → BasisDenot) → BasisDenot :=
        fun T₀ domB fam => BasisDenot.frame T₀.El domB fam
      have hL : denotBasis σ (Basis.subst x u (.frame b₀ b₁))
          = F T (denotBasis σ (Basis.subst x u b₀)) (fun y =>
              denotBasis (σ.bind z₁ (T.embed y))
                (Basis.openVar z₁ (Basis.subst x u b₁))) := by
        show denotBasis σ (.frame (Basis.subst x u b₀) (Basis.subst x u b₁)) = _
        rw [denotBasis]
      have hR : denotBasis σ' (.frame b₀ b₁)
          = F (denotTy σ' (Basis.tof b₀)) (denotBasis σ' b₀) (fun y =>
              denotBasis (σ'.bind z₂ ((denotTy σ' (Basis.tof b₀)).embed y))
                (Basis.openVar z₂ b₁)) := by
        rw [denotBasis]
      rw [hL, hR, ← htof, ← hdom]
      refine congrArg (F T (denotBasis σ (Basis.subst x u b₀))) ?_
      funext y
      set wv : DVal := T.embed y with hwv
      -- A common fresh name for both fibers (avoids the two canonical opens,
      -- `x`, and `Term.fv u`).
      obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset
        (Basis.fv b₁ ∪ Basis.fv (Basis.subst x u b₁) ∪ Term.fv u ∪ {x, z₁, z₂})
      simp only [Finset.notMem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or] at ha
      obtain ⟨⟨⟨ha_b₁, ha_sub⟩, ha_u⟩, ha_x, _ha_z₁, _ha_z₂⟩ := ha
      -- H7: re-open both fibers at the common fresh `a`.
      have eL : denotBasis (σ.bind z₁ wv) (Basis.openVar z₁ (Basis.subst x u b₁))
          = denotBasis (σ.bind a wv) (Basis.openVar a (Basis.subst x u b₁)) :=
        denotBasisOpenIrrel σ (Basis.subst x u b₁) z₁ a wv
          (Basis.freshFor_spec _) ha_sub
      have eR : denotBasis (σ'.bind z₂ wv) (Basis.openVar z₂ b₁)
          = denotBasis (σ'.bind a wv) (Basis.openVar a b₁) :=
        denotBasisOpenIrrel σ' b₁ z₂ a wv (Basis.freshFor_spec _) ha_b₁
      rw [eL, eR]
      -- Commute the term-open past the `x`-substitution (`a ≠ x`).
      have hcomm : Basis.openVar a (Basis.subst x u b₁)
          = Basis.subst x u (Basis.openVar a b₁) := by
        show Basis.openRec 0 (.var a) (Basis.subst x u b₁) = _
        rw [Basis.subst_openRec x u hu b₁ 0 (.var a)]
        congr 1
        simp only [Term.subst]; rw [if_neg (Ne.symm ha_x)]
      rw [hcomm]
      -- Size-decreasing IH on `openVar a b₁`.
      have ih := denotBasis_subst_lc_raw x u hu (Basis.openVar a b₁) (σ.bind a wv)
      rw [ih]
      -- `a ∉ Term.fv u` so the bound value is `⟦u⟧σ`.
      have hval : denotTerm (σ.bind a wv) u = denotTerm σ u :=
        denotTerm_agree u (DEnv.AgreeOn.bind_left_of_not_mem ha_u)
      rw [hval, hσ']
      -- Residual: a name-disjoint bind swap (`a ≠ x`).
      rw [DEnv.bind_comm wv (denotTerm σ u) ha_x]
  termination_by b => Basis.size b
  decreasing_by
    all_goals first
      | (simp only [Basis.size]; omega)
      | (simp only [Basis.openVar, Basis.size_openVar]; simp only [Basis.size]; omega)

/-- **`denotBasis` instantiation** (basis analogue of `denotTy_instantiate`):
    for locally-closed `u`, opening `b`'s top bound index with `u` denotes as
    opening it with a fresh name `x` bound to `⟦u⟧σ` in `σ`. This is exactly
    the fact the `appN` output-agreement bridges need (`Adequacy_G4N1Bridge`
    step 6): `denotBasis`'s `.frame` arm produces the RHS form, and the
    application argument supplies the LHS.

    `x` must be fresh for `b` (`x ∉ Basis.fv b`); the bridges use
    `Basis.freshFor b` (canonically fresh). -/
theorem denotBasis_inst_raw {x : Name} {u : Term} (hu : Term.lc u) (σ : DEnv)
    (b : Basis) (hx : x ∉ Basis.fv b) :
    denotBasis σ (Basis.instantiate u b)
      = denotBasis (σ.bind x (denotTerm σ u)) (Basis.openVar x b) := by
  rw [show Basis.instantiate u b = Basis.openRec 0 u b from rfl,
    Basis.subst_intro x u b hx 0,
    denotBasis_subst_lc_raw x u hu (Basis.openVar x b) σ]

/-- The exact general instantiation fact needed below.  The retired proof is
`denotBasis_inst` in `ValueAdequacyFullFirstOrder.lean`; it must be promoted
without importing that stale module. -/
def RawBasisInstantiationLaw : Prop :=
  forall {x : Name} {u : Term}, Term.lc u -> forall (sigma : DEnv) (b : Basis),
    x ∉ Basis.fv b ->
    denotBasis sigma (Basis.instantiate u b) =
      denotBasis (sigma.bind x (denotTerm sigma u)) (Basis.openVar x b)

theorem rawBasisInstantiationLaw_holds : RawBasisInstantiationLaw := by
  intro x u hu sigma b hx
  exact denotBasis_inst_raw hu sigma b hx

/-- Once the general instantiation law is available, applying a denoted frame
at a sound argument is exactly the denotation of the instantiated codomain
basis. -/
theorem denotBasis_frame_applyEl_instantiate_of_law
    (hinst : RawBasisInstantiationLaw)
    {sigma : DEnv} {n1 : Term} {b0 b1 : Basis}
    (hlc : Term.lc n1)
    (hmatch : (denotTerm sigma n1).matchesShape
      (denotTy sigma (Basis.tof b0))) :
    (denotBasis sigma (.frame b0 b1)).applyEl
        ((denotTy sigma (Basis.tof b0)).extract (denotTerm sigma n1)) =
      denotBasis sigma (Basis.instantiate n1 b1) := by
  let y := Basis.freshFor b1
  have hy : y ∉ Basis.fv b1 := Basis.freshFor_spec b1
  rw [denotBasis_frame_applyEl_openVar y hy]
  rw [HType.embed_extract_of_matchesShape hmatch]
  exact (hinst hlc sigma b1 hy).symm

/-- The unconditional bridge required by the `appN_val` adequacy arm. -/
theorem denotBasis_frame_applyEl_instantiate
    {sigma : DEnv} {n1 : Term} {b0 b1 : Basis}
    (hlc : Term.lc n1)
    (hmatch : (denotTerm sigma n1).matchesShape
      (denotTy sigma (Basis.tof b0))) :
    (denotBasis sigma (.frame b0 b1)).applyEl
        ((denotTy sigma (Basis.tof b0)).extract (denotTerm sigma n1)) =
      denotBasis sigma (Basis.instantiate n1 b1) :=
  denotBasis_frame_applyEl_instantiate_of_law
    rawBasisInstantiationLaw_holds hlc hmatch

end GLang
