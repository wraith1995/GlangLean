

import GLang.Proofs.Progress.Supporting.ProgressMasterDefs

namespace GLang.V2

theorem progress_arm_sub_ker {ε : NLCtx} {e : Term} {s₀ s₁ : Space}
    (_hsv₀ : SValid ε s₀) (_hsv₁ : SValid ε s₁)
    (_hte : HasType ∅ ε e (Ty.space (s₀.dual.tprod s₁)))
    (ih₀ : pMotiveS ε s₀) (ih₁ : pMotiveS ε s₁)
    (ihe : pMotiveH ∅ ε e (Ty.space (s₀.dual.tprod s₁))) :
    pMotiveSub ε (s₀.ker s₁ e) s₀ := by
  intro Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, hv⟩ := (ihe Ψ hP hcov).1
  -- (C2): the witness's std basis IS the rule's `.tprod (.dual b₀) b₁`.
  have hv' : ValExpr.OpStep Ψ e
      (.tprod (.dual (Basis.stdSpace s₀)) (Basis.stdSpace s₁)) v := hv
  -- (C4)/(C5): the goal basis IS the `embed_ker` conclusion basis.
  exact ⟨_, ValExpr.OpStep.embed_ker
    (Basis.sof_stdSpace s₀) (Basis.sof_stdSpace s₁)
    (.inner_std (Basis.isStd_stdSpace s₀) hsv₀ (Basis.sof_stdSpace s₀))
    (.inner_std (Basis.isStd_stdSpace s₁) hsv₁ (Basis.sof_stdSpace s₁))
    hv'⟩

theorem progress_arm_sub_coker {ε : NLCtx} {e : Term} {s₀ s₁ : Space}
    (_hsv₀ : SValid ε s₀) (_hsv₁ : SValid ε s₁)
    (_hte : HasType ∅ ε e (Ty.space (s₀.dual.tprod s₁)))
    (ih₀ : pMotiveS ε s₀) (ih₁ : pMotiveS ε s₁)
    (ihe : pMotiveH ∅ ε e (Ty.space (s₀.dual.tprod s₁))) :
    pMotiveSub ε (s₀.coker s₁ e) s₀ := by
  intro Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, hv⟩ := (ihe Ψ hP hcov).1
  have hv' : ValExpr.OpStep Ψ e
      (.tprod (.dual (Basis.stdSpace s₀)) (Basis.stdSpace s₁)) v := hv
  exact ⟨_, ValExpr.OpStep.embed_coker
    (Basis.sof_stdSpace s₀) (Basis.sof_stdSpace s₁)
    (.inner_std (Basis.isStd_stdSpace s₀) hsv₀ (Basis.sof_stdSpace s₀))
    (.inner_std (Basis.isStd_stdSpace s₁) hsv₁ (Basis.sof_stdSpace s₁))
    hv'⟩

/-- refine_14, `SubType.sub_img`: `Img(e) ≤ s₁` — `OpStep.embed_img`
    (value `Trans(GSVDV)`, erratum E2), conclusion tail `stdSpace s₁` (the `s₁`-side
    supertype — the catalog-flagged ker/coker vs img/coimg tail
    difference, resolved per constructor). -/
theorem progress_arm_sub_img {ε : NLCtx} {e : Term} {s₀ s₁ : Space}
    (_hsv₀ : SValid ε s₀) (_hsv₁ : SValid ε s₁)
    (_hte : HasType ∅ ε e (Ty.space (s₀.dual.tprod s₁)))
    (ih₀ : pMotiveS ε s₀) (ih₁ : pMotiveS ε s₁)
    (ihe : pMotiveH ∅ ε e (Ty.space (s₀.dual.tprod s₁))) :
    pMotiveSub ε (s₀.img s₁ e) s₁ := by
  intro Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, hv⟩ := (ihe Ψ hP hcov).1
  have hv' : ValExpr.OpStep Ψ e
      (.tprod (.dual (Basis.stdSpace s₀)) (Basis.stdSpace s₁)) v := hv
  exact ⟨_, ValExpr.OpStep.embed_img
    (Basis.sof_stdSpace s₀) (Basis.sof_stdSpace s₁)
    (.inner_std (Basis.isStd_stdSpace s₀) hsv₀ (Basis.sof_stdSpace s₀))
    (.inner_std (Basis.isStd_stdSpace s₁) hsv₁ (Basis.sof_stdSpace s₁))
    hv'⟩

/-- refine_15, `SubType.sub_coimg`: `CoImg(e) ≤ s₁` — `OpStep.embed_coimg`
    (value `Trans(GSVDVI)`, erratum E2), conclusion tail `stdSpace s₁`. -/
theorem progress_arm_sub_coimg {ε : NLCtx} {e : Term} {s₀ s₁ : Space}
    (_hsv₀ : SValid ε s₀) (_hsv₁ : SValid ε s₁)
    (_hte : HasType ∅ ε e (Ty.space (s₀.dual.tprod s₁)))
    (ih₀ : pMotiveS ε s₀) (ih₁ : pMotiveS ε s₁)
    (ihe : pMotiveH ∅ ε e (Ty.space (s₀.dual.tprod s₁))) :
    pMotiveSub ε (s₀.coimg s₁ e) s₁ := by
  intro Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, hv⟩ := (ihe Ψ hP hcov).1
  have hv' : ValExpr.OpStep Ψ e
      (.tprod (.dual (Basis.stdSpace s₀)) (Basis.stdSpace s₁)) v := hv
  exact ⟨_, ValExpr.OpStep.embed_coimg
    (Basis.sof_stdSpace s₀) (Basis.sof_stdSpace s₁)
    (.inner_std (Basis.isStd_stdSpace s₀) hsv₀ (Basis.sof_stdSpace s₀))
    (.inner_std (Basis.isStd_stdSpace s₁) hsv₁ (Basis.sof_stdSpace s₁))
    hv'⟩

end GLang.V2

