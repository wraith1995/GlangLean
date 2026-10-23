import GLang.Semantics.BasisObjects

/-! Actual interpretation of bases. Validity and helper operations are
separate; source/basis soundness proves these lists and frames are well formed. -/
namespace GLang

noncomputable def denotBasis (σ : DEnv) : Basis → BasisDenot
  | .empty   => .vecs HSpace.empty []
  | .one     => .vecs HSpace.real [(1 : ℝ)]
  | .dual b  =>
      let V := denotSpace σ (Basis.sof b)
      let vs := (denotBasis σ b).atSpace V
      .vecs (HSpace.dual V) (V.dualOfList vs)
  | .dsum b₀ b₁ =>
      let V₀ := denotSpace σ (Basis.sof b₀)
      let V₁ := denotSpace σ (Basis.sof b₁)
      let vs₀ := (denotBasis σ b₀).atSpace V₀
      let vs₁ := (denotBasis σ b₁).atSpace V₁
      .vecs (HSpace.dsum V₀ V₁) (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁)
  | .tprod b₀ b₁ =>
      let V₀ := denotSpace σ (Basis.sof b₀)
      let V₁ := denotSpace σ (Basis.sof b₁)
      let vs₀ := (denotBasis σ b₀).atSpace V₀
      let vs₁ := (denotBasis σ b₁).atSpace V₁
      .vecs (HSpace.tprod V₀ V₁) (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁)
  | .proj s b₀ b₁  =>

      match s with
      | .ker s₀ s₁ e =>
          let V₀ := denotSpace σ s₀
          let V₁ := denotSpace σ s₁
          let f : V₀.carrier →ₗ[ℝ] V₁.carrier :=
            (denotTerm σ e).asLinMap V₀ V₁
          let vs₀ := (denotBasis σ b₀).atSpace V₀
          let vs₁ := (denotBasis σ b₁).atSpace V₁
          let raw := BasisFSV.fsvLeft V₀ V₁ f (fun μ => decide (μ = 0)) vs₀ vs₁
          let K : Submodule ℝ V₀.carrier := LinearMap.ker f
          .vecs (HSpace.ofSubmodule V₀ K) (HSpace.liftToSubmodule K raw)
      | .coker s₀ s₁ e =>
          let V₀ := denotSpace σ s₀
          let V₁ := denotSpace σ s₁
          let f : V₀.carrier →ₗ[ℝ] V₁.carrier :=
            (denotTerm σ e).asLinMap V₀ V₁
          let vs₀ := (denotBasis σ b₀).atSpace V₀
          let vs₁ := (denotBasis σ b₁).atSpace V₁
          let raw := BasisFSV.fsvLeft V₀ V₁ f (fun μ => decide (μ ≠ 0)) vs₀ vs₁
          let K : Submodule ℝ V₀.carrier :=
            Submodule.orthRel V₀.innerProduct (LinearMap.ker f)
          .vecs (HSpace.ofSubmodule V₀ K) (HSpace.liftToSubmodule K raw)
      | .img s₀ s₁ e =>
          let V₀ := denotSpace σ s₀
          let V₁ := denotSpace σ s₁
          let f : V₀.carrier →ₗ[ℝ] V₁.carrier :=
            (denotTerm σ e).asLinMap V₀ V₁
          let vs₀ := (denotBasis σ b₀).atSpace V₀
          let vs₁ := (denotBasis σ b₁).atSpace V₁
          let raw := BasisFSV.fsvRight V₀ V₁ f (fun μ => decide (μ ≠ 0)) vs₀ vs₁
          let K : Submodule ℝ V₁.carrier := LinearMap.range f
          .vecs (HSpace.ofSubmodule V₁ K) (HSpace.liftToSubmodule K raw)
      | .coimg s₀ s₁ e =>
          let V₀ := denotSpace σ s₀
          let V₁ := denotSpace σ s₁
          let f : V₀.carrier →ₗ[ℝ] V₁.carrier :=
            (denotTerm σ e).asLinMap V₀ V₁
          let vs₀ := (denotBasis σ b₀).atSpace V₀
          let vs₁ := (denotBasis σ b₁).atSpace V₁
          let raw := BasisFSV.fsvRight V₀ V₁ f (fun μ => decide (μ = 0)) vs₀ vs₁
          let K : Submodule ℝ V₁.carrier :=
            Submodule.orthRel V₁.innerProduct (LinearMap.range f)
          .vecs (HSpace.ofSubmodule V₁ K) (HSpace.liftToSubmodule K raw)
      | _ =>
          -- Non-FFS `s` — unreachable for valid bases (BasisValid's
          -- `.proj` clause requires `s ∈ {.ker, .coker, .img, .coimg}`).
          .vecs (denotSpace σ s) []
  | .image b       =>

      match _h_sof : Basis.sof b with
      | .coker s₀ s₁ e =>
          let V₀ := denotSpace σ s₀
          let V₁ := denotSpace σ s₁
          let f : V₀.carrier →ₗ[ℝ] V₁.carrier :=
            (denotTerm σ e).asLinMap V₀ V₁
          -- Recurse on `b`; under `_h_sof` the resulting HSpace is
          -- `HSpace.ofSubmodule V₀ (orthRel V₀.IP (ker f))`, whose carrier
          -- is the Submodule subtype. Lift via `.atSpace` of THAT HSpace.
          let V_coker : HSpace :=
            HSpace.ofSubmodule V₀ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f))
          let vs_sub : List V_coker.carrier := (denotBasis σ b).atSpace V_coker
          -- Coerce each ⟨v, _⟩ via subtype to V₀, apply f, repackage.
          let mapped : List (LinearMap.range f) :=
            vs_sub.map fun w =>
              ⟨f (Subtype.val w), LinearMap.mem_range_self f _⟩
          .vecs (HSpace.ofSubmodule V₁ (LinearMap.range f)) mapped
      | _ => .vecs (denotSpace σ (Basis.sof (.image b))) []
  | .terms s es b   =>
      -- Apply LexInd to the ordered concatenation of the term denotations
      -- and the fallback basis. `BasisLexInd.lean` proves independence and
      -- preservation of the span for this construction.
      let V := denotSpace σ s
      let vs_terms : List V.carrier := es.map (fun e => (denotTerm σ e).atSpace V)
      let vs_back  : List V.carrier := (denotBasis σ b).atSpace V
      .vecs V (V.lexInd (vs_terms ++ vs_back))
  | .frame b₀ b₁ =>

      let T_outer : HType := denotTy σ (Basis.tof b₀)
      let x : Name := Basis.freshFor b₁
      .frame T_outer.El (denotBasis σ b₀) (fun y : T_outer.El =>
        denotBasis (σ.bind x (T_outer.embed y)) (Basis.openVar x b₁))
termination_by b => Basis.size b
decreasing_by
  all_goals first
    | (simp only [Basis.openVar, Basis.size_openVar]; simp [Basis.size]; try omega)
    | (try simp [Basis.size]; try omega)

end GLang
