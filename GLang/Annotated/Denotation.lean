import GLang.Semantics.SourceValues

/-! Source spaces, types, and terms: the actual mutual denotation.
Mathematical operations and representation checks live in Semantics/.
PaperDenotationResults proves the named-binder equations on typed syntax. -/
namespace GLang
open scoped TensorProduct

mutual

  /-- `Sem⟦s⟧σΔ` — denote a space under a local de Bruijn env `Δ`. -/
  noncomputable def denotSpaceAux (σ : DEnv) (Δ : List DVal) (s : Space) : HSpace :=
    match s with
    | .empty       => HSpace.empty
    | .real        => HSpace.real
    | .dual s      => HSpace.dual (denotSpaceAux σ Δ s)
    | .dsum s₀ s₁  => HSpace.dsum (denotSpaceAux σ Δ s₀) (denotSpaceAux σ Δ s₁)
    | .tprod s₀ s₁ => HSpace.tprod (denotSpaceAux σ Δ s₀) (denotSpaceAux σ Δ s₁)

    | .ker s₀ s₁ e =>
        let V₀ := denotSpaceAux σ Δ s₀
        let V₁ := denotSpaceAux σ Δ s₁
        let f := (denotTermAux σ Δ e).asLinMap V₀ V₁
        HSpace.ofSubmodule V₀ (LinearMap.ker f)
    | .coker s₀ s₁ e =>
        let V₀ := denotSpaceAux σ Δ s₀
        let V₁ := denotSpaceAux σ Δ s₁
        let f := (denotTermAux σ Δ e).asLinMap V₀ V₁
        HSpace.ofSubmodule V₀
          (Submodule.orthRel V₀.innerProduct (LinearMap.ker f))
    | .img s₀ s₁ e =>
        let V₀ := denotSpaceAux σ Δ s₀
        let V₁ := denotSpaceAux σ Δ s₁
        let f := (denotTermAux σ Δ e).asLinMap V₀ V₁
        HSpace.ofSubmodule V₁ (LinearMap.range f)
    | .coimg s₀ s₁ e =>
        let V₀ := denotSpaceAux σ Δ s₀
        let V₁ := denotSpaceAux σ Δ s₁
        let f := (denotTermAux σ Δ e).asLinMap V₀ V₁
        HSpace.ofSubmodule V₁
          (Submodule.orthRel V₁.innerProduct (LinearMap.range f))

  /-- `Sem⟦τ⟧σΔ` — denote a type. LN/D1: the `piTy` codomain `τ₁` binds `bvar 0`;
      the section fiber pushes the domain value onto `Δ` and recurses on `τ₁`. -/
  noncomputable def denotTyAux (σ : DEnv) (Δ : List DVal) (τ : Ty) : HType :=
    match τ with
    | .space s     => HType.hil (denotSpaceAux σ Δ s)
    | .piTy τ₀ τ₁ =>
        let T_outer : HType := denotTyAux σ Δ τ₀
        HType.sec T_outer.El (fun y : T_outer.El =>
          denotTyAux σ (T_outer.embed y :: Δ) τ₁)

  /-- `Sem⟦e⟧σΔ` — denote a term under a local de Bruijn env `Δ`. -/
  noncomputable def denotTermAux (σ : DEnv) (Δ : List DVal) (tm : Term) : DVal :=
    match tm with
    -- Bound de Bruijn index: read the local environment.
    | .bvar n => Δ.getD n DVal.default
    -- 0_s : zero of denoted space.
    | .zero s =>
        let V := denotSpaceAux σ Δ s
        .hil ⟨V, (0 : V.carrier)⟩
    -- Real literal.
    | .real r =>
        .hil ⟨HSpace.real, r⟩
    -- Scalar mult: r ∈ ℝ, v ∈ s ⇒ r • v ∈ s.
    | .smul e₀ e₁ =>
        let ⟨V₁, v₁⟩ := (denotTermAux σ Δ e₁).asHil
        .hil ⟨V₁, (denotTermAux σ Δ e₀).asReal • v₁⟩
    -- Addition: both at same space.
    | .add e₀ e₁ => (denotTermAux σ Δ e₀).addAt (denotTermAux σ Δ e₁)
    -- Inner product: V.innerProduct (intrinsic) as bilinear form, viewed in V*⊗V*.
    | .inner s =>
        let V := denotSpaceAux σ Δ s
        V.innerTensor V.innerProduct
    -- Linear application: contract V₀*⊗V₁ tensor with V₀ vector → V₁.
    | .appL s₀ s₁ e₀ e₁ =>
        let V₀ := denotSpaceAux σ Δ s₀
        let V₁ := denotSpaceAux σ Δ s₁
        let f := (denotTermAux σ Δ e₀).asLinMap V₀ V₁
        let v : V₀.carrier := (denotTermAux σ Δ e₁).atSpace V₀
        .hil ⟨V₁, f v⟩
    -- Inner-product application: e₀ : s* applied to e₁ : s yields ℝ.
    | .appI s e₀ e₁ =>
        let V := denotSpaceAux σ Δ s
        let φ := (denotTermAux σ Δ e₀).asLinFunctional V
        let v₁ : V.carrier := (denotTermAux σ Δ e₁).atSpace V
        .hil ⟨HSpace.real, φ v₁⟩
    -- Non-linear application: apply the section to the argument value.
    | .appN e₀ e₁ =>
        (denotTermAux σ Δ e₀).applyAsPi (denotTermAux σ Δ e₁)
    -- Free variable: lookup in `σ.vars` (the de Bruijn env `Δ` is for bound vars).
    | .var x =>
        (σ.vars.lookup x).getD DVal.default
    -- Pseudo-inverse on a tensor: `e : s₀*⊗s₁ ⊢ e† : s₁*⊗s₀`.
    | .pinvT s₀ s₁ e =>
        pinvTensorDVal (denotSpaceAux σ Δ s₀) (denotSpaceAux σ Δ s₁) (denotTermAux σ Δ e)
    -- Pseudo-inverse on a dual: `e : s* ⊢ e† : ℝ*⊗s`.
    | .pinvD s e =>
        pinvDualDVal (denotSpaceAux σ Δ s) (denotTermAux σ Δ e)
    -- Direct sum: pair the two component denotations.
    | .dsumE e₀ e₁ =>
        let ⟨V₀, v₀⟩ := (denotTermAux σ Δ e₀).asHil
        let ⟨V₁, v₁⟩ := (denotTermAux σ Δ e₁).asHil
        .hil ⟨HSpace.dsum V₀ V₁, (v₀, v₁)⟩
    -- Tensor product.
    | .tprodE e₀ e₁ =>
        let ⟨V₀, v₀⟩ := (denotTermAux σ Δ e₀).asHil
        let ⟨V₁, v₁⟩ := (denotTermAux σ Δ e₁).asHil
        .hil ⟨HSpace.tprod V₀ V₁, v₀ ⊗ₜ[ℝ] v₁⟩
    -- Linear λ: the codomain `s` is part of the syntax. Match on it to pick the
    -- result shape. LN/D1: the body `e` binds `bvar 0` (the linear vector) —
    -- push the fiber value onto `Δ` and recurse on `e`.
    | .llam s₀ s e =>
        let V₀ := denotSpaceAux σ Δ s₀
        match s with
        | .real =>
            llamRealDVal V₀ (fun v => (denotTermAux σ (v :: Δ) e).atSpace HSpace.real)
        | s' =>
            let V₁ := denotSpaceAux σ Δ s'
            llamTensorDVal V₀ V₁ (fun v => denotTermAux σ (v :: Δ) e)
    -- Non-linear λ: produces a section of the discrete bundle over ⟦τ₀⟧σ.
    | .nllam τ₀ e =>
        let T_outer : HType := denotTyAux σ Δ τ₀
        .pi T_outer.El (fun y : T_outer.El =>
          denotTermAux σ (T_outer.embed y :: Δ) e)
    -- Subspace inclusion `embed_s : s* ⊗ s_amb`, where `s` must be one of the
    -- four fundamental-subspace constructors. An unrecognised `s` falls back to
    -- `DVal.default`.
    | .embed s =>
        match s with
        | .ker s₀_amb s₁ e =>
            let V₀_amb := denotSpaceAux σ Δ s₀_amb
            let V₁ := denotSpaceAux σ Δ s₁
            let f := (denotTermAux σ Δ e).asLinMap V₀_amb V₁
            let V_sub := HSpace.ofSubmodule V₀_amb (LinearMap.ker f)
            embedDVal V_sub V₀_amb (LinearMap.ker f).subtype
        | .coker s₀_amb s₁ e =>
            let V₀_amb := denotSpaceAux σ Δ s₀_amb
            let V₁ := denotSpaceAux σ Δ s₁
            let f := (denotTermAux σ Δ e).asLinMap V₀_amb V₁
            let K := Submodule.orthRel V₀_amb.innerProduct (LinearMap.ker f)
            let V_sub := HSpace.ofSubmodule V₀_amb K
            embedDVal V_sub V₀_amb K.subtype
        | .img s₀ s₁_amb e =>
            let V₀ := denotSpaceAux σ Δ s₀
            let V₁_amb := denotSpaceAux σ Δ s₁_amb
            let f := (denotTermAux σ Δ e).asLinMap V₀ V₁_amb
            let V_sub := HSpace.ofSubmodule V₁_amb (LinearMap.range f)
            embedDVal V_sub V₁_amb (LinearMap.range f).subtype
        | .coimg s₀ s₁_amb e =>
            let V₀ := denotSpaceAux σ Δ s₀
            let V₁_amb := denotSpaceAux σ Δ s₁_amb
            let f := (denotTermAux σ Δ e).asLinMap V₀ V₁_amb
            let K := Submodule.orthRel V₁_amb.innerProduct (LinearMap.range f)
            let V_sub := HSpace.ofSubmodule V₁_amb K
            embedDVal V_sub V₁_amb K.subtype
        | _ => DVal.default

end

/-! ## Closed-term denotation wrappers (`Δ = []`). -/

/-- `Sem⟦s⟧σ` on a closed space (no dangling `bvar`). -/
@[reducible] noncomputable def denotSpace (σ : DEnv) (s : Space) : HSpace :=
  denotSpaceAux σ [] s
/-- `Sem⟦τ⟧σ` on a closed type. -/
@[reducible] noncomputable def denotTy (σ : DEnv) (τ : Ty) : HType :=
  denotTyAux σ [] τ
/-- `Sem⟦e⟧σ` on a closed term. -/
@[reducible] noncomputable def denotTerm (σ : DEnv) (e : Term) : DVal :=
  denotTermAux σ [] e

end GLang
