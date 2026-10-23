import GLang.Proofs.Source.Soundness
import GLang.Graded.Regularity

namespace GLang

/-! ## Pointwise linearity through dependent sections -/

/-- A map from a Hilbert space into a semantic type is pointwise linear when it is
linear at a Hilbert-space leaf, and remains pointwise linear after fixing any
argument of a dependent section.  Thus nested dependent functions are checked all
the way down to their vector-valued leaves. -/
def HType.PointwiseLinear (V : HSpace) :
    (T : HType) → (V.carrier → T.El) → Prop
  | .hil W, f =>
      IsLinearMap ℝ (show V.carrier → W.carrier from f)
  | .sec A fibers, f =>
      ∀ a : A, (fibers a).PointwiseLinear V (fun y => f y a)

/-- Meaningful higher-order replacement for `LinearAtVar`.

At a space result this is definitionally the established `LinearAtVar` predicate.
At a dependent-function result, the untyped denotation is extracted at its expected
semantic type and required to be pointwise linear through every dependent argument.
The extraction makes the predicate total on raw denotations; in the theorem below,
source typing proves that there is no retained linear `x` at a function result, so
this well-defined semantic obligation is never invoked through a mismatched value. -/
noncomputable def HigherOrderLinearAtVar
    (σ : DEnv) (x : Name) (s : Space) (e : Term) : Ty → Prop
  | .space sOut => LinearAtVar σ x s e (.space sOut)
  | tau@(.piTy _ _) =>
      let T := denotTy σ tau
      T.PointwiseLinear (denotSpace σ s) (fun y =>
        T.extract (denotTerm (σ.bind x (.hil ⟨denotSpace σ s, y⟩)) e))

/-! ## The source context-validity premise omitted from `CtxWF` -/

structure SourceCtxValid (Δ : LCtx) (Γ : NLCtx) : Type where
  linear : ∀ x s, Δ.lookup x = some s → SValid Γ s
  nonlinear : ∀ x τ, Γ.lookup x = some τ → Σ k, TValid Γ τ k

/-! ## Dependent-function typing cannot retain a linear context -/

private theorem right_empty_of_union_empty {A : Type}
    {left right : Finmap (fun _ : Name => A)}
    (h : left ∪ right = (∅ : Finmap (fun _ : Name => A))) :
    right = (∅ : Finmap (fun _ : Name => A)) := by
  apply Finmap.ext_lookup
  intro x
  rw [Finmap.lookup_empty]
  cases hx : right.lookup x with
  | none => rfl
  | some value =>
      have hm : x ∈ left ∪ right := Finmap.mem_union.mpr
        (Or.inr (Finmap.mem_of_lookup_eq_some hx))
      rw [h] at hm
      exact False.elim (Finmap.notMem_empty hm)

private def PiResultLinearContextMotive
    (Δ : LCtx) (_Γ : NLCtx) (_e : Term) (τ : Ty)
    (_h : HasType Δ _Γ _e τ) : Prop :=
  ∀ τIn τOut, τ = .piTy τIn τOut → Δ = ∅

/-- A source term with dependent-function result type has no linear assumptions. -/
theorem HasType.piResultLinearContextEmpty
    {Δ : LCtx} {Γ : NLCtx} {e : Term} {τIn τOut : Ty}
    (h : HasType Δ Γ e (.piTy τIn τOut)) : Δ = ∅ := by
  have result := HasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := PiResultLinearContextMotive)
    ?svEmpty ?svReal ?svDual ?svDsum ?svTprod
    ?svKer ?svCoker ?svImg ?svCoimg
    ?tvSpace ?tvPi
    ?subKer ?subCoker ?subImg ?subCoimg
    ?termZero ?termSmul ?termAdd ?termInner ?termReal
    ?termAppL ?termAppI ?termAppN ?termVarL ?termVarN
    ?termPinvT ?termPinvD ?termPromote ?termDsum ?termTprod
    ?termLlamReal ?termLlamTensor ?termEmbed ?termNllam h
  case termPromote =>
    intro Δ Γ e τ lin hDisjΔ hDisjΓ hFresh hInner ih
      codIn codOut hτ
    exact right_empty_of_union_empty (ih codIn codOut hτ)
  all_goals try simp [PiResultLinearContextMotive]
  exact result τIn τOut rfl

/-- Full source soundness payload: result-type formation, deep denotational shape,
and a non-vacuous semantic definition of higher-order pointwise linearity. -/
structure StrongSourceSoundClaim
    (σ : DEnv) (Δ : LCtx) (Γ : NLCtx) (e : Term) (τ : Ty) : Type where
  resultTypeValid : Σ k, TValid Γ τ k
  matchesShape : (denotTerm σ e).matchesShape (denotTy σ τ)
  higherOrderLinear :
    ∀ x s, Δ.lookup x = some s → HigherOrderLinearAtVar σ x s e τ

/-- Proof-irrelevant public view of `StrongSourceSoundClaim`.

The `Nonempty` truncation keeps the claim in `Prop` while still saying that the
result type has an actual formation derivation at some kind.  The Type-valued
structure above remains available to clients that need to consume that derivation. -/
def StrongSourceSoundProp
    (σ : DEnv) (Δ : LCtx) (Γ : NLCtx) (e : Term) (τ : Ty) : Prop :=
  (∃ k, Nonempty (TValid Γ τ k)) ∧
  (denotTerm σ e).matchesShape (denotTy σ τ) ∧
  ∀ x s, Δ.lookup x = some s → HigherOrderLinearAtVar σ x s e τ

/-- Forget the computational payload of strong soundness while retaining every
mathematical assertion. -/
theorem StrongSourceSoundClaim.toProp
    {σ : DEnv} {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty}
    (h : StrongSourceSoundClaim σ Δ Γ e τ) :
    StrongSourceSoundProp σ Δ Γ e τ := by
  refine ⟨⟨h.resultTypeValid.1, ⟨h.resultTypeValid.2⟩⟩,
    h.matchesShape, h.higherOrderLinear⟩

/-- Projection of strengthened soundness to `SoundClaim`. -/
theorem StrongSourceSoundClaim.toSoundClaim
    {σ : DEnv} {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty}
    (h : StrongSourceSoundClaim σ Δ Γ e τ) : SoundClaim σ Δ e τ := by
  refine ⟨h.matchesShape, ?_⟩
  intro x s hx
  cases τ with
  | space sOut => exact h.higherOrderLinear x s hx
  | piTy τIn τOut => trivial

/-- Source soundness under context formation, including result-type validity and pointwise semantic linearity. -/
noncomputable def strongSourceSoundness
    {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty}
    (d : HasType Δ Γ e τ)
    {σ : DEnv} (ctx : CtxWF Δ Γ) (wf : EnvWF σ Δ Γ)
    (ctxValid : SourceCtxValid Δ Γ) :
    StrongSourceSoundClaim σ Δ Γ e τ := by
  have oldSound : SoundClaim σ Δ e τ := soundness d ctx wf
  have gradedCtxValid : Graded.CtxValid (Graded.tr Δ Γ) :=
    Graded.ctxValid_tr ctx.disjoint ctxValid.linear ctxValid.nonlinear
  refine {
    resultTypeValid := Graded.hasType_regular ctx.disjoint gradedCtxValid d
    matchesShape := oldSound.1
    higherOrderLinear := ?_
  }
  intro x s hx
  cases τ with
  | space sOut => exact oldSound.2 x s hx
  | piTy τIn τOut =>
      have hEmpty : Δ = ∅ := d.piResultLinearContextEmpty
      rw [hEmpty, Finmap.lookup_empty] at hx
      contradiction

/-- Prop-valued public form of strengthened source soundness. -/
theorem strongSourceSoundnessProp
    {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty}
    (d : HasType Δ Γ e τ)
    {σ : DEnv} (ctx : CtxWF Δ Γ) (wf : EnvWF σ Δ Γ)
    (ctxValid : SourceCtxValid Δ Γ) :
    StrongSourceSoundProp σ Δ Γ e τ :=
  (strongSourceSoundness d ctx wf ctxValid).toProp

/-- Strengthened soundness implies `SoundClaim`. -/
theorem strongSourceSoundness_toSoundClaim
    {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty}
    (d : HasType Δ Γ e τ)
    {σ : DEnv} (ctx : CtxWF Δ Γ) (wf : EnvWF σ Δ Γ)
    (ctxValid : SourceCtxValid Δ Γ) :
    SoundClaim σ Δ e τ :=
  (strongSourceSoundness d ctx wf ctxValid).toSoundClaim

end GLang
