import GLang.Examples.TangentAreaGeometry
import GLang.Examples.TangentProjectedArea

namespace GLang.Examples.TangentCoordinates
open scoped TensorProduct

private theorem antiSymBody_denot (σ : DEnv) (V : HSpace) (a b : V.carrier) :
    denotTermAux σ [.hil ⟨V, b⟩, .hil ⟨V, a⟩]
      (antiSymBody (.bvar 1) (.bvar 0)) =
      .hil ⟨HSpace.tprod V V, antisymMap V (a ⊗ₜ[ℝ] b)⟩ := by
  have hn : denotTermAux σ [.hil ⟨V, b⟩, .hil ⟨V, a⟩]
      (.smul (.real (-1)) (.tprodE (.bvar 0) (.bvar 1))) =
      .hil ⟨HSpace.tprod V V, -(b ⊗ₜ[ℝ] a)⟩ := by
    change DVal.hil ⟨HSpace.tprod V V,
      (DVal.hil ⟨HSpace.real, (-1 : ℝ)⟩).asReal • (b ⊗ₜ[ℝ] a)⟩ = _
    rw [DVal.asReal_hil_real]
    simp
  have hadd : denotTermAux σ [.hil ⟨V, b⟩, .hil ⟨V, a⟩]
      (.add (.tprodE (.bvar 1) (.bvar 0))
        (.smul (.real (-1)) (.tprodE (.bvar 0) (.bvar 1)))) =
      .hil ⟨HSpace.tprod V V, a ⊗ₜ[ℝ] b - b ⊗ₜ[ℝ] a⟩ := by
    change (DVal.hil ⟨HSpace.tprod V V, a ⊗ₜ[ℝ] b⟩).addAt
      (denotTermAux σ [.hil ⟨V, b⟩, .hil ⟨V, a⟩]
        (.smul (.real (-1)) (.tprodE (.bvar 0) (.bvar 1)))) = _
    rw [hn, DVal.addAt_hil_hil]
    rfl
  unfold antiSymBody
  rw [denotTermAux, hadd]
  change DVal.hil ⟨HSpace.tprod V V,
    (DVal.hil ⟨HSpace.real, (1 / 2 : ℝ)⟩).asReal • (a ⊗ₜ[ℝ] b - b ⊗ₜ[ℝ] a)⟩ = _
  rw [DVal.asReal_hil_real, antisymMap_tmul]

private theorem antiSym_denot_contract {σ : DEnv} {Γ : NLCtx} {s : Space}
    (hs : SValid Γ s) (hctx : CtxWF ∅ Γ) (henv : EnvWF σ ∅ Γ)
    (a b : (denotSpace σ s).carrier) :
    dualTensorHom ℝ (denotSpace σ s).carrier (HSpace.tprod (denotSpace σ s) (denotSpace σ s)).carrier
      (dualTensorHom ℝ (denotSpace σ s).carrier
        (denotSpace σ (.tprod (.dual s) (.tprod s s))).carrier
        ((denotTerm σ (antiSym s)).atSpace
          (denotSpace σ (.tprod (.dual s) (.tprod (.dual s) (.tprod s s))))) a) b =
      antisymMap (denotSpace σ s) (a ⊗ₜ[ℝ] b) := by
  let V := denotSpace σ s
  let T := HSpace.tprod V V
  have hmatch := (soundness (antiSym_hasType hs) hctx henv).1
  change (denotTerm σ (antiSym s)).matchesShape
    (.hil (HSpace.tprod (HSpace.dual V) (HSpace.tprod (HSpace.dual V) T))) at hmatch
  change dualTensorHom ℝ V.carrier T.carrier
    (dualTensorHom ℝ V.carrier (HSpace.tprod (HSpace.dual V) T).carrier
      ((denotTerm σ (antiSym s)).atSpace
        (HSpace.tprod (HSpace.dual V) (HSpace.tprod (HSpace.dual V) T))) a) b = _
  rw [← DVal.asLinMap_eq_of_matchesShape hmatch]
  have hlin := denot_llam_tensor_body_isLinear (antiSym_hasType hs) hctx henv
  change IsLinearMap ℝ (fun x : V.carrier =>
    (denotTermAux σ [.hil ⟨V, x⟩]
      (.llam s (.tprod s s) (antiSymBody (.bvar 1) (.bvar 0)))).atSpace
        (HSpace.tprod (HSpace.dual V) T)) at hlin
  rw [antiSym, denotTerm_llam_non_real (by intro h; cases h)]
  change dualTensorHom ℝ V.carrier T.carrier
    ((llamTensorDVal V (HSpace.tprod (HSpace.dual V) T)
      (fun z => denotTermAux σ [z]
        (.llam s (.tprod s s) (antiSymBody (.bvar 1) (.bvar 0))))).asLinMap
      V (HSpace.tprod (HSpace.dual V) T) a) b = _
  rw [asLinMap_llamTensorDVal, LinearMap.ofFun_apply_of_isLinearMap hlin]
  have hinner : denotTermAux σ [.hil ⟨V, a⟩]
      (.llam s (.tprod s s) (antiSymBody (.bvar 1) (.bvar 0))) =
      llamTensorDVal V T
        (fun z => denotTermAux σ [z, .hil ⟨V, a⟩] (antiSymBody (.bvar 1) (.bvar 0))) := by
    simp only [denotTermAux]
    rw [denotSpaceAux_lc_irrel hs.lc σ [.hil ⟨V, a⟩] [],
      denotSpaceAux_lc_irrel (SValid.lc (.tprod hs hs)) σ [.hil ⟨V, a⟩] []]
    rfl
  rw [hinner]
  have hbody (z : V.carrier) :
      (denotTermAux σ [.hil ⟨V, z⟩, .hil ⟨V, a⟩]
        (antiSymBody (.bvar 1) (.bvar 0))).atSpace T =
        ((antisymMap V).comp (TensorProduct.mk ℝ V.carrier V.carrier a)) z := by
    rw [antiSymBody_denot]
    exact atSpace_hil_self _ _
  have hinnerLinear : IsLinearMap ℝ (fun z : V.carrier =>
      (denotTermAux σ [.hil ⟨V, z⟩, .hil ⟨V, a⟩]
        (antiSymBody (.bvar 1) (.bvar 0))).atSpace T) := by
    constructor
    · intro x y; simp only [hbody, map_add]
    · intro r x; simp only [hbody, map_smul]
  have hm : (llamTensorDVal V T
      (fun z => denotTermAux σ [z, .hil ⟨V, a⟩]
        (antiSymBody (.bvar 1) (.bvar 0)))).matchesShape
      (.hil (HSpace.tprod (HSpace.dual V) T)) := by rfl
  rw [← DVal.asLinMap_eq_of_matchesShape hm, asLinMap_llamTensorDVal,
    LinearMap.ofFun_apply_of_isLinearMap hinnerLinear, hbody]
  rfl

/-- The literal derived source term is the normalized antisymmetrizer. -/
theorem antiSymLinear_denot {σ : DEnv} {Γ : NLCtx} {s : Space}
    (fresh : IofFresh Γ) (hs : SValid Γ s)
    (hctx : CtxWF ∅ Γ) (henv : EnvWF σ ∅ Γ) :
    (denotTerm σ (antiSymLinear s)).asLinMap
      (HSpace.tprod (denotSpace σ s) (denotSpace σ s))
      (HSpace.tprod (denotSpace σ s) (denotSpace σ s)) =
      antisymMap (denotSpace σ s) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change (denotTerm σ (antiSymLinear s)).asLinMap
    (HSpace.tprod (denotSpace σ s) (denotSpace σ s))
    (HSpace.tprod (denotSpace σ s) (denotSpace σ s)) (a ⊗ₜ[ℝ] b) = _
  exact (applyUncurry2NonReal_denot_tmul fresh (by intro h; cases h)
    hs hs (.tprod hs hs) henv hctx (antiSym s) a b).trans
      (antiSym_denot_contract hs hctx henv a b)

noncomputable abbrev areaHSpace (V : HSpace) : HSpace :=
  HSpace.ofSubmodule (HSpace.tprod V V) (antisymMap V).range

theorem areaSpace_denot {σ : DEnv} {Γ : NLCtx} {s : Space}
    (fresh : IofFresh Γ) (hs : SValid Γ s)
    (hctx : CtxWF ∅ Γ) (henv : EnvWF σ ∅ Γ) :
    denotSpace σ (areaSpace s) = areaHSpace (denotSpace σ s) := by
  change HSpace.ofSubmodule (HSpace.tprod (denotSpace σ s) (denotSpace σ s))
    ((denotTerm σ (antiSymLinear s)).asLinMap
      (HSpace.tprod (denotSpace σ s) (denotSpace σ s))
      (HSpace.tprod (denotSpace σ s) (denotSpace σ s))).range = _
  rw [antiSymLinear_denot fresh hs hctx henv]

/-- The original projected source term, including derived uncurrying and the
Moore inverse of the image inclusion, denotes normalized antisymmetrization. -/
theorem projectedArea_denot {σ : DEnv} {Γ : NLCtx} {s : Space}
    (fresh : IofFresh Γ) (hs : SValid Γ s)
    (hctx : CtxWF ∅ Γ) (henv : EnvWF σ ∅ Γ)
    {v w : Term} {x y : (denotSpace σ s).carrier}
    (hv : denotTerm σ v = .hil ⟨denotSpace σ s, x⟩)
    (hw : denotTerm σ w = .hil ⟨denotSpace σ s, y⟩) :
    denotTerm σ (projectedArea s v w) =
      .hil ⟨areaHSpace (denotSpace σ s),
        (antisymMap (denotSpace σ s)).rangeRestrict (x ⊗ₜ[ℝ] y)⟩ := by
  let V := denotSpace σ s
  let T := HSpace.tprod V V
  have ht : denotTerm σ (.tprodE v w) = .hil ⟨T, x ⊗ₜ[ℝ] y⟩ := by
    change (let p := (denotTerm σ v).asHil
            let q := (denotTerm σ w).asHil
            DVal.hil ⟨HSpace.tprod p.fst q.fst, p.snd ⊗ₜ[ℝ] q.snd⟩) = _
    rw [hv, hw]
    rfl
  have hp : denotTerm σ (Term.lproj (areaSpace s) (.tprod s s)) =
      pinvTensorDVal (areaHSpace V) T
        (embedDVal (areaHSpace V) T (antisymMap V).range.subtype) := by
    change pinvTensorDVal
      (HSpace.ofSubmodule T ((denotTerm σ (antiSymLinear s)).asLinMap T T).range) T
      (embedDVal (HSpace.ofSubmodule T ((denotTerm σ (antiSymLinear s)).asLinMap T T).range)
        T ((denotTerm σ (antiSymLinear s)).asLinMap T T).range.subtype) = _
    have hmap : (denotTerm σ (antiSymLinear s)).asLinMap T T = antisymMap V :=
      antiSymLinear_denot fresh hs hctx henv
    rw [hmap]
  rw [projectedArea, denotTerm_appL, areaSpace_denot fresh hs hctx henv, ht, hp]
  change DVal.hil ⟨areaHSpace V,
    (pinvTensorDVal (areaHSpace V) T (embedDVal (areaHSpace V) T
      (antisymMap V).range.subtype)).asLinMap T (areaHSpace V)
      ((DVal.hil ⟨T, x ⊗ₜ[ℝ] y⟩).atSpace T)⟩ = _
  rw [asLinMap_pinvTensorDVal, asLinMap_embedDVal, atSpace_hil_self,
    antisymMap_projection]

/-- Exact denotation of the source's completed projected basis. The fallback
is retained in the source syntax and proved redundant at genuine rank two. -/
theorem projectedAreaBasis_denot {σ : DEnv} {Γ : NLCtx} {base : Basis}
    (fresh : IofFresh Γ) (hs : SValid Γ base.sof)
    (hctx : CtxWF ∅ Γ) (henv : EnvWF σ ∅ Γ)
    (b : Module.Basis (Fin 2) ℝ (denotSpace σ base.sof).carrier)
    {u₀ u₁ : Term}
    (h₀ : denotTerm σ u₀ = .hil ⟨denotSpace σ base.sof, b 0⟩)
    (h₁ : denotTerm σ u₁ = .hil ⟨denotSpace σ base.sof, b 1⟩) :
    denotBasis σ (projectedAreaBasis base u₀ u₁) =
      .vecs (areaHSpace (denotSpace σ base.sof))
        [areaGenerator (denotSpace σ base.sof) b] := by
  unfold projectedAreaBasis
  rw [denotBasis]
  let S := areaSpace base.sof
  change BasisDenot.vecs (denotSpace σ S)
    ((denotSpace σ S).lexInd
      ([(denotTerm σ (projectedArea base.sof u₀ u₀)).atSpace (denotSpace σ S),
        (denotTerm σ (projectedArea base.sof u₀ u₁)).atSpace (denotSpace σ S),
        (denotTerm σ (projectedArea base.sof u₁ u₀)).atSpace (denotSpace σ S),
        (denotTerm σ (projectedArea base.sof u₁ u₁)).atSpace (denotSpace σ S)] ++
        (denotBasis σ (areaFallback base)).atSpace (denotSpace σ S))) = _
  have hS : denotSpace σ S = areaHSpace (denotSpace σ base.sof) :=
    areaSpace_denot fresh hs hctx henv
  rw [hS, projectedArea_denot fresh hs hctx henv h₀ h₀,
    projectedArea_denot fresh hs hctx henv h₀ h₁,
    projectedArea_denot fresh hs hctx henv h₁ h₀,
    projectedArea_denot fresh hs hctx henv h₁ h₁]
  simp only [atSpace_hil_self]
  rw [projectedArea_lexInd]

end GLang.Examples.TangentCoordinates
