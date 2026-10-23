import GLang.Proofs.Adequacy.Partial.Source.PartialSourceArms
import GLang.Proofs.Adequacy.Raw.RawSpaceFFSAdequacy

/-! Partial fundamental-subspace dimension adequacy. Rank is obtained from the
actual successful compiled matrix and its source coordinate expansion. -/
namespace GLang.PartialAdequacy
open scoped TensorProduct

variable {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
  {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}

theorem reshape_space {s : Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {e : ValExpr}
    (h : ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) B x
      (denotValB_partial orc ρ Γ Δ e)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) B x
      (denotValB_partial orc ρ Γ Δ (.reshap e (.space sv) (.space sv))) := by
  obtain ⟨v,he,ha⟩ := h
  obtain ⟨a,n,rfl,hd,_,hlen,_⟩ := ha.array
  refine ⟨.array a,?_,ha⟩
  rw [denotValB_partial, he]
  simp [PartialValueEval.reshapeInferred, PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, hd, hlen]

/-- All four oracle observations have the rank of the source map. The query
uses the real partial evaluator, including the explicit storage-length check. -/
theorem ffs_oracle {s₀ s₁ : Space} {sv : ValSpace} {e : ValExpr} {x : DVal}
    {vs₀ : List (denotSpaceAux σ Ds s₀).carrier}
    {vs₁ : List (denotSpaceAux σ Ds s₁).carrier}
    (hb₀ : IsListBasis (denotSpaceAux σ Ds s₀) vs₀)
    (hb₁ : IsListBasis (denotSpaceAux σ Ds s₁) vs₁)
    (hs : sv.shpOfPartial (PartialDirectOracle.oracle ρ Γ Δ) =
      .ok [vs₀.length, vs₁.length])
    (h : ResultAgree PartialDirectOracle.oracle σ ρ Ds Γ Δ
      (.space (.tprod (.dual s₀) s₁)) (.space sv)
      (.vecs (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s₀)) (denotSpaceAux σ Ds s₁))
        (HSpace.tprodOfLists _ _ ((denotSpaceAux σ Ds s₀).dualOfList vs₀) vs₁))
      x (denotValB_partial PartialDirectOracle.oracle ρ Γ Δ e))
    (p : ValFFSProp)
    (hf : ValueQueryDependencies.Finite (.space Γ (.ffs p sv e))) :
    PartialDirectOracle.oracle ρ Γ Δ p sv e =
      .ok (ffsDim p [vs₀.length, vs₁.length]
        (Module.finrank ℝ (LinearMap.range
          (x.asLinMap (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁))))) := by
  obtain ⟨v,he,ha⟩ := h
  obtain ⟨a,n,rfl,hd,_,hlen,hcoords⟩ := ha.array
  have hd' : sv.dofPartial (PartialDirectOracle.oracle ρ Γ Δ) =
      .ok (vs₀.length * vs₁.length) := by
    simp [ValSpace.dofPartial, hs, bind, Except.bind, pure, Except.pure]
  have hn : n = vs₀.length * vs₁.length := Except.ok.inj (hd.symm.trans hd')
  rw [hn] at hlen hcoords
  rw [PartialDirectLocality.oracle_matrix ρ Γ Δ p sv e _ _ a hf hs he hlen]
  congr 2
  rw [RawSpaceFFS.asLinMap_eq_dualTensorHom_atSpace]
  apply RawSpaceFFS.rank_denotAsMatrix_of_tprodOfLists_dual hb₀ hb₁ a.get
  simpa only [denotSpaceAux, BasisDenot.atSpace_vecs_self] using hcoords

/-- Source syntax corresponding to each of the four matrix observations. -/
def fundamentalSpace (p : ValFFSProp) (s₀ s₁ : Space) (t : Term) : Space :=
  match p with
  | .kernel => .ker s₀ s₁ t
  | .cokernel => .coker s₀ s₁ t
  | .image => .img s₀ s₁ t
  | .coimage => .coimg s₀ s₁ t

private theorem fundamental_shape (p : ValFFSProp) (s₀ s₁ : Space) (t : Term) :
    [ffsDim p [Module.finrank ℝ (denotSpaceAux σ Ds s₀).carrier,
      Module.finrank ℝ (denotSpaceAux σ Ds s₁).carrier]
      (Module.finrank ℝ (LinearMap.range
        ((denotTermAux σ Ds t).asLinMap (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁))))] =
    srcShp σ Ds (fundamentalSpace p s₀ s₁ t) := by
  have hr := LinearMap.finrank_range_add_finrank_ker
    ((denotTermAux σ Ds t).asLinMap (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁))
  have hk := (denotSpaceAux σ Ds s₀).finrank_add_finrank_orthRel
    (LinearMap.ker ((denotTermAux σ Ds t).asLinMap
      (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁)))
  have hi := (denotSpaceAux σ Ds s₁).finrank_add_finrank_orthRel
    (LinearMap.range ((denotTermAux σ Ds t).asLinMap
      (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁)))
  have hc : Module.finrank ℝ (LinearMap.range
      ((denotTermAux σ Ds t).asLinMap (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁))) =
      Module.finrank ℝ (Submodule.orthRel (denotSpaceAux σ Ds s₀).innerProduct
        (LinearMap.ker ((denotTermAux σ Ds t).asLinMap
          (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁)))) := by omega
  cases p with
  | kernel =>
    simp only [fundamentalSpace, srcShp, ffsDim, denotSpaceAux]
    congr 1
    exact Nat.sub_eq_of_eq_add (hr.symm.trans (Nat.add_comm _ _))
  | cokernel =>
    simp only [fundamentalSpace, srcShp, ffsDim, denotSpaceAux]
    exact congrArg (fun n => [n]) hc
  | image =>
    simp only [fundamentalSpace, srcShp, ffsDim, denotSpaceAux]
    rfl
  | coimage =>
    simp only [fundamentalSpace, srcShp, ffsDim, denotSpaceAux]
    congr 1
    exact Nat.sub_eq_of_eq_add (hi.symm.trans (Nat.add_comm _ _))

/-- The four FFS space arms: source shape and actual partial compiled-witness
agreement imply the complete successful subspace shape. -/
theorem ffs_shape {s₀ s₁ : Space} {sv : ValSpace} {e : ValExpr} {t : Term}
    {vs₀ : List (denotSpaceAux σ Ds s₀).carrier}
    {vs₁ : List (denotSpaceAux σ Ds s₁).carrier}
    (hb₀ : IsListBasis (denotSpaceAux σ Ds s₀) vs₀)
    (hb₁ : IsListBasis (denotSpaceAux σ Ds s₁) vs₁)
    (hs : sv.shpOfPartial (PartialDirectOracle.oracle ρ Γ Δ) =
      .ok (srcShp σ Ds (.tprod (.dual s₀) s₁)))
    (h : ResultAgree PartialDirectOracle.oracle σ ρ Ds Γ Δ
      (.space (.tprod (.dual s₀) s₁)) (.space sv)
      (.vecs (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s₀)) (denotSpaceAux σ Ds s₁))
        (HSpace.tprodOfLists _ _ ((denotSpaceAux σ Ds s₀).dualOfList vs₀) vs₁))
      (denotTermAux σ Ds t) (denotValB_partial PartialDirectOracle.oracle ρ Γ Δ e))
    (p : ValFFSProp)
    (hf : ValueQueryDependencies.Finite (.space Γ (.ffs p sv e))) :
    ValSpace.shpOfPartial (PartialDirectOracle.oracle ρ Γ Δ) (.ffs p sv e) =
      .ok (srcShp σ Ds (fundamentalSpace p s₀ s₁ t)) := by
  have hsd : sv.shpOfPartial (PartialDirectOracle.oracle ρ Γ Δ) =
      .ok [vs₀.length, vs₁.length] := by
    simpa only [srcShp, RawSpaceFFS.finrank_denotSpaceAux_dual,
      hb₀.finrank_eq, hb₁.finrank_eq] using hs
  rw [ValSpace.shpOfPartial, ffs_oracle hb₀ hb₁ hsd h p hf]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [← hb₀.finrank_eq, ← hb₁.finrank_eq, fundamental_shape]

theorem shape_dof {s : Space} {sv : ValSpace}
    (h : sv.shpOfPartial (orc ρ Γ Δ) = .ok (srcShp σ Ds s)) :
    sv.dofPartial (orc ρ Γ Δ) =
      .ok (Module.finrank ℝ (denotSpaceAux σ Ds s).carrier) := by
  rw [ValSpace.dofPartial, h]
  simp only [bind, Except.bind, pure, Except.pure, raw_srcShp_foldr]

theorem space_real : ValSpace.shpOfPartial (orc ρ Γ Δ) .real =
    .ok (srcShp σ Ds .real) := by simp [ValSpace.shpOfPartial, srcShp]

theorem space_empty : ValSpace.shpOfPartial (orc ρ Γ Δ) .empty =
    .ok (srcShp σ Ds .empty) := by simp [ValSpace.shpOfPartial, srcShp]

theorem space_dual {s : Space} {sv : ValSpace}
    (h : sv.shpOfPartial (orc ρ Γ Δ) = .ok (srcShp σ Ds s)) :
    sv.shpOfPartial (orc ρ Γ Δ) = .ok (srcShp σ Ds (.dual s)) := by
  simpa only [srcShp] using h

theorem space_dsum {s₀ s₁ : Space} {sv₀ sv₁ : ValSpace}
    (h₀ : sv₀.shpOfPartial (orc ρ Γ Δ) = .ok (srcShp σ Ds s₀))
    (h₁ : sv₁.shpOfPartial (orc ρ Γ Δ) = .ok (srcShp σ Ds s₁)) :
    ValSpace.shpOfPartial (orc ρ Γ Δ) (.dsum sv₀ sv₁) =
      .ok (srcShp σ Ds (.dsum s₀ s₁)) := by
  rw [ValSpace.shpOfPartial, shape_dof h₀]
  simp only [shape_dof h₁, bind, Except.bind, pure, Except.pure, srcShp]

theorem space_tprod {s₀ s₁ : Space} {sv₀ sv₁ : ValSpace}
    (h₀ : sv₀.shpOfPartial (orc ρ Γ Δ) = .ok (srcShp σ Ds s₀))
    (h₁ : sv₁.shpOfPartial (orc ρ Γ Δ) = .ok (srcShp σ Ds s₁)) :
    ValSpace.shpOfPartial (orc ρ Γ Δ) (.tprod sv₀ sv₁) =
      .ok (srcShp σ Ds (.tprod s₀ s₁)) := by
  rw [ValSpace.shpOfPartial, shape_dof h₀]
  simp only [shape_dof h₁, bind, Except.bind, pure, Except.pure, srcShp]

end GLang.PartialAdequacy
