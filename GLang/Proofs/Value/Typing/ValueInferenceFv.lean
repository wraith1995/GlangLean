import GLang.Proofs.Value.Binding.ValueBetaFv
import GLang.Value.Inference

set_option maxHeartbeats 3000000
namespace GLang

private theorem spaceOf_fv (t : ValTy) : t.spaceOf.fv ⊆ t.fv := by
  cases t <;> simp [ValTy.spaceOf, ValTy.fv, ValSpace.fv]

/-- Recovering the type cannot introduce a new free variable. -/
theorem ValExpr.fv_inferType_subset : ∀ e : ValExpr,
    (ValExpr.inferType e).fv ⊆ e.fv
  | .bvar i => by
    intro z hz
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .var y t => by
    intro z hz
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .vlam t0 t1 e => by
    intro z hz
    have hi2 := @ValExpr.fv_inferType_subset e z
    have hs2 := @spaceOf_fv (ValExpr.inferType e) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .zero s => by
    intro z hz
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .rlit r => by
    intro z hz
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .scale e0 e1 => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e0 z
    have hs0 := @spaceOf_fv (ValExpr.inferType e0) z
    have hi1 := @ValExpr.fv_inferType_subset e1 z
    have hs1 := @spaceOf_fv (ValExpr.inferType e1) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .dsumE e0 e1 => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e0 z
    have hs0 := @spaceOf_fv (ValExpr.inferType e0) z
    have hi1 := @ValExpr.fv_inferType_subset e1 z
    have hs1 := @spaceOf_fv (ValExpr.inferType e1) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .tprodE e0 e1 => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e0 z
    have hs0 := @spaceOf_fv (ValExpr.inferType e0) z
    have hi1 := @ValExpr.fv_inferType_subset e1 z
    have hs1 := @spaceOf_fv (ValExpr.inferType e1) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .appV e0 e1 => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e0 z
    have hs0 := @spaceOf_fv (ValExpr.inferType e0) z
    have hi1 := @ValExpr.fv_inferType_subset e1 z
    have hs1 := @spaceOf_fv (ValExpr.inferType e1) z
    simp only [ValExpr.inferType] at hz
    split at hz
    · rename_i d c heq
      have hh := ValTy.fv_substBound_subset e1 c 0 hz
      simp only [heq, ValTy.fv, Finset.mem_union] at hi0
      simp only [ValExpr.fv, Finset.mem_union]
      rcases Finset.mem_union.mp hh with hc | ha
      · exact Or.inl (hi0 (Or.inr hc))
      · exact Or.inr ha
    · simpa [ValTy.fv, ValSpace.fv] using hz
  | .vkrn e0 e1 => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e0 z
    have hs0 := @spaceOf_fv (ValExpr.inferType e0) z
    have hi1 := @ValExpr.fv_inferType_subset e1 z
    have hs1 := @spaceOf_fv (ValExpr.inferType e1) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .vblk e0 e1 => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e0 z
    have hs0 := @spaceOf_fv (ValExpr.inferType e0) z
    have hi1 := @ValExpr.fv_inferType_subset e1 z
    have hs1 := @spaceOf_fv (ValExpr.inferType e1) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .rrefRep e0 e1 => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e0 z
    have hs0 := @spaceOf_fv (ValExpr.inferType e0) z
    have hi1 := @ValExpr.fv_inferType_subset e1 z
    have hs1 := @spaceOf_fv (ValExpr.inferType e1) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .vadd s e0 e1 => by
    intro z hz
    have hi1 := @ValExpr.fv_inferType_subset e0 z
    have hs1 := @spaceOf_fv (ValExpr.inferType e0) z
    have hi2 := @ValExpr.fv_inferType_subset e1 z
    have hs2 := @spaceOf_fv (ValExpr.inferType e1) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .delta i s => by
    intro z hz
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .idelta s => by
    intro z hz
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .vsum s [] => by simp [ValExpr.inferType, ValTy.fv, ValSpace.fv]
  | .vsum s (e :: es) => by
    exact (ValExpr.fv_inferType_subset e).trans (by
      intro z hz
      simp only [ValExpr.fv, ValExpr.fvList, Finset.mem_union]
      tauto)
  | .ttv s e0 e1 => by
    intro z hz
    simp only [ValExpr.inferType] at hz
    split at hz
    · rename_i a sout heq
      have hm : z ∈ (ValExpr.inferType e0).fv := by
        rw [heq]
        exact Finset.mem_union_right _ hz
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (ValExpr.fv_inferType_subset e0 hm))
    · simp [ValTy.fv, ValSpace.fv] at hz
  | .mtm i j s0 s1 e0 e1 => by
    intro z hz
    have hi4 := @ValExpr.fv_inferType_subset e0 z
    have hs4 := @spaceOf_fv (ValExpr.inferType e0) z
    have hi5 := @ValExpr.fv_inferType_subset e1 z
    have hs5 := @spaceOf_fv (ValExpr.inferType e1) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .reshap e t t0 => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .vtrans e => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .pinv e => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .inv e => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .svds e => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .gsvdS e a b => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    have hi1 := @ValExpr.fv_inferType_subset a z
    have hs1 := @spaceOf_fv (ValExpr.inferType a) z
    have hi2 := @ValExpr.fv_inferType_subset b z
    have hs2 := @spaceOf_fv (ValExpr.inferType b) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .gsvdU e a b => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    have hi1 := @ValExpr.fv_inferType_subset a z
    have hs1 := @spaceOf_fv (ValExpr.inferType a) z
    have hi2 := @ValExpr.fv_inferType_subset b z
    have hs2 := @spaceOf_fv (ValExpr.inferType b) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .gsvdUI e a b => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    have hi1 := @ValExpr.fv_inferType_subset a z
    have hs1 := @spaceOf_fv (ValExpr.inferType a) z
    have hi2 := @ValExpr.fv_inferType_subset b z
    have hs2 := @spaceOf_fv (ValExpr.inferType b) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .gsvdV e a b => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    have hi1 := @ValExpr.fv_inferType_subset a z
    have hs1 := @spaceOf_fv (ValExpr.inferType a) z
    have hi2 := @ValExpr.fv_inferType_subset b z
    have hs2 := @spaceOf_fv (ValExpr.inferType b) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .gsvdVI e a b => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    have hi1 := @ValExpr.fv_inferType_subset a z
    have hs1 := @spaceOf_fv (ValExpr.inferType a) z
    have hi2 := @ValExpr.fv_inferType_subset b z
    have hs2 := @spaceOf_fv (ValExpr.inferType b) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto
  | .gpinv e a b => by
    intro z hz
    have hi0 := @ValExpr.fv_inferType_subset e z
    have hs0 := @spaceOf_fv (ValExpr.inferType e) z
    have hi1 := @ValExpr.fv_inferType_subset a z
    have hs1 := @spaceOf_fv (ValExpr.inferType a) z
    have hi2 := @ValExpr.fv_inferType_subset b z
    have hs2 := @spaceOf_fv (ValExpr.inferType b) z
    simp only [ValExpr.inferType] at hz
    try (split at hz)
    all_goals simp_all only [ValTy.fv, ValExpr.fv, ValSpace.fv, Finset.mem_union,
      Finset.mem_insert, Finset.notMem_empty]
    all_goals tauto

/-- Compiler argument conversion introduces no additional free names. -/
theorem ValExpr.fv_applyValue_subset (f a : ValExpr) :
    (ValExpr.applyValue f a).fv ⊆ f.fv ∪ a.fv := by
  have hd : f.inferType.domain.fv ⊆ f.inferType.fv := by
    cases f.inferType <;> simp only [ValTy.domain, ValTy.fv, ValSpace.fv]
    · exact Finset.Subset.refl _
    · exact Finset.subset_union_left
  simp only [ValExpr.applyValue, ValExpr.fv]
  exact Finset.union_subset Finset.subset_union_left
    (Finset.union_subset (Finset.union_subset Finset.subset_union_right
      ((hd.trans f.fv_inferType_subset).trans Finset.subset_union_left))
      (a.fv_inferType_subset.trans Finset.subset_union_right))

/-- A result conversion adds only the selected target type's free names. -/
theorem ValExpr.fv_applyAt_subset (f a : ValExpr) (t : ValTy) :
    (ValExpr.applyAt f a t).fv ⊆ (f.fv ∪ a.fv) ∪ t.fv := by
  simp only [ValExpr.applyAt, ValExpr.fv]
  exact Finset.union_subset
    (Finset.union_subset ((fv_applyValue_subset f a).trans Finset.subset_union_left)
      Finset.subset_union_right)
    (((ValExpr.applyValue f a).fv_inferType_subset.trans
      (fv_applyValue_subset f a)).trans Finset.subset_union_left)

end GLang
