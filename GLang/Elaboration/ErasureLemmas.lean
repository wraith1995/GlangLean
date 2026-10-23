import GLang.Elaboration.Contexts
import GLang.Proofs.Basis.Binding

/-! Structural erasure laws needed by source elaboration. -/
namespace GLang

mutual
  theorem Space.erase_fv_subset (s : Space) : s.erase.fv ⊆ s.fv :=
    match s with
    | .empty | .real => Finset.Subset.refl _
    | .dual a => a.erase_fv_subset
    | .dsum a b | .tprod a b => Finset.union_subset_union a.erase_fv_subset b.erase_fv_subset
    | .ker _ _ e | .coker _ _ e | .img _ _ e | .coimg _ _ e =>
      Finset.Subset.trans e.erase_fv_subset Finset.subset_union_right
  theorem Ty.erase_fv_subset (t : Ty) : t.erase.fv ⊆ t.fv :=
    match t with
    | .space s => s.erase_fv_subset
    | .piTy a b => Finset.union_subset_union a.erase_fv_subset b.erase_fv_subset
  theorem Term.erase_fv_subset (e : Term) : e.erase.fv ⊆ e.fv :=
    match e with
    | .bvar _ | .var _ | .real _ => Finset.Subset.refl _
    | .zero s | .inner s | .embed s => s.erase_fv_subset
    | .smul a b | .add a b | .dsumE a b | .tprodE a b | .appN a b =>
      Finset.union_subset_union a.erase_fv_subset b.erase_fv_subset
    | .nllam t e => Finset.union_subset_union t.erase_fv_subset e.erase_fv_subset
    | .pinvT _ _ e | .pinvD _ e =>
      Finset.Subset.trans e.erase_fv_subset Finset.subset_union_right
    | .llam a _ e => Finset.union_subset_union
        (Finset.Subset.trans a.erase_fv_subset Finset.subset_union_left) e.erase_fv_subset
    | .appL _ _ a b | .appI _ a b => by
      exact Finset.union_subset_union
        (Finset.Subset.trans a.erase_fv_subset Finset.subset_union_right) b.erase_fv_subset
end

@[simp] theorem LCtx.erase_toNL (Δ : LCtx) : Δ.toNL.erase = Δ.erase.toNL := by
  apply Finmap.ext
  change (Δ.entries.map _).map _ = (Δ.entries.map _).map _
  simp only [Multiset.map_map]
  rfl

theorem PromoteFresh.toSurface {lin Δ ε} (h : PromoteFresh lin Δ ε) :
    Surface.PromoteFresh lin.erase Δ.erase ε.erase := by
  constructor
  · intro y hy x s hs hyfv
    obtain ⟨s', hs', rfl⟩ := (sourceMap_lookup_some Space.erase Δ x s).mp hs
    exact h.fresh_Δ y ((sourceMap_mem _ _ _).mp hy) x s' hs' (s'.erase_fv_subset hyfv)
  · intro y hy x s hs hyfv
    obtain ⟨s', hs', rfl⟩ := (sourceMap_lookup_some Space.erase lin x s).mp hs
    exact h.fresh_lin y ((sourceMap_mem _ _ _).mp hy) x s' hs' (s'.erase_fv_subset hyfv)
  · intro y hy x t ht hyfv
    obtain ⟨t', ht', rfl⟩ := (sourceMap_lookup_some Ty.erase ε x t).mp ht
    exact h.fresh_ε y ((sourceMap_mem _ _ _).mp hy) x t' ht' (t'.erase_fv_subset hyfv)

@[simp] theorem Basis.erase_sof (b : Basis) : b.sof.erase = b.erase.sof := by
  induction b with
  | image b ih =>
    simp only [Basis.sof, Basis.erase, Surface.Basis.sof, ← ih]
    cases b.sof <;> rfl
  | _ => simp_all [Basis.sof, Basis.erase, Surface.Basis.sof, Space.erase]

@[simp] theorem Basis.erase_tof (b : Basis) : b.tof.erase = b.erase.tof := by
  cases b with
  | frame a b =>
      exact congrArg₂ Surface.Ty.piTy (Basis.erase_tof a) (Basis.erase_tof b)
  | _ => exact congrArg Surface.Ty.space (Basis.erase_sof _)
termination_by b

end GLang
