import GLang.Proofs.Basis.Binding
import GLang.Proofs.Source.Soundness

/-!
# Free-variable closure for valid bases

This small regularity layer combines basis validity with the source typing
free-variable theorem.  It is kept out of `Soundness` so the source
soundness module does not acquire a dependency on basis syntax.
-/

namespace GLang

/-- Cofinite free-variable closure for a basis binder body. -/
private theorem Basis.fv_openVar_body_subset_for_progress
    {b : Basis} {L A : Finset Name}
    (h : ∀ y, y ∉ L → ∀ z, z ∈ Basis.fv (Basis.openVar y b) →
      z = y ∨ z ∈ A) :
    Basis.fv b ⊆ A := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Basis.fv b)
  simp only [Finset.mem_union, not_or] at hy
  intro z hz
  rcases h y hy.1 z (Basis.fv_subset_openRec hz) with rfl | hzA
  · exact absurd hz hy.2
  · exact hzA

/-- A valid basis mentions only names already declared by its nonlinear
source context. -/
theorem Basis.BasisValid.fv_subset_keys_for_progress
    {Gamma : NLCtx} {b : Basis}
    (h : Basis.BasisValid Gamma b) : Basis.fv b ⊆ Gamma.keys := by
  induction h with
  | empty | one => simp [Basis.fv]
  | dual _ _ ih => simpa only [Basis.fv] using ih
  | dsum _ _ _ _ ih0 ih1 | tprod _ _ _ _ ih0 ih1 =>
      simpa only [Basis.fv] using Finset.union_subset ih0 ih1
  | proj_ker hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_ker hb0 hb1 hs0 hs1 htype)).some
  | proj_coker hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_coker hb0 hb1 hs0 hs1 htype)).some
  | proj_img hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_img hb0 hb1 hs0 hs1 htype)).some
  | proj_coimg hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_coimg hb0 hb1 hs0 hs1 htype)).some
  | image _ _ _ ih => simpa only [Basis.fv] using ih
  | terms hb hs hsv hterms _ ih =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih) ?_
      · exact SValid.fv_closure hsv.some
      · intro z hz
        obtain ⟨e, he, hze⟩ := Term.mem_fvList.mp hz
        have hzctx := HasType.fv_closure (hterms e he).some hze
        simpa only [Finmap.keys_empty, Finset.empty_union] using hzctx
  | frame L hb0 hbody ih0 ihbody =>
      simp only [Basis.fv]
      refine Finset.union_subset ih0 ?_
      apply Basis.fv_openVar_body_subset_for_progress (L := L)
      intro y hy z hz
      have hzctx := ihbody y hy hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hzctx
      exact hzctx

end GLang
