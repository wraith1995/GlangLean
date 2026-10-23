import GLang.Proofs.Adequacy.Foundations.Consistent

namespace GLang
namespace RawLocalCtxWFInsertionScratch

private theorem validBasis_tof_tvalid {Gamma : NLCtx} {b : Basis}
    (hb : Basis.BasisValid Gamma b) :
    exists k, Nonempty (TValid Gamma (Basis.tof b) k) := by
  cases b
  case frame b0 b1 =>
    obtain ⟨_, _, k0, k1, ht⟩ := hb.frame_inv
    exact ⟨.arrow k0 k1, ht⟩
  all_goals
    obtain ⟨hs⟩ := hb.sof_valid
    exact ⟨.base, ⟨.space hs⟩⟩

/-- A fresh nonlinear binder whose chosen basis is valid produces the exact
`CtxWF'` used by an opened nonlinear body.  Freshness for both source
namespaces prevents overwriting and preserves their disjointness. -/
theorem ctxWF_insert_nl
    {Delta : LCtx} {Gamma : NLCtx} {y : Name} {b : Basis}
    (hwf : V2.CtxWF' Delta Gamma)
    (hyDelta : y ∉ Delta) (hyGamma : y ∉ Gamma)
    (hb : Basis.BasisValid Gamma b) :
    V2.CtxWF' Delta (Finmap.insert y (Basis.tof b) Gamma) where
  disjoint := by
    intro x hxDelta hxGamma'
    rcases Finmap.mem_insert.mp hxGamma' with rfl | hxGamma
    · exact hyDelta hxDelta
    · exact hwf.disjoint x hxDelta hxGamma
  lin_fv := by
    intro x s hx z hz
    exact Finmap.mem_keys.mpr <| Finmap.mem_insert.mpr <| Or.inr <|
      Finmap.mem_keys.mp (hwf.lin_fv x s hx hz)
  nl_fv := by
    intro x tau hx z hz
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hx
      obtain rfl := Option.some.inj hx
      exact Finmap.mem_keys.mpr <| Finmap.mem_insert.mpr <| Or.inr <|
        Finmap.mem_keys.mp
          (((Basis.fv_tof_subset b).trans hb.fv_subset_keys) hz)
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      exact Finmap.mem_keys.mpr <| Finmap.mem_insert.mpr <| Or.inr <|
        Finmap.mem_keys.mp (hwf.nl_fv x tau hx hz)
  lin_valid := by
    intro x s hx
    obtain ⟨hs⟩ := hwf.lin_valid x s hx
    exact ⟨hs.weakenInsertNL y (Basis.tof b) hyGamma⟩
  nl_valid := by
    intro x tau hx
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hx
      obtain rfl := Option.some.inj hx
      obtain ⟨k, ⟨ht⟩⟩ := validBasis_tof_tvalid hb
      exact ⟨k, ⟨ht.weakenInsertNL y (Basis.tof b) hyGamma⟩⟩
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      obtain ⟨k, ⟨ht⟩⟩ := hwf.nl_valid x tau hx
      exact ⟨k, ⟨ht.weakenInsertNL y (Basis.tof b) hyGamma⟩⟩

/-- A fresh linear binder whose chosen basis is valid produces the exact
`CtxWF'` used by an opened linear body. -/
theorem ctxWF_insert_lin
    {Delta : LCtx} {Gamma : NLCtx} {y : Name} {b : Basis}
    (hwf : V2.CtxWF' Delta Gamma)
    (_hyDelta : y ∉ Delta) (hyGamma : y ∉ Gamma)
    (hb : Basis.BasisValid Gamma b) :
    V2.CtxWF' (Finmap.insert y (Basis.sof b) Delta) Gamma where
  disjoint := by
    intro x hxDelta' hxGamma
    rcases Finmap.mem_insert.mp hxDelta' with rfl | hxDelta
    · exact hyGamma hxGamma
    · exact hwf.disjoint x hxDelta hxGamma
  lin_fv := by
    intro x s hx z hz
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hx
      obtain rfl := Option.some.inj hx
      exact Finmap.mem_keys.mp
        (((Basis.fv_sof_subset b).trans hb.fv_subset_keys) hz)
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      exact hwf.lin_fv x s hx hz
  nl_fv := hwf.nl_fv
  lin_valid := by
    intro x s hx
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hx
      obtain rfl := Option.some.inj hx
      exact hb.sof_valid
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      exact hwf.lin_valid x s hx
  nl_valid := hwf.nl_valid

theorem typingImplyEval_insert_nl
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {y : Name} {b : Basis} {v : ValExpr}
    (hlink : V2.TypingImplyEval Delta Gamma Psi)
    (hyDelta : y ∉ Delta) (hyGamma : y ∉ Gamma)
    (hyPsi : forall b', (y, b') ∉ Psi)
    (hb : Basis.BasisValid Gamma b) :
    V2.TypingImplyEval Delta (Finmap.insert y (Basis.tof b) Gamma)
      (Psi.extend y b v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [Finmap.mem_insert, EvalCtx.exists_mem_extend]
    constructor
    · rintro (hxDelta | rfl | hxGamma)
      · exact Or.inr ((hlink.1 x).mp (Or.inl hxDelta))
      · exact Or.inl rfl
      · exact Or.inr ((hlink.1 x).mp (Or.inr hxGamma))
    · rintro (rfl | hxPsi)
      · exact Or.inr (Or.inl rfl)
      · rcases (hlink.1 x).mpr hxPsi with hxDelta | hxGamma
        · exact Or.inl hxDelta
        · exact Or.inr (Or.inr hxGamma)
  · intro x s b' hxDelta hxPsi'
    rcases EvalCtx.mem_extend.mp hxPsi' with ⟨rfl, rfl⟩ | hxPsi
    · exact absurd (Finmap.mem_of_lookup_eq_some hxDelta) hyDelta
    · exact hlink.2.1 x s b' hxDelta hxPsi
  · intro x tau b' hxGamma' hxPsi'
    rcases EvalCtx.mem_extend.mp hxPsi' with ⟨rfl, rfl⟩ | hxPsi
    · rw [Finmap.lookup_insert] at hxGamma'
      exact Option.some.inj hxGamma'
    · have hxy : x ≠ y := by
        intro h
        subst x
        exact hyPsi b' hxPsi
      rw [Finmap.lookup_insert_of_ne _ hxy] at hxGamma'
      exact hlink.2.2.1 x tau b' hxGamma' hxPsi
  · intro x b' hxPsi'
    rcases EvalCtx.mem_extend.mp hxPsi' with ⟨rfl, rfl⟩ | hxPsi
    · exact hb.weakenInsertNL hyGamma
        (hb.not_mem_fv_of_not_mem hyGamma)
    · have hb' := hlink.2.2.2 x b' hxPsi
      exact hb'.weakenInsertNL hyGamma
        (hb'.not_mem_fv_of_not_mem hyGamma)

theorem typingImplyEval_insert_lin
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {y : Name} {b : Basis} {v : ValExpr}
    (hlink : V2.TypingImplyEval Delta Gamma Psi)
    (hyDelta : y ∉ Delta) (hyGamma : y ∉ Gamma)
    (hyPsi : forall b', (y, b') ∉ Psi)
    (hb : Basis.BasisValid Gamma b)
    (htof : Basis.tof b = .space (Basis.sof b)) :
    V2.TypingImplyEval (Finmap.insert y (Basis.sof b) Delta) Gamma
      (Psi.extend y b v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [Finmap.mem_insert, EvalCtx.exists_mem_extend]
    constructor
    · rintro ((rfl | hxDelta) | hxGamma)
      · exact Or.inl rfl
      · exact Or.inr ((hlink.1 x).mp (Or.inl hxDelta))
      · exact Or.inr ((hlink.1 x).mp (Or.inr hxGamma))
    · rintro (rfl | hxPsi)
      · exact Or.inl (Or.inl rfl)
      · rcases (hlink.1 x).mpr hxPsi with hxDelta | hxGamma
        · exact Or.inl (Or.inr hxDelta)
        · exact Or.inr hxGamma
  · intro x s b' hxDelta' hxPsi'
    rcases EvalCtx.mem_extend.mp hxPsi' with ⟨rfl, rfl⟩ | hxPsi
    · rw [Finmap.lookup_insert] at hxDelta'
      obtain rfl := Option.some.inj hxDelta'
      exact htof
    · have hxy : x ≠ y := by
        intro h
        subst x
        exact hyPsi b' hxPsi
      rw [Finmap.lookup_insert_of_ne _ hxy] at hxDelta'
      exact hlink.2.1 x s b' hxDelta' hxPsi
  · intro x tau b' hxGamma hxPsi'
    rcases EvalCtx.mem_extend.mp hxPsi' with ⟨rfl, rfl⟩ | hxPsi
    · exact absurd (Finmap.mem_of_lookup_eq_some hxGamma) hyGamma
    · exact hlink.2.2.1 x tau b' hxGamma hxPsi
  · intro x b' hxPsi'
    rcases EvalCtx.mem_extend.mp hxPsi' with ⟨rfl, rfl⟩ | hxPsi
    · exact hb
    · exact hlink.2.2.2 x b' hxPsi

end RawLocalCtxWFInsertionScratch
end GLang
