import GLang.Graded.BridgeBwd

namespace GLang.Graded

open GLang

/-- `tr` of a nonlinear insert (`y ∉ Δ`) is a `Function.update` at grade `ω`. -/
theorem tr_insert_nl_gen {Δ : LCtx} {Γ : NLCtx} {y : Name} {τ : Ty} (hyΔ : y ∉ Δ) :
    tr Δ (Finmap.insert y τ Γ)
      = Function.update (tr Δ Γ) y (some (GGrade.omega, τ)) := by
  funext x
  rcases eq_or_ne x y with rfl | hxy
  · rw [Function.update_self]
    simp only [tr, Finmap.lookup_eq_none.mpr hyΔ, Finmap.lookup_insert]
  · rw [Function.update_of_ne hxy]
    simp only [tr, Finmap.lookup_insert_of_ne _ hxy]

/-- Adding a fresh `ω` variable to a `tr`-image is a `GWk`. -/
theorem gwk_insert_omega {Δ : LCtx} {Γ : NLCtx} {y : Name} {τ : Ty}
    (hyΔ : y ∉ Δ) (hyΓ : y ∉ Γ) :
    GWk (tr Δ Γ) (Function.update (tr Δ Γ) y (some (GGrade.omega, τ))) := by
  intro z
  rcases eq_or_ne z y with rfl | hzy
  · rw [Function.update_self]
    have hnone : tr Δ Γ z = none := by
      simp only [tr, Finmap.lookup_eq_none.mpr hyΔ, Finmap.lookup_eq_none.mpr hyΓ]
    rw [hnone]; exact (by decide : GGrade.omega ≠ GGrade.one)
  · rw [Function.update_of_ne hzy]
    cases h : tr Δ Γ z with
    | none => simp only [WkPt]
    | some p => obtain ⟨g, t⟩ := p; exact ⟨rfl, GGrade.Wk.refl _⟩

/-- **Source nonlinear weakening (insert), via graded.** Inserting a fresh
    (`x ∉ Δ`, `x ∉ Γ`) non-linear binding `(x, τ')` preserves typing — proved
    forward-bridge → `gradeWeaken` (add ω var) → backward-bridge. NO promote arm,
    NO `promote_freshen_ε`/rename stub. Needs only `CtxDisj Δ Γ` (the bridge's
    context invariant; supplied by `CtxWF.disjoint` at every real call site). -/
noncomputable def hasType_weaken_insert {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty}
    {x : Name} {τ' : Ty} (hcd : CtxDisj Δ Γ) (hxΔ : x ∉ Δ) (hxΓ : x ∉ Γ)
    (h : HasType Δ Γ e τ) : HasType Δ (Finmap.insert x τ' Γ) e τ := by
  have hcd' : CtxDisj Δ (Finmap.insert x τ' Γ) := by
    intro y hy hmem
    rcases Finmap.mem_insert.mp hmem with rfl | hyΓ
    · exact hxΔ hy
    · exact hcd y hy hyΓ
  have hg' : GHasType (Function.update (tr Δ Γ) x (some (GGrade.omega, τ'))) e τ :=
    gradeWeaken (hasTypeBridge hcd h) (gwk_insert_omega hxΔ hxΓ)
  rw [← tr_insert_nl_gen hxΔ] at hg'
  exact hasTypeBridgeBwd hcd' hg'

end GLang.Graded
