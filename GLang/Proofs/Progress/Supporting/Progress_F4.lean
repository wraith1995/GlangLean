

import GLang.Proofs.Progress.Supporting.ProgressMasterDefs

namespace GLang.V2

/-- refine_24 `HasType.var_lin` (catalog F4). -/
theorem progress_arm_var_lin :
    ∀ {ε : NLCtx} {x : Name} {s : Space},
      pMotiveH (Finmap.singleton x s) ε (Term.var x) (Ty.space s) := by
  intro ε x s Ψ hP hcov
  refine ⟨?_, fun _ _ h => nomatch h⟩
  obtain ⟨b, hmem, htof⟩ := hcov.1 x s Finmap.lookup_singleton_eq
  obtain ⟨v, hv⟩ := hP.2.1 x b hmem
  rw [htof] at hv
  exact ⟨v, hv⟩

/-- refine_25 `HasType.var_nlin` (catalog F4). -/
theorem progress_arm_var_nlin :
    ∀ {ε : NLCtx} {x : Name} {τ : Ty},
      Finmap.lookup x ε = some τ → pMotiveH ∅ ε (Term.var x) τ := by
  intro ε x τ hlk Ψ hP hcov
  obtain ⟨b, hmem, htof⟩ := hcov.2 x τ hlk
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv⟩ := hP.2.1 x b hmem
    rw [htof] at hv
    exact ⟨v, hv⟩
  · intro τ₀ τ₁ heq
    exact hP.2.2 x b hmem τ₀ τ₁ (htof.trans heq)

/-- refine_28 `HasType.promote` (catalog F4). -/
theorem progress_arm_promote :
    ∀ {Δ : Finmap fun _x => Space} {ε' : Finmap fun _x => Ty} {e : Term}
      {τ : Ty} (lin : LCtx),
      Finmap.Disjoint lin Δ →
        Finmap.Disjoint lin.toNL ε' →
          PromoteFresh lin Δ ε' →
            ∀ (_a : HasType (lin ∪ Δ) ε' e τ),
              pMotiveH (lin ∪ Δ) ε' e τ → pMotiveH Δ (lin.toNL ∪ ε') e τ := by
  intro Δ ε' e τ lin _hdisjΔ hdisjε _hfresh _ht ih Ψ hP hcov
  exact ih Ψ hP (hcov.promote hdisjε)

end GLang.V2

