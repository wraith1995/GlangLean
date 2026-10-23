/-
GLang.PreservationV2_FFS — the FFS (kernel/cross-part) preservation arm helper.

Generalizes the proved `eKer` arm of `ValuePreservationV2` over the FFS prop tag
`p : ValFFSProp`. The body of `eKer` after `cases hsval` does NOT inspect the FFS
prop specifically — the witness is reshaped to `svb`, so its `inferType` IS `svb`
(no witness typing needed for `ValSValidC`). This file factors that core out.
-/
import GLang.Proofs.Preservation.PreservationV2Helpers

namespace GLang

/-- **The FFS arm, generalized over the prop tag `p`.** The realized sub-space
    `svb` of `sof b = (dual s₀) ⊗ s₁` is a `.tprod`; the FFS value built by
    reshaping the witness `leev` to `svb` is valid (its `inferType` is `svb`),
    with free variables contained in `ρ'`. -/
theorem term_ffs_v2 {Ψ : EvalCtx} {ρ' : Finset VName} {s₀ s₁ : Space} {b : Basis}
    {leev : ValExpr} {svb : ValSpace} (p : ValFFSProp)
    (hb : Basis.sof b = .tprod (.dual s₀) s₁)
    (hsvb : ValSpace.EvalS Ψ (Basis.sof b) svb)
    (hsvbval : Nonempty (ValSValidC svb)) (hfvsvb : ValSpace.fv svb ⊆ ρ')
    (hfvleev : ValExpr.fv leev ⊆ ρ') :
    Nonempty (ValSValidC (.ffs p svb (.reshap leev (.space svb) (.space svb))))
    ∧ ValSpace.fv (.ffs p svb (.reshap leev (.space svb) (.space svb))) ⊆ ρ' := by
  obtain ⟨sva, svb1, rfl⟩ := evalS_tprod_inv (hb ▸ hsvb)
  obtain ⟨svbv⟩ := hsvbval
  obtain ⟨hsva, hsvb1⟩ := valSValidC_tprod_inv svbv
  exact ⟨⟨ValSValidC.ffs hsva hsvb1 rfl⟩,
    Finset.union_subset hfvsvb
      (Finset.union_subset (Finset.union_subset hfvleev hfvsvb) hfvsvb)⟩

end GLang
