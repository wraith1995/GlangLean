import GLang.Annotated.Judgments

/-!
# Free-variable support of a non-linear context

`NLCtx.fv ε` — the free names of all bound types of a non-linear context. Small
standalone home (relocated from `GLang/Proofs/Source/Substitution.lean` when that
source-substitution subsystem was RETIRED — the graded reformulation supplanted
it; see `GLang/Graded/SourceSubst.lean`). Consumed by `gtvInst`
(`GLang/Graded/Regularity.lean`) to pick a fresh instantiation witness past all
context-type free names.
-/

namespace GLang

open GLang

/-- Free names of all bound types of a non-linear context (the `Multiset.sup`
    of each bound type's `Ty.fv`). -/
def NLCtx.fv (ε : NLCtx) : Finset Name :=
  (ε.entries.map (fun p : Σ _ : Name, Ty => Ty.fv p.2)).sup

theorem NLCtx.mem_fv_of_lookup {ε : NLCtx} {z : Name} {τ : Ty} {w : Name}
    (hl : ε.lookup z = some τ) (hw : w ∈ Ty.fv τ) : w ∈ NLCtx.fv ε := by
  have hmem : (⟨z, τ⟩ : Σ _ : Name, Ty) ∈ ε.entries := by
    rw [← Finmap.lookup_eq_some_iff]; exact hl
  have hin : Ty.fv τ ∈ ε.entries.map (fun p : Σ _ : Name, Ty => Ty.fv p.2) := by
    rw [Multiset.mem_map]; exact ⟨⟨z, τ⟩, hmem, rfl⟩
  exact Finset.mem_of_subset (Multiset.le_sup hin) hw

end GLang
