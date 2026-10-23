import GLang.Value.Supporting.StrictTyping

namespace GLang
namespace ValCtx

/-- Finite support of the free variables occurring in types stored in a value
typing context.  Binder proofs choose their fresh name outside this set so all
pre-existing semantic bindings survive a named environment update. -/
def fvSupport (ε : ValCtx) : Finset VName :=
  ε.keys.biUnion fun x => (ε.lookup x).elim ∅ ValTy.fv

theorem not_mem_fv_of_not_mem_support {ε : ValCtx} {y x : VName} {τ : ValTy}
    (hy : y ∉ ε.fvSupport) (hx : ε.lookup x = some τ) :
    y ∉ ValTy.fv τ := by
  intro hyt
  apply hy
  apply Finset.mem_biUnion.mpr
  refine ⟨x, ?_, ?_⟩
  · exact Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hx)
  · simpa [hx] using hyt

end ValCtx
end GLang
