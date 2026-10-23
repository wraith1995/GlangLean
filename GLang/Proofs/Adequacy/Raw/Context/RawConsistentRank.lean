import GLang.Proofs.Adequacy.Raw.Context.RawConsistent
import GLang.Proofs.Progress.Supporting.ProgressTele

namespace GLang
namespace RawConsistentRank

private theorem mem_extend
    {Psi : EvalCtx} {x x' : VName} {b b' : Basis} {v : ValExpr} :
    (x', b') ∈ Psi.extend x b v ↔
      (x' = x ∧ b' = b) ∨ (x', b') ∈ Psi := by
  simp only [EvalCtx.extend, Finmap.mem_insert, Prod.mk.injEq]

/-- A finite evaluator is ranked in exact-pair creation order. -/
def EvalCtxCreationRank (Psi : EvalCtx) : Prop :=
  ∃ rank : (VName × Basis) -> Nat,
    forall x b, (x, b) ∈ Psi ->
      forall y, y ∈ Basis.fv b ->
        ∃ bY, (y, bY) ∈ Psi ∧ rank (y, bY) < rank (x, b)

theorem EvalCtxCreationRank.extend
    {Psi : EvalCtx} (h : EvalCtxCreationRank Psi)
    {x : VName} {b : Basis} {v : ValExpr}
    (hkey : (x, b) ∉ Psi)
    (hfvb : Basis.fv b ⊆ Psi.keyNames) :
    EvalCtxCreationRank (Psi.extend x b v) := by
  classical
  rcases h with ⟨rank, hpred⟩
  let next : Nat := Psi.keys.sup rank + 1
  let rank' : (VName × Basis) -> Nat :=
    fun key => if key = (x, b) then next else rank key
  refine ⟨rank', ?_⟩
  intro owner basis hmem y hy
  rcases mem_extend.mp hmem with ⟨rfl, rfl⟩ | hold
  · have hyNames : y ∈ Psi.keyNames := hfvb hy
    obtain ⟨bY, hyKey⟩ :=
      EvalCtx.mem_keyNames_iff_exists_basis.mp hyNames
    have hyNe : (y, bY) ≠ (owner, basis) :=
      fun heq => hkey (heq ▸ hyKey)
    have hle : rank (y, bY) ≤ Psi.keys.sup rank :=
      Finset.le_sup (Finmap.mem_keys.mpr hyKey)
    refine ⟨bY, ?_, ?_⟩
    · exact Finmap.mem_insert.mpr (Or.inr hyKey)
    · simp only [rank', if_neg hyNe, if_pos, next]
      omega
  · obtain ⟨bY, hyKey, hyrank⟩ := hpred owner basis hold y hy
    have hownerNe : (owner, basis) ≠ (x, b) :=
      fun heq => hkey (heq ▸ hold)
    have hyNe : (y, bY) ≠ (x, b) :=
      fun heq => hkey (heq ▸ hyKey)
    refine ⟨bY, Finmap.mem_insert.mpr (Or.inr hyKey), ?_⟩
    simpa only [rank', if_neg hownerNe, if_neg hyNe] using hyrank

/-- The empty evaluator has the trivial rank. -/
theorem empty : EvalCtxCreationRank (∅ : EvalCtx) := by
  refine ⟨fun _ => 0, ?_⟩
  intro x b hmem
  exact absurd hmem Finmap.notMem_empty

/-- Raw consistency constructively supplies a strict creation rank. -/
theorem ofRawConsistent
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    EvalCtxCreationRank Psi := by
  induction h with
  | empty => exact empty
  | extend_lin hprefix hx htof hb hTy hinfer hinferSpace
      hfvv hlc hnr hxs hden hresult hdims ih =>
      exact ih.extend (hprefix.freshEvalName hx _)
        (hprefix.basisFvPrefix hb)
  | extend_nl hprefix hx hb hTy hinfer hinferSpace
      hfvv hlc hnr hxs hden hresult hdims _hanchor ih =>
      exact ih.extend (hprefix.freshEvalName hx _)
        (hprefix.basisFvPrefix hb)
  | extend_rep hprefix hkey hsource hsigma hb hTy hinfer hinferSpace
      hfvv hlc hxs hden hresult hdims hanchor ih =>
      exact ih.extend hkey (hprefix.basisFvPrefix hb)

/-- The source/evaluator construction history supplies the same exact-pair
creation rank without any semantic consistency hypothesis. -/
theorem EvalCtxCreationRank.ofCtxTele
    (h : V2.CtxTele Delta Gamma Psi) : EvalCtxCreationRank Psi := by
  induction h with
  | empty => exact RawConsistentRank.empty
  | extend_nlin hprefix hsource hcreation hb ih =>
      exact ih.extend (hprefix.freshEvalName hsource _)
        (hprefix.basisFvPrefix hb)
  | extend_lin hprefix hsource hcreation hb htof ih =>
      exact ih.extend (hprefix.freshEvalName hsource _)
        (hprefix.basisFvPrefix hb)
  | extend_rep hprefix hsource hkey hcreation hb ih =>
      exact ih.extend hkey (hprefix.basisFvPrefix hb)

/-- Convert an exact-pair creation rank into lookup-shaped predecessor data.
The value at the predecessor key is recovered from finite-map membership; the
rank package chooses the predecessor basis. -/
theorem EvalCtxCreationRank.exists_ranked_lookup_predecessors
    {Psi : EvalCtx} (h : EvalCtxCreationRank Psi) :
    exists rank : (VName × Basis) -> Nat,
      forall {x : VName} {b : Basis} {v : ValExpr},
        EvalCtx.lookup Psi (x, b) = some v ->
        forall y, y ∈ Basis.fv b ->
          exists bY : Basis, exists vY : ValExpr,
            EvalCtx.lookup Psi (y, bY) = some vY /\
              rank (y, bY) < rank (x, b) := by
  obtain ⟨rank, hpred⟩ := h
  refine ⟨rank, ?_⟩
  intro x b v hlookup y hy
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  obtain ⟨bY, hyKey, hyrank⟩ := hpred x b hmem y hy
  obtain ⟨vY, hyLookup⟩ := Finmap.mem_iff.mp hyKey
  exact ⟨bY, vY, hyLookup, hyrank⟩

end RawConsistentRank

namespace V2
namespace CtxTele

/-- Checked-progress histories expose the same selected lower-ranked lookup
as raw consistency, but require no denotational environment or oracle. -/
theorem exists_ranked_lookup_predecessors
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (h : CtxTele Delta Gamma Psi) :
    exists rank : (VName × Basis) -> Nat,
      forall {x : VName} {b : Basis} {v : ValExpr},
        EvalCtx.lookup Psi (x, b) = some v ->
        forall y, y ∈ Basis.fv b ->
          exists bY : Basis, exists vY : ValExpr,
            EvalCtx.lookup Psi (y, bY) = some vY /\
              rank (y, bY) < rank (x, b) := by
  exact
    RawConsistentRank.EvalCtxCreationRank.exists_ranked_lookup_predecessors
      (RawConsistentRank.EvalCtxCreationRank.ofCtxTele h)

end CtxTele
end V2
end GLang
