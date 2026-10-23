import GLang.Operational.Supporting.Operational

/-!
# Multiple-representation public-progress regression

An evaluator context is keyed by `(source name, basis)`, not by source name
alone.  This regression records the intended end-to-end behavior: a second
exact basis key may be installed for an existing source binding, both exact
lookups remain available, and the resulting history is accepted by canonical
checked term progress.
-/

namespace GLang
namespace RawMultipleRepresentationRegression

/-- Public checked progress accepts two distinct exact evaluator keys for one
source name. -/
theorem checkedProgress_after_extendRep
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {x : VName} {b0 b1 requested : Basis} {v0 v1 : ValExpr}
    {e : Term}
    (history : V2.CtxTele Delta Gamma Psi)
    (oldLookup : EvalCtx.lookup Psi (x, b0) = some v0)
    (linked : V2.SourceEntryLinked Delta Gamma x b1)
    (keyFresh : (x, b1) ∉ Psi)
    (entry : V2.EvalEntryValid Psi x b1 v1)
    (anchor : V2.EvalFrameAnchored Psi b1 v1)
    (representationValid : Basis.BasisValid Gamma b1)
    (typed : HasType Delta Gamma e (Basis.tof requested))
    (requestedValid : Basis.BasisValid Gamma requested) :
    exists v tauV,
      Operational.Term Delta Gamma (Psi.extend x b1 v1)
          e requested v tauV /\
        ValExpr.inferType v = tauV /\
        ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV /\
        EvalCtx.lookup (Psi.extend x b1 v1) (x, b0) = some v0 /\
        EvalCtx.lookup (Psi.extend x b1 v1) (x, b1) = some v1 := by
  have history' :
      V2.CtxTele Delta Gamma (Psi.extend x b1 v1) :=
    .extend_rep history linked keyFresh ⟨entry, anchor⟩ representationValid
  obtain ⟨v, tauV, hstep, hinfer, hinferSpace⟩ :=
    Operational.Term.progress {
      history := history'
      typed := typed
      basisValid := requestedValid }
  have pairNe : (x, b0) ≠ (x, b1) := by
    intro heq
    exact keyFresh (heq ▸ Finmap.mem_of_lookup_eq_some oldLookup)
  refine ⟨v, tauV, hstep, hinfer, hinferSpace, ?_, ?_⟩
  · simpa only [EvalCtx.lookup, EvalCtx.extend,
      Finmap.lookup_insert_of_ne _ pairNe] using oldLookup
  · simp only [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert]

end RawMultipleRepresentationRegression
end GLang
