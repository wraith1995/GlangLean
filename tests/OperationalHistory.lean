import GLang.Operational.Supporting.OperationalHistory

namespace GLang.V2.History

example : WellFormed .empty := .empty
example : OperationallyConsistent .empty := .empty

private def frameInLinearHistory : History :=
  .lin .empty "x" (.frame .one .one) (.rlit 0)

example : WellFormed frameInLinearHistory := by
  apply WellFormed.lin WellFormed.empty
  · constructor <;> exact Finmap.notMem_empty
  · constructor
    · simp [ValExpr.fv]
    · exact .rlit

example : ¬ OperationallyConsistent frameInLinearHistory := by
  intro hc
  cases hc with
  | lin _ _ _ _ impossible => cases impossible

example (hc : CtxTele Δ Γ Ψ) :
    ∃ h : History, h.WellFormed ∧ ConsistentWith Δ Γ h ∧ h.evalContext = Ψ := by
  obtain ⟨h, hh, hp⟩ := ctxTele_iff_exists_consistent_history.mp hc
  exact ⟨h, hh.2.2.wellFormed, hh, hp⟩

#print axioms GLang.V2.History.OperationallyConsistent.wellFormed
#print axioms GLang.V2.History.OperationallyConsistent.ctxTele
#print axioms GLang.V2.CtxTele.exists_history
#print axioms GLang.V2.ctxTele_iff_exists_consistent_history

end GLang.V2.History
