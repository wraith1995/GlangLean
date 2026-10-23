import GLang.Proofs.Value.Presentation.PaperValueNumericSubstitution
import GLang.Proofs.Value.Presentation.PaperValueOracleExtensionality

/-! The FFS branch of semantic named substitution uses the actual current
rank equation. Only parent-space and witness induction hypotheses are needed. -/
namespace GLang.PaperValueDomains

theorem SubstSpaceAgreement.shapes {q q' : FFSOracle} {x : VName} {u : ValExpr}
    {s : ValSpace} (h : SubstSpaceAgreement q q' x u s) :
    ValSpace.shpOf q s = ValSpace.shpOf q' (ValSpace.subst x u s) := by
  cases s with
  | empty | real => simp [ValSpace.subst]
  | dsum s t =>
      simp only [ValSpace.subst, ValSpace.shpOf]
      rw [SubstSpaceAgreement.dof h.1, SubstSpaceAgreement.dof h.2]
  | tprod s t =>
      simp only [ValSpace.subst, ValSpace.shpOf]
      rw [SubstSpaceAgreement.dof h.1, SubstSpaceAgreement.dof h.2]
  | ffs p s e =>
      simpa only [ValSpace.subst, ValSpace.shpOf] using congrArg (fun n => [n]) h

/-- Different witness and parent syntax may yield the same current query.
This includes unsuccessful witnesses and preserves their rank fallback. -/
theorem directOracle_eq_of_substitution_step (w w' : World)
    (x : VName) (u : ValExpr) (p : ValFFSProp) (s : ValSpace) (e : ValExpr)
    (hf : ValueQueryDependencies.Finite (.space w.types (.ffs p s e)))
    (hf' : ValueQueryDependencies.Finite (.space w'.types
      (.ffs p (ValSpace.subst x u s) (ValExpr.subst x u e))))
    (hs : SubstSpaceAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) x u s)
    (he : denotValB_semS directOracle w.env w.types w.values e =
      denotValB_semS directOracle w'.env w'.types w'.values (ValExpr.subst x u e)) :
    SubstSpaceAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) x u (.ffs p s e) := by
  change directOracle w.env w.types w.values p s e =
    directOracle w'.env w'.types w'.values p (ValSpace.subst x u s) (ValExpr.subst x u e)
  rw [directOracle_rank_equation _ _ _ _ hf, directOracle_rank_equation _ _ _ _ hf', hs.shapes]
  congr 1
  unfold ffsOperandRank
  rw [hs.shapes, he]

end GLang.PaperValueDomains
