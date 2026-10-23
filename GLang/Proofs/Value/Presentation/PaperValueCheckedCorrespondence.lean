import GLang.Proofs.Value.Presentation.PaperValueMixedCodecs
import GLang.Proofs.Adequacy.Foundations.CheckedValueSoundness
import GLang.Proofs.Value.Soundness.ValueSoundVals

namespace GLang.PaperValueDomains

/-- Checking only the right representative preserves its behavior on all
supported inputs, including every delayed callback error. -/
theorem runtime_normalize_checked_right (orc : FFSOracleSem) (τ : ValTy)
    (w w' : World) (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v')
    (b : (w'.denot orc τ).El)
    (hb : ValValSem.toEl (w'.denot orc τ) v' = .ok b) :
    PartialRel (RuntimeRelated orc τ w w') (.ok v)
      (ValValSem.fromElChecked (w'.denot orc τ) b) := by
  classical
  cases τ with
  | space s =>
    cases v <;> cases v' <;> try exact h.elim
    simp only [denotValTyS,ValValSem.toEl,Except.ok.injEq] at hb
    subst b
    simp only [denotValTyS,
      ValValSem.fromElChecked_space_of_length _ _ _ h.2.2,PartialRel]
    exact h
  | piTy d c =>
    cases v <;> cases v' <;> try exact h.elim
    rename_i T f U g
    obtain ⟨hT,hU,hfg⟩ := h
    subst T; subst U
    simp only [World.denot,denotValTyS,ValValSem.toEl,dite_true,Except.ok.injEq] at hb
    subst b
    refine ⟨rfl,rfl,?_⟩
    intro a b hab
    have hout := hfg a b hab
    cases hf : f a <;> cases hg : g b <;> simp only [hf,hg,PartialRel] at hout
    · simp only [hg,Except.bind,PartialRel]
    · rename_i r s
      obtain ⟨r',s',hr,hs,hrs⟩ := extract_related orc c _ _ r s hout
      have hn := runtime_normalize_checked_right orc c _ _ r s hout s' hs
      simp only [World.denot,World.push] at hs
      simpa only [World.denot,World.push,denotValTyS,ValValSem.fromElChecked,
        hf,hg,hs,Except.bind,PartialRel] using hn
termination_by sizeOf τ

/-- The current checker uses ordinary decoding followed by checked
reification; this is its actual one-sided relational law. -/
theorem recheck_related_right (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v') :
    PartialRel (RuntimeRelated orc τ w w') (.ok v)
      (CheckedValue.recheck (w'.denot orc τ) v') := by
  obtain ⟨a,b,ha,hb,hab⟩ := extract_related orc τ w w' v v' h
  simpa only [CheckedValue.recheck,hb,Except.bind] using
    runtime_normalize_checked_right orc τ w w' v v' h b hb

/-- Both current checkers preserve related successes and matching errors. -/
theorem recheck_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v') :
    PartialRel (RuntimeRelated orc τ w w')
      (CheckedValue.recheck (w.denot orc τ) v)
      (CheckedValue.recheck (w'.denot orc τ) v') := by
  obtain ⟨a,b,ha,hb,hab⟩ := extract_related orc τ w w' v v' h
  simpa only [CheckedValue.recheck,ha,hb,Except.bind] using
    reify_checked_related orc τ w w' a b hab

/-- Relational raw evaluation passes through the actual public inferred-type
checked evaluator. This includes matching preexisting evaluation failures. -/
theorem denot_checked_related {ε ε' : ValCtx} {e e' : ValExpr} {τ : ValTy}
    (he : ValHasType ε e τ) (he' : ValHasType ε' e' τ)
    (orc : FFSOracleSem) (w w' : World)
    (h : PartialRel (RuntimeRelated orc τ w w')
      (denotValB_semS orc w.env w.types w.values e)
      (denotValB_semS orc w'.env w'.types w'.values e')) :
    PartialRel (RuntimeRelated orc τ w w')
      (denotValB_semSChecked orc w.env w.types w.values e)
      (denotValB_semSChecked orc w'.env w'.types w'.values e') := by
  simp only [denotValB_semSChecked,denotValB_semSCheckedAt,
    ValExpr.inferTypeCtx_eq_of_typed he,ValExpr.inferTypeCtx_eq_of_typed he']
  exact h.bind _ _ (fun v v' hv => recheck_related orc τ w w' v v' hv)

/-- One-sided correspondence with the actual headline checked evaluator. -/
theorem denot_checked_related_right {ε' : ValCtx} {e e' : ValExpr} {τ : ValTy}
    (he' : ValHasType ε' e' τ) (orc : FFSOracleSem) (w w' : World)
    (h : PartialRel (RuntimeRelated orc τ w w')
      (denotValB_semS orc w.env w.types w.values e)
      (denotValB_semS orc w'.env w'.types w'.values e')) :
    PartialRel (RuntimeRelated orc τ w w')
      (denotValB_semS orc w.env w.types w.values e)
      (denotValB_semSChecked orc w'.env w'.types w'.values e') := by
  simp only [denotValB_semSChecked,denotValB_semSCheckedAt,ValExpr.inferTypeCtx_eq_of_typed he']
  have hb := h.bind Except.ok (CheckedValue.recheck (w'.denot orc τ))
    (fun v v' hv => recheck_related_right orc τ w w' v v' hv)
  cases hr : denotValB_semS orc w.env w.types w.values e <;>
    simpa only [hr,Except.bind] using hb

end GLang.PaperValueDomains
