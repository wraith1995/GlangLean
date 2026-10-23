import GLang.Proofs.Value.Presentation.PaperValuePrimitiveLocality
import GLang.Proofs.Value.Presentation.PaperValuePrimitiveSized
import GLang.Proofs.Value.Presentation.PaperValueDependentOracle
import GLang.Proofs.Value.Presentation.PaperValueTypedQueries
import GLang.Proofs.Value.Presentation.PaperValueCheckedExtensionality

/-! Induction tools for the original dependent value typing judgments. -/
namespace GLang.PaperValueDomains

/-- The current evaluator agrees between a fresh named binder and its
runtime stack presentation, including failure and higher-order results. -/
theorem original_eval_openVar (ρ : ValEnvSem) (x : VName) (τ : ValTy)
    (v : ValValSem) (body : ValExpr) (hτ : ValTy.lc τ)
    (hxτ : x ∉ ValTy.fv τ) (hx : x ∉ ValExpr.fv body) :
    denotValB_semS directOracle (ρ.update x v) [] [] (ValExpr.openVar x τ body) =
      denotValB_semS directOracle ρ [τ] [v] body := by
  have h : DirectOracleEval.ValueOpenPushEvalPrefix directOracle :=
    DirectOracleEval.valueOpenPushEvalPrefix_from_leaf directOracle
    directOracle_spec.valueOpenPushOracleCoherent
  simpa only [ValExpr.openVar, List.length_nil, List.nil_append,
    ValTy.closePrefix] using
    h (rho := ρ) (y := x) (sigmaV := τ) (w := v) (G := []) (D := [])
      (e := body) rfl hτ hxτ (by simp) hx

/-- Numerical induction step at an original typing conclusion.  It requires
agreement only on the finitely many spaces inspected by this rule, and
related results only for its immediate numerical operands.  FFS-dependent
spaces and errors are retained. -/
theorem original_numeric_step {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e)
    (w w' : World) (hΓ : w.types = w'.types)
    (hq : ∀ q ∈ primitiveQuerySpaces w.types e,
      SpaceOracleAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) q)
    (hi : ∀ a ∈ primitiveOperands e, ∃ t : ValSpace,
      PartialRel (RuntimeRelated directOracle (.space t) w w')
        (denotValB_semS directOracle w.env w.types w.values a)
        (denotValB_semS directOracle w'.env w'.types w'.values a)) :
    PartialRel (RuntimeRelated directOracle (.space s) w w')
      (denotValB_semS directOracle w.env w.types w.values e)
      (denotValB_semS directOracle w'.env w'.types w'.values e) := by
  apply arrayPrimitive_related_of_eval_eq directOracle w w' e s hp
  · rw [ValExpr.inferSpaceCtx_eq_of_typed ht]
  · rw [ValExpr.inferSpaceCtx_eq_of_typed ht]
  apply arrayPrimitive_eval_congr_local directOracle e w w' hp hΓ hq
  intro a ha
  obtain ⟨t, hrel⟩ := hi a ha
  exact base_results_eq hrel

/-- Original typing supplies the types of every operand and the validity of
all finite queried spaces. Consequently the numerical case consumes only
space and term induction hypotheses from the original judgments. -/
theorem original_numeric_step_of_typingIH {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (ht : ValHasType ε e (.space s)) (hp : ArrayPrimitive e) (hc : ValCtxValid ε)
    (w w' : World) (hΓ : w.types = w'.types)
    (spaceIH : ∀ q ∈ primitiveQuerySpaces w.types e, GLang.ValSValid ε q →
      SpaceOracleAgreement (directOracle w.env w.types w.values)
        (directOracle w'.env w'.types w'.values) q)
    (termIH : ∀ a ∈ primitiveOperands e, ∀ t, ValHasType ε a (.space t) →
      PartialRel (RuntimeRelated directOracle (.space t) w w')
        (denotValB_semS directOracle w.env w.types w.values a)
        (denotValB_semS directOracle w'.env w'.types w'.values a)) :
    PartialRel (RuntimeRelated directOracle (.space s) w w')
      (denotValB_semS directOracle w.env w.types w.values e)
      (denotValB_semS directOracle w'.env w'.types w'.values e) := by
  apply original_numeric_step ht hp w w' hΓ
  · intro q hq
    obtain ⟨hqtyped⟩ := original_primitive_query_valid ht hp hc w.types q hq
    exact spaceIH q hq hqtyped
  · intro a ha
    obtain ⟨t, ⟨hatyped⟩⟩ := original_primitive_operand_typed ht hp a ha
    exact ⟨t, termIH a ha t hatyped⟩

/-- Application induction step for the original typing judgment. The remaining
premise is precisely dependent semantic substitution: the decoded argument
selects a codomain fibre that represents the syntactically instantiated type.
Operand failures are proved here, not omitted from the induction obligation. -/
theorem original_application_step {ε : ValCtx} {ef ea : ValExpr} {d c out : ValTy}
    (hf : ValHasType ε ef (.piTy d c)) (w w' : World)
    (ihf : PartialRel (RuntimeRelated directOracle (.piTy d c) w w')
      (denotValB_semS directOracle w.env w.types w.values ef)
      (denotValB_semS directOracle w'.env w'.types w'.values ef))
    (iha : PartialRel (RuntimeRelated directOracle d w w')
      (denotValB_semS directOracle w.env w.types w.values ea)
      (denotValB_semS directOracle w'.env w'.types w'.values ea))
    (hsubst : ∀ v v' a b,
      denotValB_semS directOracle w.env w.types w.values ea = .ok v →
      denotValB_semS directOracle w'.env w'.types w'.values ea = .ok v' →
      ValValSem.toElDomainChecked (w.denot directOracle d) v = .ok a →
      ValValSem.toElDomainChecked (w'.denot directOracle d) v' = .ok b →
      Related directOracle d w w' a b →
      ∀ r r', RuntimeRelated directOracle c
        (w.push directOracle d a) (w'.push directOracle d b) r r' →
        RuntimeRelated directOracle out w w' r r') :
    PartialRel (RuntimeRelated directOracle out w w')
      (denotValB_semS directOracle w.env w.types w.values (.appV ef ea))
      (denotValB_semS directOracle w'.env w'.types w'.values (.appV ef ea)) := by
  cases hfl : denotValB_semS directOracle w.env w.types w.values ef with
  | error err =>
      cases hfr : denotValB_semS directOracle w'.env w'.types w'.values ef with
      | error err' =>
          have he : err = err' := by simpa only [hfl,hfr,PartialRel] using ihf
          subst err'
          simp only [denotValB_semS.eq_28,hfl,hfr,PartialRel]
      | ok f' => simp only [hfl,hfr,PartialRel] at ihf
  | ok f =>
      cases hfr : denotValB_semS directOracle w'.env w'.types w'.values ef with
      | error err => simp only [hfl,hfr,PartialRel] at ihf
      | ok g =>
          have hfg : RuntimeRelated directOracle (.piTy d c) w w' f g :=
            by simpa only [hfl,hfr,PartialRel] using ihf
          cases f with
          | array a => cases g <;> exact hfg.elim
          | fn T f =>
            cases g with
            | array a => exact hfg.elim
            | fn U g =>
              cases hal : denotValB_semS directOracle w.env w.types w.values ea with
              | error err =>
                  cases har : denotValB_semS directOracle w'.env w'.types w'.values ea with
                  | error err' =>
                      have he : err = err' := by simpa only [hal,har,PartialRel] using iha
                      subst err'
                      simp only [denotValB_semS.eq_28,hfl,hfr,hal,har,PartialRel]
                  | ok a' => simp only [hal,har,PartialRel] at iha
              | ok v =>
                  cases har : denotValB_semS directOracle w'.env w'.types w'.values ea with
                  | error err => simp only [hal,har,PartialRel] at iha
                  | ok v' =>
                      have hv : RuntimeRelated directOracle d w w' v v' :=
                        by simpa only [hal,har,PartialRel] using iha
                      obtain ⟨a,b,ha,hb,hab,hres⟩ := eval_appV_related directOracle d c out out
                        w w' ef ea ef ea (.fn T f) (.fn U g) v v'
                        (by rw [ValExpr.inferTypeCtx_eq_of_typed hf]; rfl)
                        (by rw [ValExpr.inferTypeCtx_eq_of_typed hf]; rfl)
                        hfl hfr hal har hfg hv
                      generalize hl : denotValB_semS directOracle w.env w.types w.values
                        (.appV ef ea) = l at hres ⊢
                      generalize hr : denotValB_semS directOracle w'.env w'.types w'.values
                        (.appV ef ea) = r at hres ⊢
                      cases l <;> cases r <;> simp only [PartialRel] at hres ⊢
                      exact hsubst v v' a b hal har ha hb hab _ _ hres

end GLang.PaperValueDomains
