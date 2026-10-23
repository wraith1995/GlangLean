import GLang.Proofs.Value.Presentation.PaperValueExtensionality

/-! Bridges from the two-world logical relation to the live strict access and
application boundaries. These use relational callback contracts; they do not
assert that arbitrary unary-valid callbacks are extensionally equal. -/
namespace GLang.PaperValueDomains

/-- Immediate-domain decoding preserves related values and succeeds on both
sides. At a base type, the relation supplies exactly the length check. -/
theorem extract_domain_checked_related (orc : FFSOracleSem) (τ : ValTy)
    (w w' : World) (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v') :
    ∃ a b, ValValSem.toElDomainChecked (w.denot orc τ) v = .ok a ∧
      ValValSem.toElDomainChecked (w'.denot orc τ) v' = .ok b ∧
      Related orc τ w w' a b := by
  cases τ with
  | space s =>
    cases v <;> cases v' <;> try exact h.elim
    refine ⟨_, _, ?_, ?_, h⟩
    · exact ValValSem.toElChecked_space_of_length _ _ _ h.2.1
    · exact ValValSem.toElChecked_space_of_length _ _ _ h.2.2
  | piTy τ₀ τ₁ => exact extract_related orc (.piTy τ₀ τ₁) w w' v v' h

/-- Full recursive checked extraction also preserves the relation. Its checks
remain suspended in higher-order result fibres. -/
theorem extract_checked_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v') :
    ∃ a b, ValValSem.toElChecked (w.denot orc τ) v = .ok a ∧
      ValValSem.toElChecked (w'.denot orc τ) v' = .ok b ∧ Related orc τ w w' a b := by
  classical
  cases τ with
  | space s =>
    cases v <;> cases v' <;> try exact h.elim
    exact ⟨_, _, ValValSem.toElChecked_space_of_length _ _ _ h.2.1,
      ValValSem.toElChecked_space_of_length _ _ _ h.2.2, h⟩
  | piTy τ₀ τ₁ =>
    cases v <;> cases v' <;> try exact h.elim
    rename_i T f U g
    obtain ⟨hT, hU, hfg⟩ := h
    subst T; subst U
    simp only [World.denot, denotValTyS, ValValSem.toElChecked_pi_fn]
    refine ⟨_, _, rfl, rfl, ?_⟩
    intro x y hxy
    apply PartialRel.bind _ _ ?_ (hfg x y hxy)
    intro u v huv
    obtain ⟨a, b, ha, hb, hab⟩ := extract_checked_related orc τ₁ _ _ u v huv
    simp only [World.push, World.denot] at ha hb
    rw [ha, hb]
    exact hab
termination_by sizeOf τ

/-- Checked reification respects the relation, including matching delayed
errors. It never needs to repair an admissible base array by resizing. -/
theorem reify_checked_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (a : (w.denot orc τ).El) (b : (w'.denot orc τ).El)
    (h : Related orc τ w w' a b) :
    PartialRel (RuntimeRelated orc τ w w')
      (ValValSem.fromElChecked (w.denot orc τ) a)
      (ValValSem.fromElChecked (w'.denot orc τ) b) := by
  cases τ with
  | space s =>
    simp only [World.denot, denotValTyS,
      ValValSem.fromElChecked_space_of_length _ _ _ h.2.1,
      ValValSem.fromElChecked_space_of_length _ _ _ h.2.2, PartialRel]
    exact h
  | piTy τ₀ τ₁ =>
    refine ⟨rfl, rfl, ?_⟩
    intro x y hxy
    exact PartialRel.bind _ _
      (fun u v huv => reify_checked_related orc τ₁ _ _ u v huv) (h x y hxy)
termination_by sizeOf τ

/-- Scalar observation is identical on related runtime values, for every
index: valid entries agree, out-of-bounds errors agree, and functions reject
scalar observation on both sides. -/
theorem read_checked_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v') (i : Nat) :
    v.readChecked i = v'.readChecked i := by
  cases τ with
  | space s =>
    cases v <;> cases v' <;> try exact h.elim
    rw [h.1]
  | piTy τ₀ τ₁ =>
    cases v <;> cases v' <;> try exact h.elim
    rfl

/-- Checked observation preserves prior errors as well as related successes. -/
theorem read_result_checked_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (r r' : Except DimError ValValSem)
    (h : PartialRel (RuntimeRelated orc τ w w') r r') (i : Nat) :
    ValValSem.readResultChecked r i = ValValSem.readResultChecked r' i := by
  cases r <;> cases r' <;> simp only [PartialRel] at h
  · cases h; rfl
  · exact read_checked_related orc τ w w' _ _ h i

/-- Checked extraction of partial results preserves both errors and related
successes, including errors suspended in dependent callbacks. -/
theorem extract_checked_results_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (r r' : Except DimError ValValSem)
    (h : PartialRel (RuntimeRelated orc τ w w') r r') :
    PartialRel (Related orc τ w w')
      (r.bind (ValValSem.toElChecked (w.denot orc τ)))
      (r'.bind (ValValSem.toElChecked (w'.denot orc τ))) := by
  apply PartialRel.bind _ _ ?_ h
  intro v v' hv
  obtain ⟨a, b, ha, hb, hab⟩ := extract_checked_related orc τ w w' v v' hv
  rw [ha, hb]
  exact hab

/-- Checked reification followed by extraction preserves the two-world
relation. This is a relational round trip, not equality of unrestricted
higher-order callbacks. -/
theorem checked_roundtrip_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (a : (w.denot orc τ).El) (b : (w'.denot orc τ).El)
    (h : Related orc τ w w' a b) :
    PartialRel (Related orc τ w w')
      ((ValValSem.fromElChecked (w.denot orc τ) a).bind
        (ValValSem.toElChecked (w.denot orc τ)))
      ((ValValSem.fromElChecked (w'.denot orc τ) b).bind
        (ValValSem.toElChecked (w'.denot orc τ))) :=
  extract_checked_results_related orc τ w w' _ _ (reify_checked_related orc τ w w' a b h)

/-- Evaluate a function application using its actual strict domain decoder. -/
theorem eval_appV_fn_domain_checked (orc : FFSOracleSem) (w : World)
    (ef ea : ValExpr) (out dom : ValTy)
    (f : (w.denot orc dom).El → Except DimError ValValSem)
    (v : ValValSem) (a : (w.denot orc dom).El)
    (hd : (ValExpr.inferTypeCtx w.types ef).domain = dom)
    (hf : denotValB_semS orc w.env w.types w.values ef =
      .ok (.fn (w.denot orc dom).El f))
    (hv : denotValB_semS orc w.env w.types w.values ea = .ok v)
    (ha : ValValSem.toElDomainChecked (w.denot orc dom) v = .ok a) :
    denotValB_semS orc w.env w.types w.values (.appV ef ea) = f a := by
  subst dom
  rw [denotValB_semS.eq_28]
  simp only [hf, hv, ↓reduceDIte, ha]

/-- Live application preserves related successful operands. The result fibre
is selected by the values actually returned by the strict domain decoder.
Inferred domain annotations are explicit: result annotations do not determine
the runtime domain check. -/
theorem eval_appV_related (orc : FFSOracleSem) (τ₀ τ₁ out out' : ValTy)
    (w w' : World) (ef ea ef' ea' : ValExpr) (f g v v' : ValValSem)
    (hdom : (ValExpr.inferTypeCtx w.types ef).domain = τ₀)
    (hdom' : (ValExpr.inferTypeCtx w'.types ef').domain = τ₀)
    (hef : denotValB_semS orc w.env w.types w.values ef = .ok f)
    (hef' : denotValB_semS orc w'.env w'.types w'.values ef' = .ok g)
    (hea : denotValB_semS orc w.env w.types w.values ea = .ok v)
    (hea' : denotValB_semS orc w'.env w'.types w'.values ea' = .ok v')
    (hf : RuntimeRelated orc (.piTy τ₀ τ₁) w w' f g)
    (hv : RuntimeRelated orc τ₀ w w' v v') :
    ∃ a b, ValValSem.toElDomainChecked (w.denot orc τ₀) v = .ok a ∧
      ValValSem.toElDomainChecked (w'.denot orc τ₀) v' = .ok b ∧
      Related orc τ₀ w w' a b ∧
      PartialRel (RuntimeRelated orc τ₁ (w.push orc τ₀ a) (w'.push orc τ₀ b))
        (denotValB_semS orc w.env w.types w.values (.appV ef ea))
        (denotValB_semS orc w'.env w'.types w'.values (.appV ef' ea')) := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := extract_domain_checked_related orc τ₀ w w' v v' hv
  refine ⟨a, b, ha, hb, hab, ?_⟩
  cases f <;> cases g <;> try exact hf.elim
  rename_i T f U g
  obtain ⟨hT, hU, hfg⟩ := hf
  subst T; subst U
  rw [eval_appV_fn_domain_checked orc w ef ea out τ₀ f v a hdom hef hea ha,
    eval_appV_fn_domain_checked orc w' ef' ea' out' τ₀ g v' b hdom' hef' hea' hb]
  exact hfg a b hab

/-- Base-domain annotations may differ syntactically when their semantic
dimensions coincide. No runtime resizing or callback equality is needed. -/
theorem eval_appV_space_domain_related (orc : FFSOracleSem) (s u u' : ValSpace)
    (τ₁ out out' : ValTy)
    (w w' : World) (ef ea ef' ea' : ValExpr) (f g v v' : ValValSem)
    (hdom : (ValExpr.inferTypeCtx w.types ef).domain = .space u)
    (hdom' : (ValExpr.inferTypeCtx w'.types ef').domain = .space u')
    (hdim : ValSpace.dof (orc w.env w.types w.values) u =
      ValSpace.dof (orc w.env w.types w.values) s)
    (hdim' : ValSpace.dof (orc w'.env w'.types w'.values) u' =
      ValSpace.dof (orc w'.env w'.types w'.values) s)
    (hef : denotValB_semS orc w.env w.types w.values ef = .ok f)
    (hef' : denotValB_semS orc w'.env w'.types w'.values ef' = .ok g)
    (hea : denotValB_semS orc w.env w.types w.values ea = .ok v)
    (hea' : denotValB_semS orc w'.env w'.types w'.values ea' = .ok v')
    (hf : RuntimeRelated orc (.piTy (.space s) τ₁) w w' f g)
    (hv : RuntimeRelated orc (.space s) w w' v v') :
    ∃ a b, ValValSem.toElDomainChecked (w.denot orc (.space s)) v = .ok a ∧
      ValValSem.toElDomainChecked (w'.denot orc (.space s)) v' = .ok b ∧
      Related orc (.space s) w w' a b ∧
      PartialRel (RuntimeRelated orc τ₁ (w.push orc (.space s) a) (w'.push orc (.space s) b))
        (denotValB_semS orc w.env w.types w.values (.appV ef ea))
        (denotValB_semS orc w'.env w'.types w'.values (.appV ef' ea')) := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := extract_domain_checked_related orc (.space s) w w' v v' hv
  refine ⟨a, b, ha, hb, hab, ?_⟩
  cases f <;> cases g <;> try exact hf.elim
  rename_i T f U g
  obtain ⟨hT, hU, hfg⟩ := hf
  subst T; subst U
  have ha' : ValValSem.toElDomainChecked (w.denot orc (.space u)) v = .ok a := by
    cases v <;> simpa only [World.denot, denotValTyS, ValValSem.toElDomainChecked,
      ValValSem.toElChecked, hdim] using ha
  have hb' : ValValSem.toElDomainChecked (w'.denot orc (.space u')) v' = .ok b := by
    cases v' <;> simpa only [World.denot, denotValTyS, ValValSem.toElDomainChecked,
      ValValSem.toElChecked, hdim'] using hb
  rw [eval_appV_fn_domain_checked orc w ef ea out (.space u) f v a hdom hef hea ha',
    eval_appV_fn_domain_checked orc w' ef' ea' out' (.space u') g v' b hdom' hef' hea' hb']
  exact hfg a b hab

end GLang.PaperValueDomains
