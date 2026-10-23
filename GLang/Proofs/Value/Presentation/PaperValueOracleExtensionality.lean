import GLang.Proofs.Value.Presentation.PaperValueExtensionality
import GLang.Proofs.Adequacy.Total.DirectOracle
import GLang.Proofs.Value.Runtime.RuntimeValueEmbedding
import GLang.Proofs.Value.Runtime.RuntimeValueQueryFinite
import GLang.Proofs.Value.Queries.ValueQueryConstructors

/-! The numerical step for a typed-query logical-relation argument about the
current oracle. -/
namespace GLang.PaperValueDomains

/-- At a base type, error-sensitive runtime relatedness entails exact equality
of the two evaluator results, including finite storage and failure. -/
theorem base_results_eq_of_related (orc : FFSOracleSem) (s : ValSpace)
    (w w' : World) (r r' : Except DimError ValValSem)
    (h : PartialRel (RuntimeRelated orc (.space s) w w') r r') : r = r' := by
  cases r with
  | error err =>
    cases r' with
    | error err' => exact congrArg Except.error h
    | ok v' => exact h.elim
  | ok v =>
    cases r' with
    | error err' => exact h.elim
    | ok v' =>
      cases v <;> cases v' <;> try exact h.elim
      exact congrArg (fun a => Except.ok (ValValSem.array a)) h.1

/-- Current fixed-point equation in the two-world interface. No oracle
specification is supplied by the caller, at either empty or nonempty stacks. -/
theorem directOracle_rank_equation (w : World) (p : ValFFSProp)
    (s : ValSpace) (e : ValExpr)
    (hf : ValueQueryDependencies.Finite (.space w.types (.ffs p s e))) :
    directOracle w.env w.types w.values p s e =
      ffsDim p (ValSpace.shpOf (directOracle w.env w.types w.values) s)
        (ffsOperandRank directOracle w.env w.types w.values s e) :=
  DirectOracleLocality.derivedDirectQuery_rank_eq_production
    ⟨w.env, w.types, w.values, p, s, e⟩ hf

/-- Uncertified raw queries take only the compatibility fallback. -/
theorem directOracle_zero_of_not_finite (w : World) (p : ValFFSProp)
    (s : ValSpace) (e : ValExpr)
    (hf : ¬ ValueQueryDependencies.Finite (.space w.types (.ffs p s e))) :
    directOracle w.env w.types w.values p s e = 0 := by
  change DirectOracleWF.derivedDirectQuery ⟨w.env,w.types,w.values,p,s,e⟩ = 0
  rw [DirectOracleWF.derivedDirectQuery_eq]
  simp [DirectOracleWF.derivedStep, DirectOracleWF.Query.derivedMeasure,
    DirectOracleWF.Query.certifiedMeasure, DirectOracleWF.Query.node,
    ValueQueryDependencies.rank, hf]

/-- Identical query syntax and type stacks share the finite-dependency gate. -/
theorem directOracle_eq_of_same_query (w w' : World) (p : ValFFSProp)
    (s : ValSpace) (e : ValExpr) (hΓ : w.types = w'.types)
    (hs : ValSpace.shpOf (directOracle w.env w.types w.values) s =
      ValSpace.shpOf (directOracle w'.env w'.types w'.values) s)
    (he : denotValB_semS directOracle w.env w.types w.values e =
      denotValB_semS directOracle w'.env w'.types w'.values e) :
    directOracle w.env w.types w.values p s e =
      directOracle w'.env w'.types w'.values p s e := by
  by_cases hf : ValueQueryDependencies.Finite (.space w.types (.ffs p s e))
  · have hf' : ValueQueryDependencies.Finite (.space w'.types (.ffs p s e)) := hΓ ▸ hf
    rw [directOracle_rank_equation _ _ _ _ hf,
      directOracle_rank_equation _ _ _ _ hf', hs]
    congr 1
    unfold ffsOperandRank
    rw [hs, he]
  · have hf' : ¬ ValueQueryDependencies.Finite (.space w'.types (.ffs p s e)) := hΓ ▸ hf
    rw [directOracle_zero_of_not_finite _ _ _ _ hf,
      directOracle_zero_of_not_finite _ _ _ _ hf']

/-- One numerical step of the extensionality induction: equal parent shapes
and related base results of the queried witness give identical FFS dimensions.
The witness-result hypothesis is the recursive evaluator obligation, not a
claim that related named environments alone already discharge it. -/
theorem directOracle_eq_of_related_witness (w w' : World) (p : ValFFSProp)
    (s : ValSpace) (e e' : ValExpr)
    (hf : ValueQueryDependencies.Finite (.space w.types (.ffs p s e)))
    (hf' : ValueQueryDependencies.Finite (.space w'.types (.ffs p s e')))
    (hshape : ValSpace.shpOf (directOracle w.env w.types w.values) s =
      ValSpace.shpOf (directOracle w'.env w'.types w'.values) s)
    (heval : PartialRel (RuntimeRelated directOracle (.space s) w w')
      (denotValB_semS directOracle w.env w.types w.values e)
      (denotValB_semS directOracle w'.env w'.types w'.values e')) :
    directOracle w.env w.types w.values p s e =
      directOracle w'.env w'.types w'.values p s e' := by
  have heq := base_results_eq_of_related directOracle s w w' _ _ heval
  rw [directOracle_rank_equation _ _ _ _ hf, directOracle_rank_equation _ _ _ _ hf', hshape]
  congr 1
  unfold ffsOperandRank
  rw [hshape, heq]

/-- Primitive-leaf agreement is sufficient parent information for the numeric
step. This does not demand equality on unrelated or ill-typed queries. -/
theorem directOracle_eq_of_leafAgreement (w w' : World) (p : ValFFSProp)
    (s : ValSpace) (e e' : ValExpr)
    (hf : ValueQueryDependencies.Finite (.space w.types (.ffs p s e)))
    (hf' : ValueQueryDependencies.Finite (.space w'.types (.ffs p s e')))
    (hparent : SpaceOracleAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) s)
    (heval : PartialRel (RuntimeRelated directOracle (.space s) w w')
      (denotValB_semS directOracle w.env w.types w.values e)
      (denotValB_semS directOracle w'.env w'.types w'.values e')) :
    directOracle w.env w.types w.values p s e =
      directOracle w'.env w'.types w'.values p s e' :=
  directOracle_eq_of_related_witness w w' p s e e' hf hf'
    (leafAgreement_shapes _ _ s hparent).1 heval

/-- A concrete live-oracle case, requiring no evaluator-invariance premise:
querying a declared base variable in related named environments preserves its
FFS dimension, provided the parent leaves agree. -/
theorem directOracle_variable_related (ε : ValCtx) (ρ ρ' : ValEnvSem)
    (hρ : EnvironmentsRelated directOracle ε ρ ρ')
    (x : VName) (s : ValSpace) (hx : ε.lookup x = some (.space s))
    (hparent : SpaceOracleAgreement (directOracle ρ [] []) (directOracle ρ' [] []) s)
    (p : ValFFSProp) :
    directOracle ρ [] [] p s (.var x (.space s)) =
      directOracle ρ' [] [] p s (.var x (.space s)) :=
  directOracle_eq_of_same_query ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ p s _ rfl
    (leafAgreement_shapes _ _ s hparent).1
    (base_results_eq_of_related directOracle s _ _ _ _
      (eval_var_related directOracle ε ρ ρ' hρ x (.space s) hx))

end GLang.PaperValueDomains
