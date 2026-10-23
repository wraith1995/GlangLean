import GLang.Proofs.Value.Presentation.PaperValueOracleExtensionality

/-! Typed, finite current-oracle obligations for the original dependent
value judgments. These are induction steps, not an assumed global oracle law. -/
namespace GLang.PaperValueDomains

/-- A query retains the space and witness used by the current rank equation. -/
structure SpaceQuery where
  prop : ValFFSProp
  parent : ValSpace
  witness : ValExpr

/-- All queries needed to compare a space, including queries in an FFS parent.
Witness-internal queries belong to the witness typing induction, not this list. -/
def spaceQueries : ValSpace → List SpaceQuery
  | .real | .empty => []
  | .dsum s t | .tprod s t => spaceQueries s ++ spaceQueries t
  | .ffs p s e => ⟨p,s,e⟩ :: spaceQueries s

/-- Every occurring query in an originally valid space has an originally typed
witness and valid parent. No separate fragment typing judgment is introduced. -/
theorem ValSValid.query_typed {ε : ValCtx} {s : ValSpace}
    (h : GLang.ValSValid ε s) (q : SpaceQuery) (hq : q ∈ spaceQueries s) :
    Nonempty (GLang.ValSValid ε q.parent) ∧
      Nonempty (ValHasType ε q.witness (.space q.parent)) := by
  cases h with
  | real => simp [spaceQueries] at hq
  | empty => simp [spaceQueries] at hq
  | dsum h0 h1 =>
    simp only [spaceQueries, List.mem_append] at hq
    rcases hq with hq | hq
    · exact ValSValid.query_typed h0 q hq
    · exact ValSValid.query_typed h1 q hq
  | tprod h0 h1 =>
    simp only [spaceQueries, List.mem_append] at hq
    rcases hq with hq | hq
    · exact ValSValid.query_typed h0 q hq
    · exact ValSValid.query_typed h1 q hq
  | ffs h0 h1 he =>
    simp only [spaceQueries, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨⟨.tprod h0 h1⟩, ⟨he⟩⟩
    · simp only [spaceQueries, List.mem_append] at hq
      rcases hq with hq | hq
      · exact ValSValid.query_typed h0 q hq
      · exact ValSValid.query_typed h1 q hq
termination_by sizeOf s

/-- Exact FFS branch of the original mutual induction. The three premises are
precisely its two space IHs and its witness term IH, restricted to this query. -/
theorem original_ffs_oracle_step (w w' : World)
    (p : ValFFSProp) (s t : ValSpace) (e : ValExpr) (hΓ : w.types = w'.types)
    (hs : SpaceOracleAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) s)
    (ht : SpaceOracleAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) t)
    (he : PartialRel (RuntimeRelated directOracle (.space (.tprod s t)) w w')
      (denotValB_semS directOracle w.env w.types w.values e)
      (denotValB_semS directOracle w'.env w'.types w'.values e)) :
    SpaceOracleAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) (.ffs p (.tprod s t) e) :=
  directOracle_eq_of_same_query w w' p (.tprod s t) e hΓ
    (leafAgreement_shapes _ _ (.tprod s t) ⟨hs,ht⟩).1
    (base_results_eq_of_related directOracle _ _ _ _ _ he)

/-- Reconstruct all space/shape agreement from the finite recursive witness
obligations. Each obligation is discharged by the original term induction;
`query_typed` recovers its exact original typing evidence. -/
theorem spaceAgreement_of_query_results (s : ValSpace) (w w' : World) (hΓ : w.types = w'.types)
    (he : ∀ q ∈ spaceQueries s,
      PartialRel (RuntimeRelated directOracle (.space q.parent) w w')
        (denotValB_semS directOracle w.env w.types w.values q.witness)
        (denotValB_semS directOracle w'.env w'.types w'.values q.witness)) :
    SpaceOracleAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) s := by
  cases s with
  | empty => trivial
  | real => trivial
  | dsum s t | tprod s t =>
    exact ⟨spaceAgreement_of_query_results s w w' hΓ (fun q hq =>
        he q (List.mem_append_left _ hq)),
      spaceAgreement_of_query_results t w w' hΓ (fun q hq =>
        he q (List.mem_append_right _ hq))⟩
  | ffs p s e =>
    exact directOracle_eq_of_same_query w w' p s e hΓ
      (leafAgreement_shapes _ _ s
        (spaceAgreement_of_query_results s w w' hΓ (fun q hq =>
          he q (List.mem_cons_of_mem _ hq)))).1
      (base_results_eq_of_related directOracle _ _ _ _ _ (he ⟨p,s,e⟩ List.mem_cons_self))
termination_by sizeOf s

/-- An actual original-judgment dependent-space theorem: arbitrarily nested
FFS dimensions whose witnesses are declared variables agree in related worlds.
The extra condition is purely syntactic; evaluation invariance is proved. -/
theorem ValSValid.oracleAgreement_namedQueries {ε : ValCtx} {s : ValSpace}
    (h : GLang.ValSValid ε s) (ρ ρ' : ValEnvSem)
    (hρ : EnvironmentsRelated directOracle ε ρ ρ')
    (hn : ∀ q ∈ spaceQueries s, ∃ x, q.witness = .var x (.space q.parent)) :
    SpaceOracleAgreement (directOracle ρ [] []) (directOracle ρ' [] []) s := by
  apply spaceAgreement_of_query_results s ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ rfl
  intro q hq
  obtain ⟨x, hx⟩ := hn q hq
  obtain ⟨_, ⟨ht⟩⟩ := ValSValid.query_typed h q hq
  rw [hx] at ht ⊢
  cases ht with
  | var hlookup => exact eval_var_related directOracle ε ρ ρ' hρ x _ hlookup

end GLang.PaperValueDomains
