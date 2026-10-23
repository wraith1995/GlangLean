import GLang.Proofs.Value.Presentation.PaperValueOracleExtensionality
import GLang.Proofs.Adequacy.Foundations.ValueSoundnessSemS
open GLang GLang.PaperValueDomains
namespace OracleCounterexample
noncomputable section

def one : FlatArray := FlatArray.ofFn 1 (fun _ => 1)
def always : ValValSem := .fn FlatArray (fun _ => .ok (.array one))
def onlyValid : ValValSem := .fn FlatArray (fun a =>
  if a.length = 1 then .ok (.array one) else .error .mismatch)
def ρ : ValEnvSem := fun _ => always
def ρ' : ValEnvSem := fun _ => onlyValid

def forged : ValExpr := .appV
  (.var "f" (.piTy (.space .empty) (.space .real))) (.zero .empty)

theorem callbacks_related : RuntimeRelated directOracle (.piTy (.space .real) (.space .real))
    ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ always onlyValid := by
  refine ⟨rfl, rfl, ?_⟩
  intro a b hab
  have hb : b.length = 1 := by simpa [Related] using hab.2.2
  simp [hb, PartialRel, RuntimeRelated, Related, one]

theorem forged_success (orc : FFSOracleSem) : denotValB_semS orc ρ [] [] forged = .ok (.array one) := by
  simp [forged, denotValB_semS, ρ, always, ValExpr.inferTypeCtx, ValTy.domain,
    denotValTyS, ValValSem.toElDomainChecked, ValValSem.toElChecked, ValValSem.arrayOf, ValExpr.inferSpaceCtx, ValTypeSem.El]

theorem forged_error (orc : FFSOracleSem) : denotValB_semS orc ρ' [] [] forged = .error .mismatch := by
  simp [forged, denotValB_semS, ρ', onlyValid, ValExpr.inferTypeCtx, ValTy.domain,
    denotValTyS, ValValSem.toElDomainChecked, ValValSem.toElChecked, ValValSem.arrayOf, ValExpr.inferSpaceCtx, ValTypeSem.El]

theorem one_matrix : denotAsMatrix 1 1 one.get = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i; fin_cases j
  simp [denotAsMatrix, one, FlatArray.get, FlatArray.ofFn]

def declared : ValCtx := Finmap.insert "f" (.piTy (.space .real) (.space .real)) ∅

theorem related_environments : EnvironmentsRelated directOracle declared ρ ρ' := by
  intro x τ hx
  by_cases h : x = "f"
  · subst x
    simp [declared] at hx
    subst τ
    exact callbacks_related
  · simp [declared, h] at hx

/-- Both callbacks also meet the existing unary canonical contract. -/
theorem callbacks_canonical :
    ValCanonicalSoundOfDenotSemS directOracle ρ [] []
      (.piTy (.space .real) (.space .real)) always ∧
    ValCanonicalSoundOfDenotSemS directOracle ρ' [] []
      (.piTy (.space .real) (.space .real)) onlyValid := by
  constructor
  · refine ⟨rfl, ?_⟩
    intro a out ho
    cases ho
    simp [ValCanonicalSoundOfDenotSemS, one]
  · refine ⟨rfl, ?_⟩
    intro a out ho
    dsimp only at ho
    split at ho
    · cases ho
      simp [ValCanonicalSoundOfDenotSemS, one]
    · contradiction

/-- The differing observation deliberately lies outside the declared typing
contract: the variable annotation falsifies its stored function domain. -/
theorem forged_not_typed (τ : ValTy) : ¬ Nonempty (ValHasType declared forged τ) := by
  rintro ⟨h⟩
  cases h with
  | appV hf _ _ _ =>
    cases hf with
    | var hx => simp [declared] at hx

private theorem forged_finite :
    ValueQueryDependencies.Finite (.space [] (.ffs .image (.tprod .real .real) forged)) := by
  have hv : ValHasType (Finmap.insert "f" (.piTy (.space .empty) (.space .real)) ∅)
      forged (.space .real) := by
    apply ValHasType.appV (ValHasType.var (by simp)) (ValHasType.zero .empty) rfl
    exact .space .real
  have hctx : RuntimeValue.ValCtxValid (Finmap.insert "f" (.piTy (.space .empty) (.space .real)) ∅) :=
    (show RuntimeValue.ValCtxValid (∅ : ValCtx) from by intro x t h; simp at h).insert (x := "f") Finmap.notMem_empty (.piTy ∅ (.space .empty) (fun _ _ => .space .real))
  exact .ffs (.tprod .real .real)
    (RuntimeValue.validExpr_queryFinite hctx hv.runtime).1

theorem direct_dimension_left :
    directOracle ρ [] [] .image (.tprod .real .real) forged = 1 := by
  rw [directOracle_rank_equation ⟨ρ, [], []⟩ _ _ _ forged_finite]
  simp [ffsOperandRank, ValSpace.shpOf, forged_success, one_matrix, ffsDim]

theorem direct_dimension_right :
    directOracle ρ' [] [] .image (.tprod .real .real) forged = 0 := by
  rw [directOracle_rank_equation ⟨ρ', [], []⟩ _ _ _ forged_finite]
  simp [ffsOperandRank, ValSpace.shpOf, forged_error, ffsDim]

/-- Even the strict evaluator cannot make arbitrary forged queries respect a
relation constrained only at the environment's genuine declared type. -/
theorem all_query_agreement_fails :
    ¬ (∀ p s e, directOracle ρ [] [] p s e = directOracle ρ' [] [] p s e) := by
  intro h
  have bad := h .image (.tprod .real .real) forged
  rw [direct_dimension_left, direct_dimension_right] at bad
  contradiction

/-- The all-query sufficient interface cannot be instantiated merely from
related declared environments, even when both compared worlds are roots. -/
theorem no_all_query_world_compatibility :
    ¬ WorldCompatibility directOracle (fun w w' =>
      w.types = [] ∧ w'.types = [] ∧ w.values = [] ∧ w'.values = [] ∧
      EnvironmentsRelated directOracle declared w.env w'.env) := by
  intro h
  apply all_query_agreement_fails
  exact h.oracle ⟨ρ, [], []⟩ ⟨ρ', [], []⟩
    ⟨rfl, rfl, rfl, rfl, related_environments⟩

#print axioms directOracle_eq_of_related_witness
#print axioms directOracle_variable_related
#print axioms related_environments
#print axioms all_query_agreement_fails
#print axioms callbacks_canonical
#print axioms forged_not_typed
#print axioms no_all_query_world_compatibility
end
end OracleCounterexample
