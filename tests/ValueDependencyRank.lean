import GLang.Proofs.Value.Queries.ValueDependencyRank
import Lean
open GLang GLang.ValueDependency Lean Elab Command

example (t : ValTy) (x : VName) (h : x ∈ t.fv) :
    ∃ a, (x, a) ∈ typeAnnotations t ∧ a.size < t.size :=
  fv_has_smaller_annotation t x h

example (x : VName) (d a b : ValTy) (k : Nat)
    (ha : x ∉ a.fv) (hb : x ∉ b.fv)
    (h : ValTy.openRec k (.var x d) a = b) : a = b :=
  opened_annotation_eq x d a b k ha hb h

elab "check_dependency_rank_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``fv_has_smaller_annotation, ``opened_annotation_eq,
      ``typed_var_annotation_lookup, ``typeAnnotations_rank,
      ``typeAnnotations_close_fresh, ``typeAnnotations_open_occurrence,
      ``annotation_agreement_of_opening, ``context_dependency_rank_of_annotation_agreement] do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected dependency-rank assumption in {n}: {ax}"
  logInfo "Syntactic annotation rank and fresh opening cancellation use foundations only."
check_dependency_rank_axioms
