import GLang.Proofs.Value.Partial.PartialValueNamedSubstitution
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceValueBridge
import Lean

namespace GLang.PartialValueSubstitutionTests
open GLang

-- Successful substitution must preserve a failed query: an empty matrix
-- payload remains malformed after substituting a scalar into an unused binder.
private def matTy : ValTy := .space (.tprod .real .real)
private def codomain : ValTy := .space (.ffs .kernel (.tprod .real .real)
  (.var "m" matTy))

example (ρ : ValEnvSem) (hρ : ρ "m" = .array FlatArray.empty) :
    denotValTyPartial PartialDirectOracle.oracle ρ [] []
      (ValTy.instantiate (.rlit 3) codomain) = .error .mismatch := by
  simp only [codomain, matTy, ValTy.instantiate, ValTy.openRec, ValSpace.openRec, ValExpr.openRec]
  simp only [denotValTyPartial, ValSpace.dofPartial, ValSpace.shpOfPartial]
  rw [PartialDirectLocality.oracle_eq (hf := by
    refine ⟨6, ?_⟩
    simp [ValueQueryDependencies.Bounded, ValueQueryDependencies.children,
      ValueQueryDependencies.exprChildren, ValExpr.inferSpaceCtx,
      ValExpr.inferTypeCtx, ValTy.spaceOf])]
  simp [denotValB_partial, hρ, ValSpace.shpOfPartial, ValSpace.dofPartial,
    ffsDimensionPartial, ffsOperandRankPartial, FlatArray.empty,
    bind, Except.bind, pure, Except.pure]

end GLang.PartialValueSubstitutionTests

open Lean Elab Command
elab "check_partial_substitution_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``GLang.PartialValueSubstitution.namedSpaceSubstitution,
      ``GLang.PartialValueSubstitution.namedTypeSubstitution,
      ``GLang.PartialValueSubstitution.namedExprSubstitution,
      ``GLang.PartialValueSubstitution.partial_original_type_instantiation,
      ``GLang.PartialValueSubstitution.partial_original_typed_beta_evaluation,
      ``GLang.PartialValueSubstitution.RawPresentation.reshape,
      ``GLang.PartialAdequacy.Agree.representation_transport,
      ``GLang.PartialAdequacy.DimsAt.valueOpenPush] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected partial substitution axiom {n}: {ax}"
  logInfo "Full original typed substitution preserves partial errors with no new axioms."
check_partial_substitution_axioms
