import GLang.Proofs.Value.Presentation.PaperValueRecursiveCorrespondence
import Lean
open GLang GLang.PaperValueDomains GLang.PaperValueResults
open ExtensionalQuotient
noncomputable section

-- The success domain at a space is the actual finite array type.
example (orc : FFSOracleSem) (s : ValSpace) (w : World)
    (hc : TypeCoherent orc (.space s) w w) :
    (recursiveDomain orc (.space s) w hc).Carrier =
      SizedFlatArray (ValSpace.dof (orc w.env w.types w.values) s) := rfl

-- The arrow domain contains EVERY dependent partial section, without a
-- definability, computability, or extra relational premise on the section.
example (orc : FFSOracleSem) (d c : ValTy) (w : World)
    (hc : TypeCoherent orc (.piTy d c) w w)
    (F : (a : (recursiveDomain orc d w hc.1).Carrier) →
      let q := (recursiveDomain orc d w hc.1).equiv.symm a
      Except DimError (recursiveDomain orc c (w.push orc d q.out.val)
        (hc.2 _ _ q.out.property)).Carrier) :
    ∃ f, (recursiveDomain orc (.piTy d c) w hc).equiv f = F :=
  (recursiveDomain orc (.piTy d c) w hc).equiv.surjective F

-- Errors remain distinguishable even at arbitrary higher-order types.
example (orc : FFSOracleSem) (τ : ValTy) (w : World)
    (hc : TypeCoherent orc τ w w) (e e' : DimError) :
    recursiveResultEquiv orc τ w hc (Quotient.mk _ ⟨.error e, rfl⟩) =
      recursiveResultEquiv orc τ w hc (Quotient.mk _ ⟨.error e', rfl⟩) ↔ e = e' := by
  simp

example {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (ρ : ValEnvSem) (hρ : EnvWF ε ρ) (he : ValHasType ε e τ) :
    Except DimError (recursiveDomain directOracle τ ⟨ρ,[],[]⟩
      (valueDomainSoundness ρ hρ he).1).Carrier := valueDenotation ρ hρ he

open Lean Elab Command
elab "check_recursive_domain_axioms" : command => do
  let foundations := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``PER.resultEquiv, ``spaceDomainEquiv, ``functionDomainEquiv,
      ``dependentApply_injective, ``recursiveDomain, ``recursiveResultEquiv,
      ``recursiveDomain_apply, ``recursiveResultEquiv_error, ``recursiveResultEquiv_ok] do
    for ax in ← Lean.collectAxioms n do
      unless foundations.contains ax do
        throwError "Unexpected recursive domain assumption {n}: {ax}"
  for n in [``valueDenotation, ``valueDenotation_raw_eq, ``valueDenotation_error] do
    for ax in ← Lean.collectAxioms n do
      unless foundations.contains ax || ax == ``GLang.Matrix.exists_gsvd do
        throwError "Unexpected production correspondence assumption {n}: {ax}"
  logInfo "Recursive domain equivalence uses foundations only; production bridge inherits only GSVD."
check_recursive_domain_axioms
