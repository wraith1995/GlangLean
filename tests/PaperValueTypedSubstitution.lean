import GLang.Proofs.Value.Presentation.PaperValueTypedSubstitution
open GLang
noncomputable section

-- Instantiating an originally valid FFS codomain records the actual matrix
-- expression in its dimension query, not a fresh name or an abstract carrier.
example : ValTValid (∅ : ValCtx)
    (ValTy.instantiate (.zero (.tprod .real .real))
      (.space (.ffs .kernel (.tprod .real .real) (.bvar 0)))) .base := by
  apply ValTValid.instantiate_of_open (x := "matrix")
    (d := .space (.tprod .real .real))
    (ValHasType.zero (.tprod .real .real))
    (ValExpr.lc.zero (ValSpace.lc.tprod .real .real))
  · rw [← Finmap.lookup_eq_none]; exact Finmap.lookup_empty _
  · simp [ValTy.fv, ValSpace.fv]
  · simp [ValTy.fv, ValSpace.fv, ValExpr.fv]
  · intro y σ h
    simp at h
  · exact .space (.ffs .real .real (.var (by simp)))

open Lean Elab Command
elab "check_original_beta_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ValCtx.substMap_eq_of_fresh, ``ValTValid.instantiate_of_open,
      ``ValHasType.instantiate_of_open] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected beta derivation axiom in {n}: {ax}"
  logInfo "Original beta derivation builders use only foundations."
check_original_beta_axioms
