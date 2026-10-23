import GLang.Proofs.Value.Presentation.PaperValueRawReshapeCoherence
open GLang GLang.PaperValueDomains

example (orc : FFSOracleSem) (w : Bool → World) :
    ReshapeCoherent orc
      (.piTy (.space .real) (.piTy (.space .empty) (.space .real)))
      (.piTy (.space .empty) (.piTy (.space .real) (.space .empty)))
      (w false) (w true) (w false).types (w true).types (w false).values (w true).values := by
  apply reshapeCoherent_of_rawFamily _ _ orc w
  all_goals simp [RawTypeCoherent, SpaceOracleAgreement]

open Lean Elab Command
elab "check_raw_reshape_coherence_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``rawArgument_coherent, ``reshapeCoherent_of_rawFamilies,
      ``reshapeCoherent_of_rawFamily, ``eval_reshape_related_of_rawFamily] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax ||
          (n == ``eval_reshape_related_of_rawFamily && ax == ``GLang.Matrix.exists_gsvd) do
        throwError "Unexpected dependent reshape coherence axiom in {n}: {ax}"
  logInfo "Dependent raw reshape: foundations; evaluator inherits existing GSVD only."
check_raw_reshape_coherence_axioms
