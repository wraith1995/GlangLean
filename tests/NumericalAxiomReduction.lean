import GLang.Numerics.SVD.ValueSVD
import GLang.Proofs.Adequacy.Raw.Terms.RawTermsRREFLexInd
import Lean

open Lean Elab Command

/-- All numerical existence interfaces are proved from standard foundations. -/
elab "check_numerical_axiom_reduction" : command => do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``GLang.Matrix.exists_gsvd, ``GLang.Matrix.exists_svd, ``GLang.standardRREFLexInd_proved,
      ``GLang.Matrix.exists_rrefDecomp_inductive_step, ``GLang.Matrix.exists_rrefDecomp] do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless standard.contains ax do
        throwError "Unexpected assumption in {n}: {ax}"
  logInfo "GSVD, SVD, RREF existence and LexInd coherence are foundation-only."

check_numerical_axiom_reduction
#print axioms GLang.Matrix.exists_gsvd
#print axioms GLang.Matrix.exists_svd
#print axioms GLang.standardRREFLexInd_proved
