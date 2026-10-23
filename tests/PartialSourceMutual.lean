import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMutual
import Lean

open Lean Elab Command
elab "check_partial_source_mutual_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``GLang.PartialAdequacy.term_mutual,
      ``GLang.PartialAdequacy.arm_llam_assemble,
      ``GLang.PartialAdequacy.arm_llam_assemble_real,
      ``GLang.PartialAdequacy.arm_cob_terms_rref,
      ``GLang.PartialAdequacy.ImageSVDs.arm_cob_image_svds_facts] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected partial source mutual axiom {n}: {ax}"
  logInfo "Complete source partial adequacy: foundations and existing GSVD only."
check_partial_source_mutual_axioms

-- The conclusion names the actual partial evaluator, not a total fallback.
example {Δ Γ Ψ e b v τv} (h : GLang.S.Term Δ Γ Ψ e b v τv) :
    GLang.PartialAdequacy.TermFactsSubctx GLang.PartialDirectOracle.oracle Δ Γ Ψ e b v τv :=
  GLang.PartialAdequacy.term_mutual h
