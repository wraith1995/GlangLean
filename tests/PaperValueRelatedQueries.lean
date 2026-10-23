import GLang.Proofs.Value.Presentation.PaperValueRelatedQueries
import Lean
open GLang GLang.PaperValueDomains
open Lean Elab Command
elab "check_related_query_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``original_primitive_related_output, ``original_primitive_related_queries] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "Unexpected related query assumption {n}: {ax}"
  logInfo "Original numeric relation query steps inherit only existing GSVD existence."
check_related_query_axioms
