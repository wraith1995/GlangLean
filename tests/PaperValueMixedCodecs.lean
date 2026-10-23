import GLang.Proofs.Value.Presentation.PaperValueMixedCodecs
import Lean
open GLang GLang.PaperValueDomains
open Lean Elab Command
elab "check_mixed_codec_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``runtime_related_symm, ``runtime_normalize_right,
      ``runtime_normalize_left, ``runtime_normalize_domain_right, ``reify_mixed_related] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "Unexpected mixed codec assumption {n}: {ax}"
  logInfo "Mixed higher-order codec laws use foundations only."
check_mixed_codec_axioms
