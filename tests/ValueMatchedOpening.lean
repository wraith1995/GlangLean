import GLang.Proofs.Value.Binding.ValueMatchedOpening
import Lean
open GLang GLang.ValueDependency Lean Elab Command
elab "check_matched_opening_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``typeAnnotations_open_inverse, ``exprAnnotations_open_inverse,
      ``matched_type_open, ``matched_expr_open] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected matched-opening assumption in {n}: {ax}"
  logInfo "Reverse opening and matched closure binder transport use foundations only."
check_matched_opening_axioms
