import GLang.Proofs.Value.Presentation.PaperValueCheckedExtensionality
import Lean

open GLang GLang.PaperValueDomains

-- The observable contract includes out-of-bounds accesses; it does not only
-- compare entries below a separately supplied index bound.
example (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v') :
    ∀ i, v.readChecked i = v'.readChecked i :=
  read_checked_related orc τ w w' v v' h

open Lean Elab Command
elab "check_strict_extensionality_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let live := [``eval_appV_fn_domain_checked, ``eval_appV_related, ``eval_appV_space_domain_related]
  for n in [``extract_domain_checked_related, ``extract_checked_related,
      ``reify_checked_related, ``read_checked_related, ``read_result_checked_related,
      ``extract_checked_results_related, ``checked_roundtrip_related,
      ``eval_appV_fn_domain_checked, ``eval_appV_related, ``eval_appV_space_domain_related] do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax || (live.contains n && ax == ``GLang.Matrix.exists_gsvd) do
        throwError "Unexpected checked extensionality assumption in {n}: {ax}"
  logInfo "Checked conversion/observation bridges use foundations only; live applications add at most existing GSVD existence."

check_strict_extensionality_axioms
