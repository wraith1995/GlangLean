import GLang.Proofs.Value.Presentation.PaperValueOriginalFamily
import Lean

open GLang GLang.PaperValueDomains

-- The statement uses the original full typing judgment and original context
-- validity. There is no alternative fragment judgment or fibre certificate.
example {ε : ValCtx} {e : ValExpr} {t : ValTy}
    (h : ValHasType ε e t) (hc : ValCtxValid ε) (ρ : ValEnvSem)
    (hv : EnvironmentsRelated directOracle ε ρ ρ) :
    PartialRel (RuntimeRelated directOracle t ⟨ρ, [], []⟩ ⟨ρ, [], []⟩)
      (denotValB_semS directOracle ρ [] [] e) (denotValB_semS directOracle ρ [] [] e) :=
  originalExpr_related_family h hc (fun _ : Unit => ρ) (fun _ _ => hv) () ()

-- Formation yields full actual-runtime-fibre coherence, including dependent
-- arrows; callers do not supply coherence of the declared types.
example {ε : ValCtx} {t : ValTy} {k : ValKind} (h : ValTValid ε t k)
    (hc : ValCtxValid ε) {I : Type} (ρ : I → ValEnvSem)
    (hv : ∀ i j, EnvironmentsRelated directOracle ε (ρ i) (ρ j)) (i j : I) :
    RawTypeCoherent directOracle t ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩ :=
  originalType_coherent_family h hc ρ hv i j

open Lean Elab Command
elab "check_original_family_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``originalExpr_result_family, ``originalExpr_related_family,
      ``originalType_coherent_family, ``originalSpace_coherent_family,
      ``rawMatchedContext_of_valid_family] do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected proved original-judgment theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected original-family assumption in {n}: {ax}"
  logInfo "Full original dependent family correspondence uses only foundations and the existing GSVD existence axiom."
check_original_family_axioms
