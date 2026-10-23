import GLang.Proofs.Value.Presentation.PaperValueTypedCorrespondence
open GLang GLang.PaperValueDomains

-- An original value rule at an arbitrary (including FFS-dependent) space.
-- The only numerical premise concerns this rule's actual space annotation.
example {ε : ValCtx} {s : ValSpace} (hs : ValSValid ε s) (w w' : World)
    (hΓ : w.types = w'.types)
    (hq : SpaceOracleAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) s) :
    PartialRel (RuntimeRelated directOracle (.space s) w w')
      (denotValB_semS directOracle w.env w.types w.values (.zero s))
      (denotValB_semS directOracle w'.env w'.types w'.values (.zero s)) := by
  apply original_numeric_step (.zero hs) (by trivial) w w' hΓ
  · intro q h
    simp [primitiveQuerySpaces, primitiveInputSpaces, ValExpr.inferSpaceCtx] at h
    subst q
    exact hq
  · simp [primitiveOperands]

example (ρ : ValEnvSem) (x : VName) (τ : ValTy) (v : ValValSem)
    (hτ : ValTy.lc τ) (hxτ : x ∉ ValTy.fv τ) :
    denotValB_semS directOracle (ρ.update x v) [] [] (ValExpr.openVar x τ (.bvar 0)) =
      denotValB_semS directOracle ρ [τ] [v] (.bvar 0) :=
  original_eval_openVar ρ x τ v (.bvar 0) hτ hxτ (by simp [ValExpr.fv])

open Lean Elab Command
elab "check_original_correspondence_steps_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``original_eval_openVar, ``original_numeric_step,
      ``original_numeric_step_of_typingIH, ``original_application_step] do
    unless (← getConstInfo n) matches .thmInfo _ do
      throwError "Expected theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected axiom in original correspondence step {n}: {ax}"
  logInfo "Original correspondence steps: foundations plus existing GSVD existence only."
check_original_correspondence_steps_axioms
