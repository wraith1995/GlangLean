import GLang.Artifact
import Lean
import GLang.Proofs.Preservation.OperationalTypedContextSoundness
import Lean.Util.CollectAxioms

open GLang

-- The result is the caller's literal unchecked expression, in the same Γv.
example (hc : Operational.ContextHistory Δ Γ Γv Ψ)
    (ht : HasType Δ Γ e (Basis.tof b)) (hb : Basis.BasisValid Γ b)
    (he : Operational.Unchecked.OpStep Ψ e b v) :
    Nonempty (RuntimeValue.ValHasType Γv v (ValExpr.inferType v)) := by
  obtain ⟨_,_,_,_,_,hv⟩ := Metatheory.preservation hc ht hb he
  exact hv

-- Every realized type is formed in that same context, including dependent types.
example (hc : Operational.ContextHistory Δ Γ Γv Ψ)
    (he : ValTy.EvalT Ψ t tv) :
    Nonempty (RuntimeValue.ValTValid Γv tv tv.structuralKind) :=
  RuntimeValue.preservation_mutual.2.1 he Γv hc.evalContext

-- Preservation composes directly with the full recursive value-domain theorem.
example (hc : Operational.ContextHistory Δ Γ Γv Ψ)
    (he : Operational.Unchecked.OpStep Ψ e b v)
    (henv : RuntimeValue.PartialEnvWF PartialDirectOracle.oracle Γv ρ) :
    PaperValueDomains.PartialRel
      (PartialValueDomains.WorldRuntimeRelated PartialDirectOracle.oracle
        (ValExpr.inferType v) ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle ρ [] [] v)
      (denotValB_partial PartialDirectOracle.oracle ρ [] [] v) :=
  hc.result_sound he ρ henv.2

-- A malformed stored scalar multiplier cannot satisfy indexed formation.
example (hc : Operational.ContextHistory Δ Γ Γv Ψ)
    (hl : EvalCtx.lookup Ψ (x,b) =
      some (.scale (.zero (.tprod .real .real)) (.rlit 0))) : False := by
  obtain ⟨h⟩ := hc.lookup_typed hl
  cases h with
  | scale bad _ => cases bad

example (he : ValHasType Γv e τ) : RuntimeValue.ValHasType Γv e τ := he.runtime

open Lean Elab Command in
elab "check_indexed_preservation_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``RuntimeValue.preservation_mutual, ``RuntimeValue.partialValueDomainSoundness,
      ``Operational.TypedContext.result_sound, ``Metatheory.preservation,
      ``PaperOperationalResults.preservationWithKinding,
      ``Metatheory.checkedProgressAdequacy] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "Unexpected axiom in indexed preservation: {name}: {ax}"
  logInfo "Indexed preservation, recursive value soundness, and public adequacy: foundations only."
check_indexed_preservation_axioms
