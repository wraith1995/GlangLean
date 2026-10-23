import GLang.Proofs.Adequacy.Raw.Context.RawTypedConsistent
import GLang.Proofs.Adequacy.Raw.RawTypeAdequacy

/-!
# Exact-basis type adequacy over `RawConsistent`

This module specializes the consistency-independent `rawMTyAt_holds` theorem
to the current raw telescope.  The space conclusion remains an explicit
mutual-proof input; no independent oracle or axiom is introduced for it.
-/

namespace GLang

/-- Exact-basis type adequacy specialized to the current raw telescope. -/
theorem rawMTyAt_holds_rawConsistent
    {orc : FFSOracleSem}
    (hspec : RawAdequacyOracleSpec orc)
    (hspace : RawSpaceClaim orc (RawTypedConsistent orc)) :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {b : Basis} {τv : ValTy},
      S.TyAt Γ Ψ b τv →
        RawMTyAt orc (RawTypedConsistent orc) Γ Ψ b τv :=
  rawMTyAt_holds
    (RawTypedConsistent.worldExtendNLAt
      hspec.toOracleSpec.fvIrrel)
    (fun hc => hc.evalCtxLc)
    hspec.rawBinderCoherent
    hspace

end GLang
