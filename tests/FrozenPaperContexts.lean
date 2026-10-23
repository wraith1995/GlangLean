import GLang.Paper

open GLang
open GLang.PaperContextResults

-- No source-formation assumption is necessary in addition to indexed formation.
example (hc : Operational.ContextHistory Δ ε Γv Ψ) : InductiveCtxWF Δ ε :=
  sourceContext hc

example (he : Entry Ψ x b v) (hc : RuntimeValue.ValCtxValid Γv)
    (hv : RuntimeValue.ValHasType Γv v (ValExpr.inferType v)) :
    V2.EvalEntryCreation Ψ x b v := he.creation hc hv

-- Inference-space compatibility is obtained from typing, even for a dependent
-- function result; the caller does not identify a function with a base space.
example (hv : RuntimeValue.ValHasType Γv v (.piTy d c)) :
    ValExpr.InferSpaceMatchesBase v (.piTy d c) := inferSpaceMatchesBase hv

example (hv : RuntimeValue.ValHasType Γv v (.space s)) :
    ValExpr.inferSpaceCtx [] v = s := (inferSpaceMatchesBase hv).spaceEq

-- A dependent first binding is supported without restricting frames to spaces.
example (hc : Adequacy.PartialDirect.Consistent Δ ε Ψ Γv σ ρ)
    (hx : V2.SourceEntryValid Δ ε x) (hb : Basis.BasisValid ε b)
    (he : Entry Ψ x b v)
    (hk : RuntimeValue.ValTValid Γv (ValExpr.inferType v) k)
    (hv : RuntimeValue.ValHasType (Finmap.insert x (ValExpr.inferType v) Γv)
      v (ValExpr.inferType v))
    (hσ : EnvWF (σ.bind x a) Δ (Finmap.insert x (Basis.tof b) ε))
    (hρ : RuntimeValue.PartialEnvWF PartialDirectOracle.oracle
      (Finmap.insert x (ValExpr.inferType v) Γv) (ρ.update x w))
    (hnr : x ∉ ValExpr.fv v ∨ v = .var x (ValExpr.inferType v))
    (hden : denotValB_partial PartialDirectOracle.oracle ρ [] [] v = .ok w)
    (hagree : PartialAdequacy.Agree PartialDirectOracle.oracle σ ρ [] [] []
      (Basis.tof b) (ValExpr.inferType v) (denotBasis σ b) a w)
    (hdims : PartialAdequacy.DimsAt PartialDirectOracle.oracle σ ρ [] [] []
      (Basis.tof b) (ValExpr.inferType v) (denotBasis σ b)) :
    Adequacy.PartialDirect.Consistent Δ (Finmap.insert x (Basis.tof b) ε)
      (Ψ.extend x b v) (Finmap.insert x (ValExpr.inferType v) Γv)
      (σ.bind x a) (ρ.update x w) :=
  consistentNonlinear hc hx hb he hk hv hσ hρ hnr hden hagree hdims

-- A representation may differ from the canonical value-variable type. There
-- is no equality between that type and inferType v in the constructor contract.
example (hc : Adequacy.PartialDirect.Consistent Δ ε Ψ Γv σ ρ)
    (hσ : EnvWF σ Δ ε)
    (hx : V2.SourceEntryLinked Δ ε x b) (hkey : (x,b) ∉ Ψ)
    (ha : σ.vars.lookup x = some a) (hb : Basis.BasisValid ε b)
    (he : Entry Ψ x b v)
    (hv : RuntimeValue.ValHasType Γv v (ValExpr.inferType v))
    (hden : denotValB_partial PartialDirectOracle.oracle ρ [] [] v = .ok w)
    (hagree : PartialAdequacy.Agree PartialDirectOracle.oracle σ ρ [] [] []
      (Basis.tof b) (ValExpr.inferType v) (denotBasis σ b) a w)
    (hdims : PartialAdequacy.DimsAt PartialDirectOracle.oracle σ ρ [] [] []
      (Basis.tof b) (ValExpr.inferType v) (denotBasis σ b)) :
    Operational.ContextHistory Δ ε Γv (Ψ.extend x b v) ∧
      RuntimeValue.PartialEnvWF PartialDirectOracle.oracle Γv ρ := by
  have h := consistentRepresentation hc hσ hx hkey ha hb he hv hden hagree hdims
  exact ⟨h.context, h.valueEnv⟩

-- The empty case permits arbitrary values at undeclared names.
example (ρ : ValEnvSem) : Adequacy.PartialDirect.Consistent ∅ ∅ ∅ ∅ ⟨∅⟩ ρ :=
  PartialAdequacy.Consistent.empty _ ρ

open Lean Elab Command in
elab "check_frozen_context_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``inferSpaceMatchesBase, ``Entry.creation, ``entry_of_creation,
      ``sourceContext, ``contextNonlinear, ``contextLinear, ``contextRepresentation,
      ``consistentNonlinear, ``consistentLinear, ``consistentRepresentation] do
    for ax in ← Lean.collectAxioms decl do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo "Frozen-paper context constructors: foundations only."

check_frozen_context_axioms
