import GLang.Proofs.Adequacy.Partial.Source.PartialSourceTransport
import GLang.Proofs.Adequacy.Raw.Context.RawConsistent
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceWorld
import GLang.Proofs.Value.Partial.PartialValueRuntimeRelation
import GLang.Proofs.Preservation.Context
import GLang.Proofs.Value.Runtime.RuntimeValueCorrespondence

/-! Inductive semantic bindings and indexed environment consistency. -/
namespace GLang.PartialAdequacy
open Basis (BasisValid)

/-- Consistency of the source, evaluator, compiled-type, and denotational
environments using exact raw agreement. -/
inductive History (orc : PartialFFSOracleSem) :
    LCtx -> NLCtx -> EvalCtx -> ValCtx -> DEnv -> ValEnvSem -> Prop
  | empty {rho : ValEnvSem} : History orc ∅ ∅ ∅ ∅ ⟨∅⟩ rho
  | extend_lin {Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV}
      (h : History orc Delta Gamma Psi GammaV sigma rho)
      (hx : x ∉ Delta /\ x ∉ Gamma)
      (htof : Basis.tof b = .space s)
      (hb : BasisValid Gamma b)
      (hTy : ValTy.EvalT Psi (Basis.tof b) tauV)
      (hinfer : ValExpr.inferType v = tauV)
      (hinferSpaceBase : ValExpr.InferSpaceMatchesBase v tauV)
      (hfvv : ValExpr.fv v ⊆ (Psi.extend x b v).keyNames)
      (hlc : ValExpr.lc v)
      (hnr : x ∉ ValExpr.fv v \/ exists tau, v = .var x tau)
      (hxs : xs.matchesShape (denotTy sigma (Basis.tof b)))
      (hden : denotValB_partial orc rho [] [] v = .ok yV)
      (hagree : Agree orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b) xs yV)
      (hdims : DimsAt orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b)) :
      History orc (Finmap.insert x s Delta) Gamma
        (Psi.extend x b v) (Finmap.insert x tauV GammaV)
        (sigma.bind x xs) (rho.update x yV)
  | extend_nl {Delta Gamma Psi GammaV sigma rho x b v tauV xs yV}
      (h : History orc Delta Gamma Psi GammaV sigma rho)
      (hx : x ∉ Delta /\ x ∉ Gamma)
      (hb : BasisValid Gamma b)
      (hTy : ValTy.EvalT Psi (Basis.tof b) tauV)
      (hinfer : ValExpr.inferType v = tauV)
      (hinferSpaceBase : ValExpr.InferSpaceMatchesBase v tauV)
      (hfvv : ValExpr.fv v ⊆ (Psi.extend x b v).keyNames)
      (hlc : ValExpr.lc v)
      (hnr : x ∉ ValExpr.fv v \/ exists tau, v = .var x tau)
      (hxs : xs.matchesShape (denotTy sigma (Basis.tof b)))
      (hden : denotValB_partial orc rho [] [] v = .ok yV)
      (hagree : Agree orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b) xs yV)
      (hdims : DimsAt orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b))
      (hcreation : V2.EvalEntryCreation Psi x b v) :
      History orc Delta (Finmap.insert x (Basis.tof b) Gamma)
        (Psi.extend x b v) (Finmap.insert x tauV GammaV)
        (sigma.bind x xs) (rho.update x yV)
  /-- Add another evaluator representation of an existing source binding. -/
  | extend_rep {Delta Gamma Psi GammaV sigma rho x b v tauV xs yV}
      (h : History orc Delta Gamma Psi GammaV sigma rho)
      (hkey : (x, b) ∉ Psi)
      (hsource : V2.SourceEntryLinked Delta Gamma x b)
      (hsigma : sigma.vars.lookup x = some xs)
      (hb : BasisValid Gamma b)
      (hTy : ValTy.EvalT Psi (Basis.tof b) tauV)
      (hinfer : ValExpr.inferType v = tauV)
      (hinferSpaceBase : ValExpr.InferSpaceMatchesBase v tauV)
      (hfvv : ValExpr.fv v ⊆ (Psi.extend x b v).keyNames)
      (hlc : ValExpr.lc v)
      (hxs : xs.matchesShape (denotTy sigma (Basis.tof b)))
      (hden : denotValB_partial orc rho [] [] v = .ok yV)
      (hagree : Agree orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b) xs yV)
      (hdims : DimsAt orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b))
      (hcreation : V2.EvalEntryCreation Psi x b v) :
      History orc Delta Gamma (Psi.extend x b v) GammaV sigma rho

/-- Canonical environment consistency. -/
abbrev RawHistory := History

/-- Public semantic consistency includes membership of the runtime environment
in the recursive value domain. Original typing of stored expressions remains
a separate property; it is not implied by this environment condition. -/
structure Consistent (orc : PartialFFSOracleSem)
    (Δ : LCtx) (Γ : NLCtx) (Ψ : EvalCtx) (ε : ValCtx)
    (σ : DEnv) (ρ : ValEnvSem) : Prop where
  history : History orc Δ Γ Ψ ε σ ρ
  context : Operational.TypedContext Δ Γ ε Ψ
  valueEnv : RuntimeValue.PartialEnvWF orc ε ρ

end GLang.PartialAdequacy
