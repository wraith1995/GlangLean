import GLang.Proofs.Progress.Supporting.ProgressTele
import GLang.Proofs.Value.Binding.ValueWeaken
import GLang.Proofs.Value.Soundness.ValueSoundVals
import GLang.Proofs.Value.Runtime.RuntimeValueFormation

/-! Value-context-indexed operational context formation. The stored expression
at each basis is typed at its own inferred type. Additional representations do
not change the canonical value-variable context. -/
namespace GLang.Operational

inductive TypedContext : LCtx → NLCtx → ValCtx → EvalCtx → Prop
  | empty : TypedContext ∅ ∅ ∅ ∅
  | extend_nlin {Δ Γ Γv Ψ x b v k} :
      TypedContext Δ Γ Γv Ψ →
      V2.SourceEntryValid Δ Γ x →
      V2.EvalEntryCreation Ψ x b v →
      Basis.BasisValid Γ b →
      Nonempty (RuntimeValue.ValTValid Γv (ValExpr.inferType v) k) →
      Nonempty (RuntimeValue.ValHasType (Finmap.insert x (ValExpr.inferType v) Γv)
        v (ValExpr.inferType v)) →
      TypedContext Δ (Finmap.insert x (Basis.tof b) Γ)
        (Finmap.insert x (ValExpr.inferType v) Γv) (EvalCtx.extend Ψ x b v)
  | extend_lin {Δ Γ Γv Ψ x b v s k} :
      TypedContext Δ Γ Γv Ψ →
      V2.SourceEntryValid Δ Γ x →
      V2.EvalEntryCreation Ψ x b v →
      Basis.BasisValid Γ b →
      Basis.tof b = .space s →
      Nonempty (RuntimeValue.ValTValid Γv (ValExpr.inferType v) k) →
      Nonempty (RuntimeValue.ValHasType (Finmap.insert x (ValExpr.inferType v) Γv)
        v (ValExpr.inferType v)) →
      TypedContext (Finmap.insert x s Δ) Γ
        (Finmap.insert x (ValExpr.inferType v) Γv) (EvalCtx.extend Ψ x b v)
  | extend_rep {Δ Γ Γv Ψ x b v} :
      TypedContext Δ Γ Γv Ψ →
      V2.SourceEntryLinked Δ Γ x b →
      (x, b) ∉ Ψ →
      V2.EvalEntryCreation Ψ x b v →
      Basis.BasisValid Γ b →
      Nonempty (RuntimeValue.ValHasType Γv v (ValExpr.inferType v)) →
      TypedContext Δ Γ Γv (EvalCtx.extend Ψ x b v)

end GLang.Operational
