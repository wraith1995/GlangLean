import GLang.Proofs.Preservation.IndexedPreservationHelpers
import GLang.Proofs.Preservation.OperationalKindPreservation

/-! Application-kind properties of ordinary evaluation. -/
namespace GLang.RuntimeValue

/-- Source forms for the application-kind analysis. -/
def linearResultSpine : Term → Prop
  | .appL .. => True
  | .smul _ e => linearResultSpine e
  | _ => False

theorem operational_kind_or_linearResultSpine
    {Ψ : EvalCtx} {e : Term} {b : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ e b v) :
    V2.EvalCtxValidPlus Ψ →
      (ValExpr.inferType v).structuralKind = (Basis.tof b).sourceKind ∨
      linearResultSpine e :=
  fun hc => Or.inl (operational_kind_of_context h hc)

end GLang.RuntimeValue
