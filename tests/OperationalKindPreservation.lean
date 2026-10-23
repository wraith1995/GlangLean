import GLang.Proofs.Preservation.OperationalKindPreservation

namespace GLang.OperationalKindPreservationTest

private abbrev badBasis : Basis := .frame .one .one
private abbrev matrixSpace : Space := .tprod (.dual .real) .empty
private abbrev matrixValueSpace : ValSpace := .tprod .real .empty
private abbrev badSource : Term :=
  .appL .real .empty (.zero matrixSpace) (.real 0)
private abbrev badValue : ValExpr :=
  .reshapBase (.ttv .real (.zero matrixValueSpace) (.rlit 0)) .empty

private theorem emptyRegular : V2.EvalCtxValidPlus ∅ := by
  intro x b v h
  simp [EvalCtx.lookup] at h

example : ¬ ValExpr.OpStep ∅ badSource badBasis badValue := by
  intro h
  have impossible := RuntimeValue.operational_kind_of_context h emptyRegular
  cases impossible

example {Ψ e b v} (h : ValExpr.OpStep Ψ e b v)
    (hc : V2.EvalCtxValidPlus Ψ) :
    (ValExpr.inferType v).structuralKind = (Basis.tof b).sourceKind :=
  RuntimeValue.operational_kind_of_context h hc

-- The source-aligned theorem recovers both component kinds at a frame.
example {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {e : Term}
    {b₀ b₁ : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ e (.frame b₀ b₁) v) (hc : V2.EvalCtxValidPlus Ψ)
    (ht : HasType Δ Γ e (Basis.tof (.frame b₀ b₁)))
    (hb : Basis.BasisValid Γ (.frame b₀ b₁)) :
    ∃ d c, ValExpr.inferType v = .piTy d c ∧
      d.structuralKind = (Basis.tof b₀).sourceKind ∧
      c.structuralKind = (Basis.tof b₁).sourceKind :=
  RuntimeValue.operational_frame_type h hc ht hb

#print axioms RuntimeValue.operational_kind_of_context
#print axioms RuntimeValue.operational_kind
#print axioms RuntimeValue.operational_frame_type

end GLang.OperationalKindPreservationTest
