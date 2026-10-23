import GLang.Proofs.Preservation.OperationalKindPreservation
import GLang.Proofs.Value.Runtime.RuntimeValueInfer

namespace GLang.OperationalNestedKindGapTest

abbrev badBasis : Basis := .frame .one .one
abbrev matrixSpace : Space := .tprod (.dual .real) .empty
abbrev matrixValueSpace : ValSpace := .tprod .real .empty
abbrev badSource : Term := .appL .real .empty (.zero matrixSpace) (.real 0)
abbrev badValue : ValExpr := .reshapBase (.ttv .real (.zero matrixValueSpace) (.rlit 0)) .empty
abbrev outerSource : Term :=
  .appL .empty .real (.zero (.tprod (.dual .empty) .real)) badSource

noncomputable def sourceTyped : HasType ∅ ∅ outerSource (.space .real) := by
  have hin : HasType ∅ ∅ badSource (.space .empty) := by
    simpa using HasType.app_linear SValid.real SValid.empty (Finmap.disjoint_empty (∅ : LCtx))
      (HasType.zero (SValid.tprod (SValid.dual SValid.real) SValid.empty)) (HasType.real_lit 0)
  simpa using HasType.app_linear SValid.empty SValid.real (Finmap.disjoint_empty (∅ : LCtx))
    (HasType.zero (SValid.tprod (SValid.dual SValid.empty) SValid.real)) hin

example {Ψ : EvalCtx} (hc : V2.EvalCtxValidPlus Ψ) :
    ¬ ValExpr.OpStep Ψ badSource badBasis badValue := by
  intro h
  have impossible := RuntimeValue.operational_kind_of_context h hc
  cases impossible

-- Higher-order output frames cannot be used for the same array output either.
example {Ψ : EvalCtx} (hc : V2.EvalCtxValidPlus Ψ) :
    ¬ ValExpr.OpStep Ψ badSource (.frame .one badBasis) badValue := by
  intro h
  have impossible := RuntimeValue.operational_kind_of_context h hc
  cases impossible

example : Basis.BasisValid ∅ (.one : Basis) := .one

example {Γv : ValCtx} {a : ValExpr} {τ : ValTy} :
    ¬ Nonempty (RuntimeValue.ValHasType Γv (.appV badValue a) τ) := by
  rintro ⟨h⟩
  cases h with
  | appV hf _ _ _ => cases hf

end GLang.OperationalNestedKindGapTest
