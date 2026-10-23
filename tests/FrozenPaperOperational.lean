import GLang.Paper
import GLang.Proofs.Preservation.OperationalKindPreservation

/-! Audit the semantic justification of the frozen operational presentation. -/
namespace GLang.FrozenPaperOperational

theorem checkedTermFacts (h : Operational.Term Δ ε Ψ t b v Tv) :
    Nonempty (HasType Δ ε t (Basis.tof b)) ∧ Basis.BasisValid ε b ∧
      Operational.TyAt ε Ψ b Tv ∧ Operational.Unchecked.OpStep Ψ t b v ∧
      Operational.Unchecked.EvalT Ψ (Basis.tof b) Tv :=
  ⟨h.hasType, h.basisValid, h.tyAt, Operational.Term.toUnchecked h,
    Operational.Term.toUncheckedType h⟩

example (h : Operational.Space ε Ψ s sv) :
    Operational.Unchecked.EvalS Ψ s sv := Operational.Space.toUnchecked h
example (h : Operational.Ty ε Ψ T Tv) :
    Operational.Unchecked.EvalT Ψ T Tv := Operational.Ty.toUnchecked h
example (h : Operational.TyAt ε Ψ b Tv) :
    Operational.Unchecked.EvalT Ψ (Basis.tof b) Tv := Operational.TyAt.toUnchecked h
example (h : Operational.Cob ε Ψ b₀ v b₁) :
    Operational.Unchecked.EvalBB Ψ b₀ v b₁ := Operational.Cob.toUnchecked h

-- The function-shaped premise added by the application display follows from
-- context formation alone. No equality between coordinate representations is
-- needed. The native call result is C[v₂/x], before the final conversion.
theorem applicationExpansion (hc : Operational.ContextHistory Δ ε Γv Ψ)
    (hf : Operational.Unchecked.OpStep Ψ f (.frame b₀ b₁) vf)
    (va : ValExpr) (out : ValTy) :
    ∃ D C, ValExpr.inferType vf = .piTy D C ∧
      let v₂ := ValExpr.reshap va D (ValExpr.inferType va)
      ValExpr.applyAt vf va out =
        .reshap (.appV vf v₂) out (ValTy.applyCodomain v₂ C) := by
  have hk := RuntimeValue.operational_kind_of_context hf hc.erase.evalCtxValidPlus
  cases he : ValExpr.inferType vf with
  | space s => simp [he, ValTy.structuralKind, Basis.tof, Ty.sourceKind] at hk
  | piTy D C =>
    refine ⟨D, C, rfl, ?_⟩
    simp only [ValExpr.applyAt, ValExpr.applyValue, he, ValTy.domain,
      ValExpr.inferType_appV]

-- The tensor specialization in EB-ImageSvds follows from the actual space
-- premise. Expanding imageCoords then gives precisely the displayed products.
theorem imageExpansion (h : ValSpace.EvalS Ψ (.tprod (.dual s₀) s₁) sv)
    (v : ValExpr) :
    ∃ sv₀ sv₁, sv = .tprod sv₀ sv₁ ∧
      let M := ValExpr.reshapBase v sv
      ValExpr.imageCoords sv v =
        .mtm 0 0 sv₁ sv₁ (.gsvdV M (.idelta sv₀) (.idelta sv₁))
          (.mtm 0 0 sv₀ sv₀ M
            (.vtrans (.gsvdU M (.idelta sv₀) (.idelta sv₁)))) := by
  obtain ⟨sv₀, sv₁, rfl⟩ := evalS_tprod_inv h
  exact ⟨sv₀, sv₁, rfl, rfl⟩

-- Matrix compatibility specifies separate endpoint bases, not just the
-- overall tensor type. A term-sequence basis has that type but not that form.
example : Basis.tof (.terms (.tprod (.dual .real) .real)
    [.zero (.tprod (.dual .real) .real)] (.tprod (.dual .one) .one)) =
      Basis.tof (.tprod (.dual .one) .one) := rfl
example : ¬ Basis.FFSMatrixCompatible (.terms (.tprod (.dual .real) .real)
    [.zero (.tprod (.dual .real) .real)] (.tprod (.dual .one) .one)) := by
  rintro ⟨b₀, b₁, h⟩
  cases h

-- The empty assembly family uses the empty source space, while retaining a
-- tensor-shaped zero-dimensional target. This is the display's case split.
example (sv : ValSpace) : ValExpr.sumAt .empty [] (.tprod .empty sv) =
    .reshap (.vsum .empty []) (.space (.tprod .empty sv)) (.space .empty) := rfl

-- Without context formation a raw lookup can be a scalar at a frame. This
-- shows why the presentation's inferred-function premise is contextual, not
-- an identity about arbitrary raw syntax or arbitrary evaluation stores.
example : ValExpr.OpStep ((∅ : EvalCtx).extend "f" (.frame .one .one) (.rlit 0))
    (.var "f") (.frame .one .one) (.rlit 0) :=
  .var (by simp [EvalCtx.lookup, EvalCtx.extend])
example : ¬ ∃ D C, ValExpr.inferType (.rlit 0) = .piTy D C := by
  rintro ⟨D, C, h⟩
  cases h

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``checkedTermFacts, ``applicationExpansion, ``imageExpansion,
      ``Operational.Space.toUnchecked, ``Operational.Ty.toUnchecked,
      ``Operational.TyAt.toUnchecked, ``Operational.Cob.toUnchecked,
      ``Operational.Term.toUnchecked, ``Operational.Term.toUncheckedType] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected operational correspondence axiom in {n}: {ax}"
  logInfo "Literal erasure and the two operational display specializations: foundations only."

end GLang.FrozenPaperOperational
