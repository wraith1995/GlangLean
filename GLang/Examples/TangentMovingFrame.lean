import GLang.Examples.TangentProjectedArea

namespace GLang.Examples.TangentCoordinates

open Examples.Paper (R2 R3 svR2 svR3)

abbrev pointBasis : Basis := .dsum .one .one
abbrev ambientBasis : Basis := .dsum pointBasis .one
abbrev pointSV : ValSpace := .dsum .real .real
abbrev ambientSV : ValSpace := .dsum pointSV .real
abbrev parameterBasis : Basis := .tprod (.dual pointBasis) ambientBasis
abbrev parameterSV : ValSpace := .tprod pointSV ambientSV

/-- `T = Image(f)` at one opened point. -/
def tangentSpace (f : Term) : Space := .img R2 R3 f

def tangentBasis (f : Term) : Basis :=
  .image (.proj (.coker R2 R3 f) pointBasis ambientBasis)

/-- Independently canonical orthonormal image basis, used only as fallback. -/
def tangentStandard (f : Term) : Basis :=
  .proj (tangentSpace f) pointBasis ambientBasis

/-- The parameterization occurs in the dimension annotation. -/
def tangentSV (fv : ValExpr) : ValSpace :=
  .ffs .image parameterSV (.reshap fv (.space parameterSV) (.space parameterSV))

/-- Exact image-of-cokernel to canonical-image conversion. -/
def tangentBasisChangeCode (fv : ValExpr) : ValExpr :=
  .reshap (.imageCoords parameterSV fv)
    (.space (.tprod
      (.ffs .cokernel parameterSV (.reshap fv (.space parameterSV) (.space parameterSV)))
      (tangentSV fv)))
    (.space (ValExpr.inferSpaceCtx [] (.imageCoords parameterSV fv)))

/-- Conversion of moving coordinates to fallback coordinates, with checks. -/
def tangentCoordinatesInStandard (fv v : ValExpr) : ValExpr :=
  let s := tangentSV fv
  .ttv s (.reshapBase (tangentBasisChangeCode fv) (.tprod s s)) (.reshapBase v s)

theorem tangentBasis_valid {Γ : NLCtx} {f : Term}
    (hf : HasType ∅ Γ f (.space (.tprod (.dual R2) R3))) :
    Basis.BasisValid Γ (tangentBasis f) :=
  .image (.proj_coker (.dsum .one .one rfl rfl)
    (.dsum (.dsum .one .one rfl rfl) .one rfl rfl) rfl rfl ⟨hf⟩) rfl ⟨hf⟩

theorem tangentStandard_valid {Γ : NLCtx} {f : Term}
    (hf : HasType ∅ Γ f (.space (.tprod (.dual R2) R3))) :
    Basis.BasisValid Γ (tangentStandard f) :=
  .proj_img (.dsum .one .one rfl rfl)
    (.dsum (.dsum .one .one rfl rfl) .one rfl rfl) rfl rfl ⟨hf⟩

theorem tangentSpace_eval {Ψ : EvalCtx} {f : Term} {fv : ValExpr}
    (hf : ValExpr.OpStep Ψ f parameterBasis fv) :
    ValSpace.EvalS Ψ (tangentSpace f) (tangentSV fv) :=
  .img hf rfl ⟨pointBasis, ambientBasis, rfl⟩
    (.tprod (.dual (.dsum .real .real)) (.dsum (.dsum .real .real) .real))

/-- This conversion is constructed by the actual image-basis rule. -/
theorem tangentBasis_cob {Ψ : EvalCtx} {f : Term} {fv : ValExpr}
    (hf : ValExpr.OpStep Ψ f parameterBasis fv) :
    Basis.EvalBB Ψ (tangentBasis f) (tangentBasisChangeCode fv) (tangentStandard f) :=
  .image_svds rfl rfl ⟨trivial, trivial⟩ ⟨⟨trivial, trivial⟩, trivial⟩ hf
    (.tprod (.dual (.dsum .real .real)) (.dsum (.dsum .real .real) .real))

theorem tangentCoordinates_op {Ψ : EvalCtx} {f e : Term} {fv v : ValExpr}
    (hf : ValExpr.OpStep Ψ f parameterBasis fv)
    (he : ValExpr.OpStep Ψ e (tangentBasis f) v) :
    ValExpr.OpStep Ψ e (tangentStandard f) (tangentCoordinatesInStandard fv v) :=
  .cob rfl rfl he (tangentBasis_cob hf) (tangentSpace_eval hf)

/-- Dual evaluation at a moving image basis. Its output contains `fv` only
inside `tangentSV fv`, never as an arithmetic operand or Gram matrix. -/
theorem tangentDualEval_op {Γ : NLCtx} {Ψ : EvalCtx} {f : Term} {fv : ValExpr}
    (hft : HasType ∅ Γ f (.space (.tprod (.dual R2) R3)))
    (hf : ValExpr.OpStep Ψ f parameterBasis fv) :
    ValExpr.OpStep Ψ (dualEval (tangentSpace f)) (dualEvalBasis (tangentBasis f))
      (dualEvalCode (tangentSV fv)) :=
  dualEval_op (b := tangentBasis f) rfl (SValid.lc (.img svR2 svR3 hft)) (tangentSpace_eval hf)

/-- Full measured area, starting from moving-frame coordinate entries.
`u₀,u₁` have coordinate deltas 0 and 1; `v,w` have the caller's coordinate
arrays. A rank-two/injectivity semantic assumption is needed to interpret the
first two deltas as a complete tangent basis. The derivation itself also
covers rank-deficient inputs and retains runtime dimension checks. -/
theorem tangentMeasuredArea_op {Γ : NLCtx} {Ψ : EvalCtx} {f : Term} {fv vv wv : ValExpr}
    {u₀ u₁ v w : Name}
    (hft : HasType ∅ Γ f (.space (.tprod (.dual R2) R3)))
    (hf : ValExpr.OpStep Ψ f parameterBasis fv)
    (hu₀ : Ψ.lookup (u₀, tangentBasis f) = some (.delta 0 (tangentSV fv)))
    (hu₁ : Ψ.lookup (u₁, tangentBasis f) = some (.delta 1 (tangentSV fv)))
    (hv : Ψ.lookup (v, tangentBasis f) = some vv)
    (hw : Ψ.lookup (w, tangentBasis f) = some wv) :
    ValExpr.OpStep Ψ (projectedArea (tangentSpace f) (.var v) (.var w))
      (projectedAreaBasis (tangentStandard f) (.var u₀) (.var u₁))
      (measuredAreaCode (tangentSV fv)
        (tangentCoordinatesInStandard fv (.delta 0 (tangentSV fv)))
        (tangentCoordinatesInStandard fv (.delta 1 (tangentSV fv)))
        (tangentCoordinatesInStandard fv vv) (tangentCoordinatesInStandard fv wv)) :=
  measuredArea_op (b := tangentStandard f) rfl (SValid.lc (.img svR2 svR3 hft))
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩ (tangentSpace_eval hf)
    (tangentCoordinates_op hf (.var hu₀)) (tangentCoordinates_op hf (.var hu₁))
    (tangentCoordinates_op hf (.var hv)) (tangentCoordinates_op hf (.var hw))

/-- Source typing and requested-basis validity for the intended nonlinear
coordinate-entry setup. These facts are separate from evaluator lookups;
lookups alone do not certify environment consistency. -/
theorem tangentMeasuredArea_wellFormed {Γ : NLCtx} {f : Term} {u₀ u₁ v w : Name}
    (hft : HasType ∅ Γ f (.space (.tprod (.dual R2) R3)))
    (hu₀ : Γ.lookup u₀ = some (.space (tangentSpace f)))
    (hu₁ : Γ.lookup u₁ = some (.space (tangentSpace f)))
    (hv : Γ.lookup v = some (.space (tangentSpace f)))
    (hw : Γ.lookup w = some (.space (tangentSpace f))) :
    Nonempty (HasType ∅ Γ (projectedArea (tangentSpace f) (.var v) (.var w))
      (.space (areaSpace (tangentSpace f)))) ∧
    Basis.BasisValid Γ (projectedAreaBasis (tangentStandard f) (.var u₀) (.var u₁)) :=
  ⟨⟨Examples.Paper.castΔ
      (projectedArea_hasType (.img svR2 svR3 hft) (Finmap.disjoint_empty _)
        (.var_nlin hv) (.var_nlin hw)) Finmap.empty_union⟩,
    projectedAreaBasis_valid (tangentStandard_valid hft) rfl
      (.img svR2 svR3 hft) (.var_nlin hu₀) (.var_nlin hu₁)⟩

theorem tangentDualEval_wellFormed {Γ : NLCtx} {f : Term}
    (hft : HasType ∅ Γ f (.space (.tprod (.dual R2) R3))) :
    Nonempty (HasType ∅ Γ (dualEval (tangentSpace f))
      (.space (.tprod (.dual (.dual (tangentSpace f))) (.dual (tangentSpace f))))) ∧
    Basis.BasisValid Γ (dualEvalBasis (tangentBasis f)) :=
  ⟨⟨dualEval_hasType (.img svR2 svR3 hft)⟩,
    dualEvalBasis_valid (tangentBasis_valid hft) rfl⟩

end GLang.Examples.TangentCoordinates
