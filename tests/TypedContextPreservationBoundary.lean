import GLang.Metatheory
import GLang.Proofs.Preservation.Context

namespace GLang.TypedContextPreservationBoundary
open RawCertifiedOperational

abbrev matS : Space := .tprod (.dual .real) .real
abbrev matV : ValSpace := .tprod .real .real
abbrev matB : Basis := .tprod (.dual .one) .one
abbrev src : Term := .zero matS
abbrev kerS : Space := .ker .real .real src
abbrev kerB : Basis := .proj kerS .one .one

private def matValid : SValid ∅ matS := .tprod (.dual .real) .real
private theorem matBasisValid : Basis.BasisValid ∅ matB := .tprod (.dual .one rfl) .one rfl rfl
private theorem matEval : C.Space ∅ ∅ matS matV :=
  .tprod ⟨matValid⟩ (.dual ⟨.dual .real⟩ .real) .real
private theorem matAt : C.TyAt ∅ ∅ matB (.space matV) :=
  .space rfl matBasisValid matEval
private theorem matrixZero : C.Term ∅ ∅ ∅ src matB (.zero matV) (.space matV) :=
  .zero rfl ⟨.zero matValid⟩ matBasisValid matAt matEval
private theorem matrixZeroReshaped : C.Term ∅ ∅ ∅ src matB
    (.reshap (.zero matV) (.space matV) (.space matV)) (.space matV) :=
  .reshape_cob ⟨.zero matValid⟩ matBasisValid matAt matrixZero

abbrev sv0 : ValSpace := .ffs .kernel matV (ValExpr.reshapBase (.zero matV) matV)
abbrev sv1 : ValSpace := .ffs .kernel matV
  (ValExpr.reshapBase (.reshap (.zero matV) (.space matV) (.space matV)) matV)
private def kerValid : SValid ∅ kerS := .ker .real .real (.zero matValid)
private theorem kerBasisValid : Basis.BasisValid ∅ kerB := by
  exact .proj_ker .one .one rfl rfl ⟨.zero matValid⟩
private theorem kerEval0 : C.Space ∅ ∅ kerS sv0 :=
  .ker ⟨kerValid⟩ rfl ⟨.one, .one, rfl⟩ matEval matrixZero
private theorem kerEval1 : C.Space ∅ ∅ kerS sv1 :=
  .ker ⟨kerValid⟩ rfl ⟨.one, .one, rfl⟩ matEval matrixZeroReshaped
private theorem kerAt0 : C.TyAt ∅ ∅ kerB (.space sv0) :=
  .space rfl kerBasisValid kerEval0
private theorem kerAt1 : C.TyAt ∅ ∅ kerB (.space sv1) :=
  .space rfl kerBasisValid kerEval1
private theorem zero0 : C.Term ∅ ∅ ∅ (.zero kerS) kerB (.zero sv0) (.space sv0) :=
  .zero rfl ⟨.zero kerValid⟩ kerBasisValid kerAt0 kerEval0
private theorem zero1 : C.Term ∅ ∅ ∅ (.zero kerS) kerB (.zero sv1) (.space sv1) :=
  .zero rfl ⟨.zero kerValid⟩ kerBasisValid kerAt1 kerEval1

def result : ValExpr := .vadd sv0 (.zero sv0) (.zero sv1)

theorem checkedAddition : Operational.Term ∅ ∅ ∅
    (.add (.zero kerS) (.zero kerS)) kerB result (.space sv0) :=
  .add rfl ⟨.add kerValid (.zero kerValid) (.zero kerValid)⟩ kerBasisValid kerAt0 zero0 zero1

private def matVValid (Γv : ValCtx) : ValSValid Γv matV := .tprod .real .real
private def sv0Valid (Γv : ValCtx) : ValSValid Γv sv0 :=
  .ffs .real .real
    (.reshap (.zero (matVValid Γv)) (.space (matVValid Γv)) (.space (matVValid Γv)))
private def sv1Valid (Γv : ValCtx) : ValSValid Γv sv1 :=
  .ffs .real .real
    (.reshap
      (.reshap (.zero (matVValid Γv)) (.space (matVValid Γv)) (.space (matVValid Γv)))
      (.space (matVValid Γv)) (.space (matVValid Γv)))

-- The existing operational output has a typing derivation without conversions.
def result_typed (Γv : ValCtx) : ValHasType Γv result (.space sv0) :=
  .vadd (.zero (sv0Valid Γv)) (.zero (sv1Valid Γv)) (sv0Valid Γv)

-- Explicit conversion remains admissible but is unnecessary for addition.
def repairedResult : ValExpr :=
  .vadd sv0 (.zero sv0) (.reshap (.zero sv1) (.space sv0) (.space sv1))

def repairedResult_typed (Γv : ValCtx) : ValHasType Γv repairedResult (.space sv0) :=
  .vadd (.zero (sv0Valid Γv))
    (.reshap (.zero (sv1Valid Γv)) (.space (sv1Valid Γv)) (.space (sv0Valid Γv)))
    (sv0Valid Γv)

example (hc : Operational.TypedContext Δ Γ Γv Ψ)
    (hl : EvalCtx.lookup Ψ (x, b) =
      some (.scale (.zero (.tprod .real .real)) (.rlit 0))) : False := by
  obtain ⟨hv⟩ := hc.lookup_typed hl
  cases hv with
  | scale hbad _ => cases hbad

end GLang.TypedContextPreservationBoundary
