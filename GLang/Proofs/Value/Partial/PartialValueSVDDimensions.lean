import GLang.Numerics.SVD.ValueSVDRank
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectLocality

/-! SVD equations for the live partial dimension semantics. These are proved
presentations of the existing evaluator, including every error branch, rather
than an additional oracle contract or a change to the public hypotheses. -/
namespace GLang

/-- Count the positive singular values after checking the matrix shape/storage. -/
noncomputable def ffsOperandSVDPartial (shape : Except DimError (List Nat))
    (operand : Except DimError ValValSem) : Except DimError Nat :=
  match shape with
  | .error e => .error e
  | .ok sh =>
    match operand with
    | .error e => .error e
    | .ok v =>
      match sh, v with
      | [m, n], .array a =>
          if a.length = m * n then .ok (matrixSVD (denotAsMatrix m n a.get)).r
          else .error .mismatch
      | _, _ => .error .mismatch

/-- SVD and rank formulations agree on successes and failures alike. -/
theorem ffsOperandSVDPartial_eq (shape : Except DimError (List Nat))
    (operand : Except DimError ValValSem) :
    ffsOperandSVDPartial shape operand = ffsOperandRankPartial shape operand := by
  cases shape with
  | error err => rfl
  | ok sh =>
    cases operand with
    | error err => rfl
    | ok v =>
      cases sh with
      | nil => cases v <;> rfl
      | cons m sh =>
        cases sh with
        | nil => cases v <;> rfl
        | cons n sh =>
          cases sh with
          | nil => cases v <;> simp [ffsOperandSVDPartial, ffsOperandRankPartial, matrixSVD_rank]
          | cons d sh => cases v <;> rfl

/-- Four fundamental-space dimensions obtained from the SVD count. -/
noncomputable def ffsDimensionSVD (p : ValFFSProp)
    (shape : Except DimError (List Nat)) (operand : Except DimError ValValSem) :
    Except DimError Nat := do
  let sh ← shape
  let r ← ffsOperandSVDPartial (.ok sh) operand
  pure (ffsDim p sh r)

theorem ffsDimensionSVD_eq (p : ValFFSProp)
    (shape : Except DimError (List Nat)) (operand : Except DimError ValValSem) :
    ffsDimensionSVD p shape operand = ffsDimensionPartial p shape operand := by
  unfold ffsDimensionSVD ffsDimensionPartial
  simp only [ffsOperandSVDPartial_eq]

/-- The concrete dimension query has an SVD equation with no supplied oracle. -/
theorem ffsQuery_eq_svd (rho : ValEnvSem) (Gamma : List ValTy) (Delta : List ValValSem)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr)
    (hf : ValueQueryDependencies.Finite (.space Gamma (.ffs p s e))) :
    PartialDirectOracle.oracle rho Gamma Delta p s e =
      ffsDimensionSVD p (Adequacy.Partial.shapeOf rho Gamma Delta s)
        (Adequacy.Partial.evalVal rho Gamma Delta e) := by
  rw [ffsDimensionSVD_eq]
  exact PartialDirectLocality.oracle_eq rho Gamma Delta p s e hf

theorem shapeOf_ffs_svd (rho : ValEnvSem) (Gamma : List ValTy) (Delta : List ValValSem)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr)
    (hf : ValueQueryDependencies.Finite (.space Gamma (.ffs p s e))) :
    Adequacy.Partial.shapeOf rho Gamma Delta (.ffs p s e) =
      (do
        let n ← ffsDimensionSVD p (Adequacy.Partial.shapeOf rho Gamma Delta s)
          (Adequacy.Partial.evalVal rho Gamma Delta e)
        pure [n]) := by
  change ValSpace.shpOfPartial (PartialDirectOracle.oracle rho Gamma Delta) (.ffs p s e) = _
  rw [ValSpace.shpOfPartial, ffsQuery_eq_svd rho Gamma Delta p s e hf]

end GLang
