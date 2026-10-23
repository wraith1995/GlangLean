import GLang.Examples.TangentMovingFrame
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceProjectionCore

/-! A fixed two-coordinate area program. Geometry occurs only in the declared
input/output dimension checks. Correctness of the specialization is separate
from the ordinary operational relation. -/
namespace GLang.Examples.TangentCoordinates

open PartialValueEval

/-- Read one moving-frame coordinate, requiring the declared tangent dimension
and the actual input array to have length two. -/
def areaCoordinate (sv : ValSpace) (i : Fin 2) (v : ValExpr) : ValExpr :=
  .ttv pointSV (.delta i.val pointSV) (.reshap v (.space pointSV) (.space sv))

/-- The scalar determinant polynomial; its only arithmetic is four coordinate
reads, two products, a negation, and an addition. -/
def areaPolynomial (sv : ValSpace) (v w : ValExpr) : ValExpr :=
  .vadd .real
    (.scale (areaCoordinate sv 0 v) (areaCoordinate sv 1 w))
    (.scale (.rlit (-1)) (.scale (areaCoordinate sv 1 v) (areaCoordinate sv 0 w)))

/-- Preserve the exact requested image-space dimension annotation. -/
def optimizedAreaCode (sv av : ValSpace) (v w : ValExpr) : ValExpr :=
  .reshap (areaPolynomial sv v w) (.space av) (.space .real)

/-- Arithmetic nodes of this deliberately small optimization. -/
inductive AreaArithmetic where
  | input : Name → AreaArithmetic
  | literal : ℝ → AreaArithmetic
  | delta : Nat → AreaArithmetic
  | product : AreaArithmetic → AreaArithmetic → AreaArithmetic
  | add : AreaArithmetic → AreaArithmetic → AreaArithmetic
  | contract : AreaArithmetic → AreaArithmetic → AreaArithmetic

def areaArithmetic : ValExpr → Option AreaArithmetic
  | .var x _ => some (.input x)
  | .rlit r => some (.literal r)
  | .delta i _ => some (.delta i)
  | .scale v w => return .product (← areaArithmetic v) (← areaArithmetic w)
  | .vadd _ v w => return .add (← areaArithmetic v) (← areaArithmetic w)
  | .ttv _ v w => return .contract (← areaArithmetic v) (← areaArithmetic w)
  | .reshap v _ _ => areaArithmetic v
  | _ => none

/-- Parameterization and result-space expressions disappear from the entire
arithmetic tree, not just from its mathematical result. -/
theorem optimizedAreaCode_arithmetic (sv av : ValSpace) (v w : Name) :
    areaArithmetic (optimizedAreaCode sv av (.var v (.space sv)) (.var w (.space sv))) =
      some (.add
        (.product (.contract (.delta 0) (.input v)) (.contract (.delta 1) (.input w)))
        (.product (.literal (-1))
          (.product (.contract (.delta 1) (.input v)) (.contract (.delta 0) (.input w))))) := rfl

private theorem real_dof (q : PartialFFSOracle) :
    ValSpace.real.dofPartial q = .ok 1 := by
  simp [ValSpace.dofPartial, ValSpace.shpOfPartial]

private theorem point_dof (q : PartialFFSOracle) :
    pointSV.dofPartial q = .ok 2 := by
  simp [pointSV, ValSpace.dofPartial, ValSpace.shpOfPartial, bind, Except.bind, pure, Except.pure]

private theorem array_one_eq {f g : Nat → ℝ} (h : f 0 = g 0) :
    FlatArray.ofFn 1 f = FlatArray.ofFn 1 g := by
  refine FlatArray.ext_get (by rfl) ?_
  intro i
  by_cases hi : i < 1
  · have hi0 : i = 0 := by omega
    subst i
    simpa using h
  · simp [FlatArray.get_ofFn, hi]

/-- The selector is proved against the current error-capable evaluator. -/
theorem areaCoordinate_eval {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
    {sv : ValSpace} {v : ValExpr} {a : FlatArray}
    (hd : sv.dofPartial (orc ρ [] []) = .ok 2)
    (hv : denotValB_partial orc ρ [] [] v = .ok (.array a))
    (ha : a.length = 2) (i : Fin 2) :
    denotValB_partial orc ρ [] [] (areaCoordinate sv i v) =
      .ok (.array (FlatArray.ofFn 1 (fun _ => a.get i.val))) := by
  have hr : denotValB_partial orc ρ [] [] (.reshap v (.space pointSV) (.space sv)) =
      .ok (.array a) := by
    rw [denotValB_partial, hv]
    simp [reshapeInferred, reshapeBetween, reshapeArray, hd, point_dof, ha]
  unfold areaCoordinate
  rw [denotValB_partial]
  simp only [ValExpr.inferSpaceCtx, ValTy.spaceOf_space]
  have hg : dimensions (orc ρ [] []) [pointSV, pointSV, pointSV, .real] = .ok () := by
    simp [dimensions, point_dof, real_dof, bind, Except.bind]
  rw [withDimensions, hg]
  dsimp only
  rw [hr]
  have hdelta := PartialAdequacy.delta_ok (point_dof (orc ρ [] [])) i.val
  rw [hdelta]
  simp only [ValValSem.bindArrays, ValValSem.bindArray, ValueShape.ttv,
    ValueShape.pair, pointSV, ValSpace.dof, ValSpace.shpOf, List.foldr, Nat.mul_one, Nat.reduceAdd, ValValSem.arrayOf, FlatArray.length_ofFn, ha,
    and_self, if_true]
  congr 2
  apply array_one_eq
  fin_cases i <;> norm_num [FlatArray.get_ofFn, Finset.sum_range_succ]

private theorem scalar_scale_eval {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
    {v w : ValExpr} {a b : ℝ}
    (hwty : ValExpr.inferSpaceCtx [] w = .real)
    (hv : denotValB_partial orc ρ [] [] v = .ok (.array (FlatArray.ofFn 1 (fun _ => a))))
    (hw : denotValB_partial orc ρ [] [] w = .ok (.array (FlatArray.ofFn 1 (fun _ => b)))) :
    denotValB_partial orc ρ [] [] (.scale v w) =
      .ok (.array (FlatArray.ofFn 1 (fun _ => a * b))) := by
  rw [denotValB_partial, hwty]
  simp only [withDimensions, dimensions, real_dof, bind, Except.bind]
  rw [hv, hw]
  simp only [ValValSem.bindArrays, ValValSem.bindArray, ValueShape.scale,
    FlatArray.length_ofFn, ValSpace.dof, ValSpace.shpOf, List.foldr, Nat.mul_one, Nat.reduceAdd, and_self, if_true, ValValSem.arrayOf,
    ValExpr.inferSpaceCtx, hwty]
  congr 2
  apply array_one_eq
  simp

/-- The complete fixed program computes exactly `a₀ b₁ - a₁ b₀`. -/
theorem areaPolynomial_eval {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
    {sv : ValSpace} {v w : ValExpr} {a b : FlatArray}
    (hd : sv.dofPartial (orc ρ [] []) = .ok 2)
    (hv : denotValB_partial orc ρ [] [] v = .ok (.array a))
    (hw : denotValB_partial orc ρ [] [] w = .ok (.array b))
    (ha : a.length = 2) (hb : b.length = 2) :
    denotValB_partial orc ρ [] [] (areaPolynomial sv v w) =
      .ok (.array (FlatArray.ofFn 1 (fun _ => a.get 0 * b.get 1 - a.get 1 * b.get 0))) := by
  have h0 := scalar_scale_eval (by rfl)
    (areaCoordinate_eval hd hv ha (0 : Fin 2)) (areaCoordinate_eval hd hw hb (1 : Fin 2))
  have h1 := scalar_scale_eval (by rfl)
    (areaCoordinate_eval hd hv ha (1 : Fin 2)) (areaCoordinate_eval hd hw hb (0 : Fin 2))
  have hn : denotValB_partial orc ρ [] [] (.rlit (-1)) =
      .ok (.array (FlatArray.ofFn 1 (fun _ => -1))) := by
    simp only [denotValB_partial, ValExpr.inferSpaceCtx, withDimensions,
      dimensions, real_dof, bind, Except.bind, ValSpace.dof, ValSpace.shpOf, List.foldr, Nat.mul_one, Nat.reduceAdd, ValValSem.arrayOf]
    congr 2
    exact array_one_eq (by simp)
  have hneg := scalar_scale_eval (by rfl) hn h1
  unfold areaPolynomial
  rw [denotValB_partial]
  simp only [withDimensions, dimensions, real_dof, bind, Except.bind]
  rw [h0, hneg]
  simp only [ValValSem.bindArrays, ValValSem.bindArray, ValSpace.dof, ValSpace.shpOf, List.foldr, Nat.mul_one, Nat.reduceAdd,
    FlatArray.length_ofFn, ↓reduceDIte]
  congr 2
  change FlatArray.ofFn 1 _ = _
  apply array_one_eq
  simp [sub_eq_add_neg]

theorem optimizedAreaCode_eval {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
    {sv av : ValSpace} {v w : ValExpr} {a b : FlatArray}
    (hd : sv.dofPartial (orc ρ [] []) = .ok 2)
    (hout : av.dofPartial (orc ρ [] []) = .ok 1)
    (hv : denotValB_partial orc ρ [] [] v = .ok (.array a))
    (hw : denotValB_partial orc ρ [] [] w = .ok (.array b))
    (ha : a.length = 2) (hb : b.length = 2) :
    denotValB_partial orc ρ [] [] (optimizedAreaCode sv av v w) =
      .ok (.array (FlatArray.ofFn 1 (fun _ => a.get 0 * b.get 1 - a.get 1 * b.get 0))) := by
  rw [optimizedAreaCode, denotValB_partial, areaPolynomial_eval hd hv hw ha hb]
  simp [reshapeInferred, reshapeBetween, reshapeArray, real_dof, hout]

/-- Static value typing retains both the input and output dimension annotations. -/
def areaCoordinate_hasType {Γ : ValCtx} {sv : ValSpace} {v : ValExpr}
    (hs : ValSValid Γ sv) (hv : ValHasType Γ v (.space sv)) (i : Fin 2) :
    ValHasType Γ (areaCoordinate sv i v) (.space .real) :=
  .ttv_real (.dsum .real .real) (.delta (.dsum .real .real))
    (.reshap hv (.space hs) (.space (.dsum .real .real))) (by intros; intro h; cases h)

def areaPolynomial_hasType {Γ : ValCtx} {sv : ValSpace} {v w : ValExpr}
    (hs : ValSValid Γ sv) (hv : ValHasType Γ v (.space sv))
    (hw : ValHasType Γ w (.space sv)) :
    ValHasType Γ (areaPolynomial sv v w) (.space .real) :=
  .vadd (.scale (areaCoordinate_hasType hs hv 0) (areaCoordinate_hasType hs hw 1))
    (.scale (.rlit (-1)) (.scale (areaCoordinate_hasType hs hv 1)
      (areaCoordinate_hasType hs hw 0))) .real

def optimizedAreaCode_hasType {Γ : ValCtx} {sv av : ValSpace} {v w : ValExpr}
    (hs : ValSValid Γ sv) (ha : ValSValid Γ av)
    (hv : ValHasType Γ v (.space sv)) (hw : ValHasType Γ w (.space sv)) :
    ValHasType Γ (optimizedAreaCode sv av v w) (.space av) :=
  .reshap (areaPolynomial_hasType hs hv hw) (.space .real) (.space ha)

private theorem areaCoordinate_error {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
    {sv : ValSpace} {v : ValExpr}
    (he : denotValB_partial orc ρ [] [] (.reshap v (.space pointSV) (.space sv)) =
      .error .mismatch) (i : Fin 2) :
    denotValB_partial orc ρ [] [] (areaCoordinate sv i v) = .error .mismatch := by
  rw [areaCoordinate, denotValB_partial]
  simp only [ValExpr.inferSpaceCtx, ValTy.spaceOf_space]
  have hg : dimensions (orc ρ [] []) [pointSV, pointSV, pointSV, .real] = .ok () := by
    simp [dimensions, point_dof, real_dof, bind, Except.bind]
  rw [withDimensions, hg]
  dsimp only
  rw [PartialAdequacy.delta_ok (point_dof (orc ρ [] [])) i.val, he]
  rfl

/-- A rank other than two, including a failed dimension query, is rejected. -/
theorem areaCoordinate_dimension_error {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
    {sv : ValSpace} {v : ValExpr}
    (hd : sv.dofPartial (orc ρ [] []) ≠ .ok 2) (i : Fin 2) :
    denotValB_partial orc ρ [] [] (areaCoordinate sv i v) = .error .mismatch := by
  apply areaCoordinate_error _ i
  rw [denotValB_partial]
  cases he : denotValB_partial orc ρ [] [] v with
  | error e => cases e; rfl
  | ok z =>
      cases z with
      | fn T f => simp [reshapeInferred, reshapeBetween]
      | array a =>
          simp only [reshapeInferred, reshapeBetween, reshapeArray, point_dof]
          cases hdim : sv.dofPartial (orc ρ [] []) with
          | error e => cases e; rfl
          | ok n =>
              have hn : n ≠ 2 := by intro hn; subst n; exact hd hdim
              simp [hn]

/-- Short or oversized input arrays are rejected even when the rank is two. -/
theorem areaCoordinate_length_error {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
    {sv : ValSpace} {v : ValExpr} {a : FlatArray}
    (hd : sv.dofPartial (orc ρ [] []) = .ok 2)
    (hv : denotValB_partial orc ρ [] [] v = .ok (.array a))
    (ha : a.length ≠ 2) (i : Fin 2) :
    denotValB_partial orc ρ [] [] (areaCoordinate sv i v) = .error .mismatch := by
  apply areaCoordinate_error _ i
  rw [denotValB_partial, hv]
  simp [reshapeInferred, reshapeBetween, reshapeArray, hd, point_dof, ha]

/-- The exact result-space check remains active after specialization. -/
theorem optimizedAreaCode_output_error {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
    {sv av : ValSpace} {v w : ValExpr} {a b : FlatArray}
    (hd : sv.dofPartial (orc ρ [] []) = .ok 2)
    (hout : av.dofPartial (orc ρ [] []) ≠ .ok 1)
    (hv : denotValB_partial orc ρ [] [] v = .ok (.array a))
    (hw : denotValB_partial orc ρ [] [] w = .ok (.array b))
    (ha : a.length = 2) (hb : b.length = 2) :
    denotValB_partial orc ρ [] [] (optimizedAreaCode sv av v w) = .error .mismatch := by
  rw [optimizedAreaCode, denotValB_partial, areaPolynomial_eval hd hv hw ha hb]
  simp only [reshapeInferred, reshapeBetween, reshapeArray, real_dof]
  cases hdim : av.dofPartial (orc ρ [] []) with
  | error e => cases e; rfl
  | ok n =>
      have hn : n ≠ 1 := by intro hn; subst n; exact hout hdim
      simp [Ne.symm hn]

end GLang.Examples.TangentCoordinates
