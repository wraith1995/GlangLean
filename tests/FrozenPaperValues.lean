import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectLocality
import GLang.Proofs.Value.Runtime.RuntimeValueInfer
import GLang.Proofs.Value.Runtime.RuntimeValueInstantiation
import GLang.Proofs.Value.Typing.ValuePrimitiveShapeBounds

/-! Malformed runtime arrays must fail before arithmetic can pad or truncate
coordinates. Zero-dimensional valid inputs and bounded inactive summands are
separate from failed reads. -/
namespace GLang.FrozenPaperValueTests

private def short : ValEnvSem := fun _ => .array FlatArray.empty
private def long : ValEnvSem := fun _ => .array (FlatArray.zeros 2)
private def x : ValExpr := .var "x" (.space .real)

macro "partial_shape_test" : tactic => `(tactic|
  simp [denotValB_partial, short, long, x,
    PartialValueEval.withDimensions, PartialValueEval.dimensions, PartialValueEval.numbers,
    ValSpace.dofPartial, ValSpace.shpOfPartial, Bind.bind, Except.bind, Pure.pure, Except.pure,
    ValValSem.bindArrays, ValValSem.bindArray, ValValSem.sequenceArrays,
    ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, ValTy.spaceOf,
    ValSpace.dof, ValSpace.shpOf, ValueShape.scale, ValueShape.pair,
    ValueShape.tensor, ValueShape.matrices, ValueShape.ttv, ValueShape.mtm,
    ValueShape.family, ValSpace.dof_real, ValSpace.dof_empty, ValSpace.dof_tprod,
    List.attach_cons, List.attach_nil, ValValSem.arrayOf, FlatArray.empty, FlatArray.zeros,
    FlatArray.ofFn])

example : denotValB_partial PartialDirectOracle.oracle short [] [] (.scale x (.rlit 2)) =
    .error .mismatch := by partial_shape_test
example : denotValB_partial PartialDirectOracle.oracle long [] [] (.scale (.rlit 2) x) =
    .error .mismatch := by partial_shape_test
example : denotValB_partial PartialDirectOracle.oracle short [] [] (.tprodE x (.rlit 2)) =
    .error .mismatch := by partial_shape_test
example : denotValB_partial PartialDirectOracle.oracle long [] [] (.dsumE x (.rlit 2)) =
    .error .mismatch := by partial_shape_test
example : denotValB_partial PartialDirectOracle.oracle short [] [] (.vtrans (.rlit 2)) =
    .error .mismatch := by partial_shape_test
example : denotValB_partial PartialDirectOracle.oracle short [] [] (.ttv .empty (.rlit 2) (.rlit 3)) =
    .error .mismatch := by partial_shape_test
example : denotValB_partial PartialDirectOracle.oracle short [] []
    (.mtm 0 0 .empty .empty (.zero (.tprod .real .real)) (.zero (.tprod .real .real))) =
    .error .mismatch := by partial_shape_test
example : denotValB_partial PartialDirectOracle.oracle short [] [] (.vkrn (.rlit 2) (.rlit 3)) =
    .error .mismatch := by partial_shape_test
example : denotValB_partial PartialDirectOracle.oracle short [] [] (.vblk (.rlit 2) (.rlit 3)) =
    .error .mismatch := by partial_shape_test
example : denotValB_partial PartialDirectOracle.oracle short [] [] (.vsum .real []) =
    .error .mismatch := by partial_shape_test
example : denotValB_partial PartialDirectOracle.oracle short [] [] (.vsum .real [x]) =
    .error .mismatch := by
  rw [denotValB_partial.eq_16]
  simp only [List.attach_map_val]
  partial_shape_test

-- Valid zero-dimensional operations remain successful.
example : ∃ a, denotValB_partial PartialDirectOracle.oracle short [] []
    (.tprodE (.zero .empty) (.rlit 2)) = .ok (.array a) ∧ a.length = 0 := by
  partial_shape_test

example : ∃ a, denotValB_partial PartialDirectOracle.oracle short [] [] (.vsum .empty []) =
    .ok (.array a) ∧ a.length = 0 := by
  rw [denotValB_partial.eq_16]
  simp only [List.attach_map_val]
  partial_shape_test

-- A malformed inactive candidate is outside the summation range.
example : ∃ a, denotValB_partial PartialDirectOracle.oracle short [] []
    (.vsum .real [.rlit 3, .bvar 999]) = .ok (.array a) ∧
      a.length = 1 ∧ a.get 0 = 3 := by
  rw [denotValB_partial.eq_16]
  simp only [List.attach_map_val]
  partial_shape_test
  simp [FlatArray.get, ValSpace.dof_real]

-- The same expression is well typed but its lengths disagree at runtime.
example : RuntimeValue.ValHasType ∅
    (.vadd .real (.rlit 2) (.zero .empty)) (.space .real) :=
  .vadd (.rlit 2) (.zero .empty) .real

example : denotValB_partial PartialDirectOracle.oracle short [] []
    (.vadd .real (.rlit 2) (.zero .empty)) = .error .mismatch := by partial_shape_test

-- A zero-dimensional constructor is successful, but reading it is an error.
example : ValValSem.readResultChecked
    (denotValB_partial PartialDirectOracle.oracle short [] [] (.zero .empty)) 0 =
      .error .mismatch := by
  simp [ValValSem.readResultChecked, ValValSem.readChecked, FlatArray.readChecked,
    denotValB_partial, PartialValueEval.withDimensions, PartialValueEval.dimensions,
    ValExpr.inferSpaceCtx, ValSpace.dofPartial, ValSpace.shpOfPartial,
    ValValSem.arrayOf, FlatArray.ofFn, Bind.bind, Except.bind, Pure.pure, Except.pure]

-- Delta is an array constructor, not a read. The out-of-range index gives zero.
example : ∃ a, denotValB_partial PartialDirectOracle.oracle short [] [] (.delta 9 .real) =
    .ok (.array a) ∧ a.length = 1 ∧ a.get 0 = 0 := by
  partial_shape_test
  simp [FlatArray.get, ValSpace.dof_real]

-- Annotated free variables must match their context, not merely have an inferred type.
example : ValExpr.inferType (.var "x" (.space .real)) = .space .real := rfl
example : ¬ Nonempty (RuntimeValue.ValHasType ∅ (.var "x" (.space .real)) (.space .real)) := by
  rintro ⟨h⟩
  cases h with | var h => simp at h

-- Binary application substitutes the argument. Formation follows from typing.
noncomputable example (hc : RuntimeValue.ValCtxValid ε)
    (hf : RuntimeValue.ValHasType ε f (.piTy d c))
    (ha : RuntimeValue.ValHasType ε a d) :
    RuntimeValue.ValHasType ε (.appV f a) (ValTy.applyCodomain a c) := by
  obtain ⟨k, hk⟩ := hf.regular hc
  cases k with
  | base => cases hk
  | arrow kd kc => exact .appV hf ha rfl (hk.applyCodomain hc ha)

-- Unused matrix indices and the stored right annotation do not affect raw evaluation.
example (q : PartialFFSOracleSem) (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (i j i' j' : Nat) (s r r' : ValSpace) (a b : ValExpr) :
    denotValB_partial q ρ Γ Δ (.mtm i j s r a b) =
      denotValB_partial q ρ Γ Δ (.mtm i' j' s r' a b) := by
  simp only [denotValB_partial, ValExpr.inferSpaceCtx]

-- The shape guards bound every coordinate read in matrix contraction.
example {q : FFSOracle} {c l o s r : ValSpace} {a b : FlatArray}
    (h : ValueShape.mtm q c (.tprod l o) (.tprod s r) a b)
    {i j k : Nat} (hi : i < s.dof q) (hj : j < o.dof q) (hk : k < c.dof q) :
    o.dof q * k + j < a.length ∧ c.dof q * i + k < b.length :=
  ValueShape.mtm_access h hi hj hk

-- Missing local variables and calling a scalar are errors, not empty arrays.
example : denotValB_partial PartialDirectOracle.oracle short [] [] (.bvar 0) =
    .error .mismatch := by simp [denotValB_partial, StrictValueAccess.lookup]
example : denotValB_partial PartialDirectOracle.oracle short [] [] (.appV (.rlit 1) (.rlit 2)) =
    .error .mismatch := by simp [denotValB_partial, ValExpr.inferTypeCtx]

-- A failing dimension query does not become a zero-dimensional success, even
-- beneath a tensor with a zero-dimensional factor.
example (q : PartialFFSOracleSem) (ρ : ValEnvSem) (p : ValFFSProp)
    (s : ValSpace) (e : ValExpr) (h : q ρ [] [] p s e = .error .mismatch) :
    denotValB_partial q ρ [] [] (.zero (.tprod .empty (.ffs p s e))) =
      .error .mismatch := by
  simp [denotValB_partial, PartialValueEval.withDimensions, PartialValueEval.dimensions,
    ValExpr.inferSpaceCtx, ValSpace.dofPartial, ValSpace.shpOfPartial, h,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

-- Rank queries reject malformed matrix storage before asking for its rank.
example (m n : Nat) (a : FlatArray) (h : a.length ≠ m*n) :
    ffsOperandRankPartial (.ok [m,n]) (.ok (.array a)) = .error .mismatch :=
  ffsOperandRankPartial_wrong_length m n a h

-- All four generalized SVD vector blocks check both their shapes and metrics.
example (p : ValFFSProp) (m n : Nat) (a g h : FlatArray)
    (bad : ¬ GSVDInputsShape m n a g h) :
    ValueCanonicalFSV.eval p m n a g h = .error .mismatch :=
  ValueCanonicalFSV.eval_shape_mismatch p m n a g h bad
example (p : ValFFSProp) (m n : Nat) (a g h : FlatArray)
    (bad : ¬ (denotAsMatrix m m g.get).PosDef ∨ ¬ (denotAsMatrix n n h.get).PosDef) :
    ValueCanonicalFSV.eval p m n a g h = .error .mismatch :=
  ValueCanonicalFSV.eval_metric_mismatch p m n a g h bad

example (q : PartialFFSOracleSem) (ρ : ValEnvSem) (a : FlatArray) (h : a.length = 1) :
    PartialValueEval.reshapeArray q ρ [] [] [] [] a (.tprod .real .real) .real =
      .ok (.array a) := by
  simp [PartialValueEval.reshapeArray, ValSpace.dofPartial, ValSpace.shpOfPartial,
    Bind.bind, Except.bind, Pure.pure, Except.pure, h]
example (q : PartialFFSOracleSem) (ρ : ValEnvSem) (a : FlatArray) :
    PartialValueEval.reshapeArray q ρ [] [] [] [] a .empty .real =
      .error .mismatch := by
  simp [PartialValueEval.reshapeArray, ValSpace.dofPartial, ValSpace.shpOfPartial,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private def two : ValSpace := .dsum .real .real
private def three : ValSpace := .dsum two .real
private def rectangularEnv : ValEnvSem := fun name =>
  if name = "a" then .array (FlatArray.ofFn 2 (fun i => (i + 2 : Nat)))
  else .array (FlatArray.ofFn 6 (fun i => (i + 1 : Nat)))
private def rectangular : ValExpr :=
  .mtm 17 23 two two (.var "a" (.space (.tprod two .real)))
    (.var "b" (.space (.tprod three two)))
example : ∃ a, denotValB_partial PartialDirectOracle.oracle rectangularEnv [] [] rectangular =
    .ok (.array a) ∧ a.length = 3 ∧ a.get 0 = 8 ∧ a.get 1 = 18 ∧ a.get 2 = 28 := by
  simp [rectangular, rectangularEnv, two, three, denotValB_partial,
    PartialValueEval.withDimensions, PartialValueEval.dimensions,
    ValExpr.inferSpaceCtx, ValTy.spaceOf, ValSpace.dofPartial, ValSpace.shpOfPartial,
    ValValSem.bindArrays, ValValSem.bindArray, ValueShape.mtm, ValueShape.matrices,
    ValueShape.tensor, ValValSem.arrayOf, FlatArray.ofFn, FlatArray.get,
    Finset.sum_range_succ, Bind.bind, Except.bind, Pure.pure, Except.pure]
  norm_num

open Lean Elab Command in
elab "check_frozen_value_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``RuntimeValue.ValHasType.inferType_eq_of_typed,
      ``RuntimeValue.ValTValid.applyCodomain, ``ValueShape.mtm_access,
      ``RuntimeValue.validExpr_queryFinite, ``ValueCanonicalFSV.eval_success_valid] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "Unexpected axiom in {n}: {ax}"
  logInfo "Frozen-paper value typing and finite-array checks: foundations only."
check_frozen_value_axioms

end GLang.FrozenPaperValueTests
