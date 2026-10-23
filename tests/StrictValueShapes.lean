import GLang.Value.Supporting.TotalDimensionSemantics

/-! Malformed runtime arrays must fail before arithmetic can pad or truncate
coordinates. Zero-dimensional valid inputs and bounded inactive summands are
separate from failed reads. -/
namespace GLang.StrictValueShapeTests

private def q : FFSOracle := fun _ _ _ => 0
private def short : ValEnvSem := fun _ => .array FlatArray.empty
private def long : ValEnvSem := fun _ => .array (FlatArray.zeros 2)
private def x : ValExpr := .var "x" (.space .real)

macro "shape_test" : tactic => `(tactic|
  simp [denotValB_semS, q, short, long, x, FFSOracleSem.const,
    ValValSem.bindArrays, ValValSem.bindArray, ValValSem.sequenceArrays,
    ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, ValTy.spaceOf,
    ValSpace.dof, ValSpace.shpOf, ValueShape.scale, ValueShape.pair,
    ValueShape.tensor, ValueShape.matrices, ValueShape.ttv, ValueShape.mtm,
    ValueShape.family, ValSpace.dof_real, ValSpace.dof_empty, ValSpace.dof_tprod,
    List.attach_cons, List.attach_nil, ValValSem.arrayOf, FlatArray.empty, FlatArray.zeros,
    FlatArray.ofFn])

example : denotValB_semS (.const q) short [] [] (.scale x (.rlit 2)) =
    .error .mismatch := by shape_test
example : denotValB_semS (.const q) long [] [] (.scale (.rlit 2) x) =
    .error .mismatch := by shape_test
example : denotValB_semS (.const q) short [] [] (.tprodE x (.rlit 2)) =
    .error .mismatch := by shape_test
example : denotValB_semS (.const q) long [] [] (.dsumE x (.rlit 2)) =
    .error .mismatch := by shape_test
example : denotValB_semS (.const q) short [] [] (.vtrans (.rlit 2)) =
    .error .mismatch := by shape_test
example : denotValB_semS (.const q) short [] [] (.ttv .empty (.rlit 2) (.rlit 3)) =
    .error .mismatch := by shape_test
example : denotValB_semS (.const q) short [] []
    (.mtm 0 0 .empty .empty (.zero (.tprod .real .real)) (.zero (.tprod .real .real))) =
    .error .mismatch := by shape_test
example : denotValB_semS (.const q) short [] [] (.vkrn (.rlit 2) (.rlit 3)) =
    .error .mismatch := by shape_test
example : denotValB_semS (.const q) short [] [] (.vblk (.rlit 2) (.rlit 3)) =
    .error .mismatch := by shape_test
example : denotValB_semS (.const q) short [] [] (.vsum .real []) =
    .error .mismatch := by shape_test
example : denotValB_semS (.const q) short [] [] (.vsum .real [x]) =
    .error .mismatch := by
  rw [denotValB_semS.eq_16]
  simp only [List.attach_map_val]
  shape_test

-- Valid zero-dimensional operations remain successful.
example : ∃ a, denotValB_semS (.const q) short [] []
    (.tprodE (.zero .empty) (.rlit 2)) = .ok (.array a) ∧ a.length = 0 := by
  shape_test

example : ∃ a, denotValB_semS (.const q) short [] [] (.vsum .empty []) =
    .ok (.array a) ∧ a.length = 0 := by
  rw [denotValB_semS.eq_16]
  simp only [List.attach_map_val]
  shape_test

-- A malformed inactive candidate is outside the summation range.
example : ∃ a, denotValB_semS (.const q) short [] []
    (.vsum .real [.rlit 3, .bvar 999]) = .ok (.array a) ∧
      a.length = 1 ∧ a.get 0 = 3 := by
  rw [denotValB_semS.eq_16]
  simp only [List.attach_map_val]
  shape_test
  simp [FlatArray.get, ValSpace.dof_real]

end GLang.StrictValueShapeTests
