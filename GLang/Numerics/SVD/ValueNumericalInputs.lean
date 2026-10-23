import GLang.Value.Arrays

namespace GLang

/-- The value denotation fails exactly when a runtime value does not have the
flat-array/function shape or dimension required by its annotated operation. -/
inductive DimError where
  | mismatch
  deriving Repr, DecidableEq, Inhabited

/-- Runtime shape contract for the represented map and its two metric arrays.
If the represented map has source dimension `d0` and target dimension `d1`,
its row-major array has `d0 * d1` entries, while the two metric arrays are
square at `d0` and `d1`, respectively. Kept as a separate predicate so
evaluator equations and adequacy proofs can name exactly the guard which
excludes zero-padding/truncation. -/
def GSVDInputsShape (d0 d1 : Nat) (map leftMetric rightMetric : FlatArray) : Prop :=
  map.length = d0 * d1 ∧
    leftMetric.length = d0 * d0 ∧
    rightMetric.length = d1 * d1

instance GSVDInputsShape.instDecidable (d0 d1 : Nat)
    (map leftMetric rightMetric : FlatArray) :
    Decidable (GSVDInputsShape d0 d1 map leftMetric rightMetric) := by
  unfold GSVDInputsShape
  infer_instance

end GLang
