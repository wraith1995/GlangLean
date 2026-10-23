import GLang.Artifact
import Lean

open GLang Lean Meta Elab Command

namespace PaperValueAnnotations

-- The only occurrence of x in each expression is inside the indicated field.
def dynamic (x : VName) : ValSpace :=
  .ffs .image (.tprod .real .real) (.var x (.space (.tprod .real .real)))
def annotationCases (x : VName) : List ValExpr :=
  [ .reshap (.zero .empty) (.space .empty) (.space (dynamic x))
  , .reshap (.zero .empty) (.space (dynamic x)) (.space .empty)
  , .mtm 0 0 .empty (dynamic x) (.zero .empty) (.zero .empty)
  , .vadd (dynamic x) (.zero .empty) (.zero .empty) ]

example : (annotationCases "x").map ValExpr.fv = List.replicate 4 {"x"} := by
  simp [annotationCases, dynamic, ValExpr.fv, ValTy.fv, ValSpace.fv]

example : (annotationCases "x").map
    (ValExpr.subst "x" (.var "y" (.space (.tprod .real .real)))) = annotationCases "y" := by
  simp [annotationCases, dynamic, ValExpr.subst, ValTy.subst, ValSpace.subst]

-- Alpha-renaming via the live close/open operations traverses every annotation.
example : (annotationCases "x").map (fun e =>
    ValExpr.openVar "y" (.space (.tprod .real .real)) (ValExpr.closeRec 0 "x" e)) =
    annotationCases "y" := by
  simp [annotationCases, dynamic, ValExpr.closeRec, ValTy.closeRec, ValSpace.closeRec,
    ValExpr.openVar, ValExpr.openRec, ValTy.openRec, ValSpace.openRec]

-- Opening a dependent codomain traverses its annotation. The binder's own
-- domain is outside its scope; closing then opening a fresh name recovers it.
example (s : ValTy) : ValTy.openVar "x" s
    (.space (.ffs .image (.tprod .real .real) (.bvar 0))) =
    .space (.ffs .image (.tprod .real .real) (.var "x" s)) := rfl

end PaperValueAnnotations
