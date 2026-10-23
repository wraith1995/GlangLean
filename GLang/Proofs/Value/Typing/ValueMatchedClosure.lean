import GLang.Proofs.Value.Queries.ValueDependencyRank
import GLang.Proofs.Value.Binding.ValueLN

namespace GLang.ValueDependency

/-- Only annotations agreeing with the original context are closure obligations.
This permits a size induction on the enclosing syntax without assuming every
context entry closed in advance. -/
def MatchedAnnotationsClosed (ε : ValCtx) (xs : List (VName × ValTy)) : Prop :=
  ∀ x a, (x, a) ∈ xs → ε.lookup x = some a → ValTy.lc a

theorem MatchedAnnotationsClosed.mono {ε : ValCtx} {xs ys : List (VName × ValTy)}
    (h : MatchedAnnotationsClosed ε ys) (hs : xs ⊆ ys) : MatchedAnnotationsClosed ε xs :=
  fun x a hx hl => h x a (hs hx) hl

theorem listAnnotations_mem {es : List ValExpr} {e : ValExpr} (he : e ∈ es)
    {q : VName × ValTy} (hq : q ∈ exprAnnotations e) : q ∈ listAnnotations es := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ (ih he)

end GLang.ValueDependency
