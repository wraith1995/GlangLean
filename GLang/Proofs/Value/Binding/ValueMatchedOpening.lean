import GLang.Proofs.Value.Typing.ValueMatchedClosure
import GLang.Proofs.Value.Queries.ValueDependencyOpening

namespace GLang.ValueDependency

/-- Finite set of names inside every annotation. Binder proofs avoid this
support as well as the free names of the body and stored context declarations. -/
def annotationSupport : List (VName × ValTy) → Finset VName
  | [] => ∅
  | p :: ps => p.2.fv ∪ annotationSupport ps

theorem annotationSupport_fresh {xs : List (VName × ValTy)} {x y : VName} {a : ValTy}
    (hx : x ∉ annotationSupport xs) (ha : (y, a) ∈ xs) : x ∉ a.fv := by
  induction xs with
  | nil => simp at ha
  | cons p ps ih =>
    simp only [annotationSupport, Finset.mem_union, not_or] at hx
    rcases List.mem_cons.mp ha with heq | hm
    · cases heq; exact hx.1
    · exact ih hx.2 hm

/-- Matched declaration closure survives a fresh binder opening. The inverse
occurrence premise is purely syntactic and supplied by the proved open lemmas. -/
theorem matchedAnnotations_opening (ε : ValCtx) (xs ys : List (VName × ValTy))
    (x : VName) (d : ValTy)
    (hinverse : ∀ y a, (y, a) ∈ ys →
      (∃ b j, (y, b) ∈ xs ∧ a = ValTy.openRec j (.var x d) b) ∨
        (y, a) ∈ exprAnnotations (.var x d))
    (hbody : MatchedAnnotationsClosed ε xs)
    (hdom : MatchedAnnotationsClosed ε (typeAnnotations d)) (hd : ValTy.lc d)
    (hname : ∀ y a, (y, a) ∈ xs → y ≠ x)
    (hann : x ∉ annotationSupport xs) (hdfresh : x ∉ d.fv)
    (hstored : ∀ y a, ε.lookup y = some a → x ∉ a.fv) :
    MatchedAnnotationsClosed (Finmap.insert x d ε) ys := by
  intro y a hya hlookup
  rcases hinverse y a hya with ⟨b, j, hb, hab⟩ | hu
  · have hyx := hname y b hb
    rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
    have hba := opened_annotation_eq x d b a j
      (annotationSupport_fresh hann hb) (hstored _ _ hlookup) hab.symm
    subst b
    exact hbody y a hb hlookup
  · simp only [exprAnnotations, List.mem_cons, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl⟩ | hu
    · exact hd
    · have hy : y ∈ d.fv := by
        rw [typeAnnotations_fv]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(y, a), hu, rfl⟩)
      have hyx : y ≠ x := by intro heq; subst y; exact hdfresh hy
      rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
      exact hdom y a hu hlookup

 theorem matched_type_open (ε : ValCtx) (t d : ValTy) (x : VName) (k : Nat)
    (hbody : MatchedAnnotationsClosed ε (typeAnnotations t))
    (hdom : MatchedAnnotationsClosed ε (typeAnnotations d)) (hd : ValTy.lc d)
    (hfree : x ∉ t.fv) (hann : x ∉ annotationSupport (typeAnnotations t))
    (hdfresh : x ∉ d.fv)
    (hstored : ∀ y a, ε.lookup y = some a → x ∉ a.fv) :
    MatchedAnnotationsClosed (Finmap.insert x d ε)
      (typeAnnotations (ValTy.openRec k (.var x d) t)) := by
  apply matchedAnnotations_opening ε _ _ x d
    (fun y a h => typeAnnotations_open_inverse t y a k (.var x d) h)
    hbody hdom hd ?_ hann hdfresh hstored
  intro y a ha heq
  subst y
  apply hfree
  rw [typeAnnotations_fv]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(x, a), ha, rfl⟩)

 theorem matched_expr_open (ε : ValCtx) (e : ValExpr) (d : ValTy) (x : VName) (k : Nat)
    (hbody : MatchedAnnotationsClosed ε (exprAnnotations e))
    (hdom : MatchedAnnotationsClosed ε (typeAnnotations d)) (hd : ValTy.lc d)
    (hfree : x ∉ e.fv) (hann : x ∉ annotationSupport (exprAnnotations e))
    (hdfresh : x ∉ d.fv)
    (hstored : ∀ y a, ε.lookup y = some a → x ∉ a.fv) :
    MatchedAnnotationsClosed (Finmap.insert x d ε)
      (exprAnnotations (ValExpr.openRec k (.var x d) e)) := by
  apply matchedAnnotations_opening ε _ _ x d
    (fun y a h => exprAnnotations_open_inverse e y a k (.var x d) h)
    hbody hdom hd ?_ hann hdfresh hstored
  intro y a ha heq
  subst y
  apply hfree
  rw [exprAnnotations_fv]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(x, a), ha, rfl⟩)

end GLang.ValueDependency
