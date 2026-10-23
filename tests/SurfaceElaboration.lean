import GLang.Elaboration.Elaboration
import GLang.Elaboration.Supporting.SurfaceClosing

/-! Signature and uniqueness/closing regressions.
`SurfaceElaborationExistence.lean` exercises the complete existence proof. -/
open GLang GLang.SurfaceElaboration

#check SpaceExists
#check TypeExists
#check SubspaceExists
#check TermExists
#check BasisExists
#check ContextExists

example : TermLift ∅ ∅ (.app (.inner .real) (.real 2)) (.space (.dual .real))
    (.appL .real (.dual .real) (.inner .real) (.real 2), .space (.dual .real)) := by
  refine ⟨rfl, rfl, ⟨?_⟩⟩
  simpa using HasType.app_linear (.real) (.dual .real)
    (show Finmap.Disjoint (∅ : LCtx) ∅ from fun _ hx => (Finmap.notMem_empty hx).elim)
    (HasType.inner SValid.real) (HasType.real_lit 2)

-- Exact basis uniqueness covers dependent frames, not just base-space bases.
example {ε b c : Basis} {Γ : NLCtx}
    (h : Basis.BasisValid Γ (.frame ε b))
    (h' : Basis.BasisValid Γ (.frame ε c))
    (he : b.erase = c.erase) : b = c := by
  have hh := Basis.BasisValid.annotation_unique h h'
    (by simp only [Basis.erase, he])
  exact (Basis.frame.inj hh).2

-- One lifted opening determines a body with exactly the original erasure.
example {e : Surface.Term} {a : Term} {x : Name}
    (hx : x ∉ e.fv) (ha : a.erase = e.openVar x) :
    (Term.closeRec 0 x a).erase = e := Term.erase_close_of_open hx ha

example {b : Surface.Basis} {a : Basis} {x : Name}
    (hx : x ∉ b.fv) (ha : a.erase = b.openVar x) :
    (Basis.closeRec 0 x a).erase = b := Basis.erase_close_of_open hx ha

example (hs : SpaceExists) (ht : TypeExists) : ContextExists :=
  context_of_formation hs ht

#print axioms Basis.BasisValid.annotation_unique
#print axioms context_of_formation
#print axioms goals_of_judgments
#print axioms spaceLift_unique
#print axioms typeLift_unique
#print axioms subspaceLift_unique
#print axioms termLift_unique
#print axioms basisLift_unique
#print axioms Term.erase_close_of_open
#print axioms Ty.erase_close_of_open
#print axioms Basis.erase_close_of_open
