import GLang.Proofs.Preservation.ValuePreservationV2

/-! Constructor shapes, without dimensions or basis-dependent witnesses.
These retain scalar/product structure that structural kinds intentionally erase. -/
namespace GLang.RuntimeValue

inductive ArrayForm where
  | empty | real | dynamic
  | dsum : ArrayForm → ArrayForm → ArrayForm
  | tprod : ArrayForm → ArrayForm → ArrayForm
  deriving DecidableEq, Repr

inductive TypeForm where
  | space : ArrayForm → TypeForm
  | piTy : TypeForm → TypeForm → TypeForm
  deriving DecidableEq, Repr

def sourceSpaceForm : Space → ArrayForm
  | .empty => .empty
  | .real => .real
  | .dual s => sourceSpaceForm s
  | .dsum s t => .dsum (sourceSpaceForm s) (sourceSpaceForm t)
  | .tprod s t => .tprod (sourceSpaceForm s) (sourceSpaceForm t)
  | .ker .. | .coker .. | .img .. | .coimg .. => .dynamic

def sourceTypeForm : Ty → TypeForm
  | .space s => .space (sourceSpaceForm s)
  | .piTy d c => .piTy (sourceTypeForm d) (sourceTypeForm c)

def spaceForm : ValSpace → ArrayForm
  | .empty => .empty
  | .real => .real
  | .dsum s t => .dsum (spaceForm s) (spaceForm t)
  | .tprod s t => .tprod (spaceForm s) (spaceForm t)
  | .ffs .. => .dynamic

def typeForm : ValTy → TypeForm
  | .space s => .space (spaceForm s)
  | .piTy d c => .piTy (typeForm d) (typeForm c)

@[simp] theorem sourceSpaceForm_open (s : Space) (k : Nat) (v : Term) :
    sourceSpaceForm (Space.openRec k v s) = sourceSpaceForm s := by
  induction s using Space.rec (motive_2 := fun _ => True) (motive_3 := fun _ => True) <;>
    simp_all [Space.openRec,sourceSpaceForm]

@[simp] theorem sourceTypeForm_open (t : Ty) (k : Nat) (v : Term) :
    sourceTypeForm (Ty.openRec k v t) = sourceTypeForm t := by
  cases t with
  | space s => simp [Ty.openRec,sourceTypeForm]
  | piTy d c => simp [Ty.openRec,sourceTypeForm,sourceTypeForm_open d,sourceTypeForm_open c]
termination_by t

@[simp] theorem spaceForm_open (s : ValSpace) (k : Nat) (v : ValExpr) :
    spaceForm (ValSpace.openRec k v s) = spaceForm s := by
  induction s using ValSpace.rec (motive_2 := fun _ => True) (motive_3 := fun _ => True) (motive_4 := fun _ => True) <;>
    first | trivial | (try simp_all [ValSpace.openRec,spaceForm])

@[simp] theorem typeForm_open (t : ValTy) (k : Nat) (v : ValExpr) :
    typeForm (ValTy.openRec k v t) = typeForm t := by
  cases t with
  | space s => simp [ValTy.openRec,typeForm]
  | piTy d c => simp [ValTy.openRec,typeForm,typeForm_open d,typeForm_open c]
termination_by t

/-- Inverting a constructor form recovers its literal syntactic constructor. -/
theorem typeForm_array {t : ValTy} {f : ArrayForm} (h : typeForm t = .space f) :
    ∃ s, t = .space s ∧ spaceForm s = f := by
  cases t <;> simp_all [typeForm]

theorem spaceForm_tensor {s : ValSpace} {a b : ArrayForm}
    (h : spaceForm s = .tprod a b) :
    ∃ s0 s1, s = .tprod s0 s1 ∧ spaceForm s0 = a ∧ spaceForm s1 = b := by
  cases s <;> simp_all [spaceForm]

theorem typeForm_tensor {t : ValTy} {a b : ArrayForm}
    (h : typeForm t = .space (.tprod a b)) :
    ∃ s0 s1, t = .space (.tprod s0 s1) ∧ spaceForm s0 = a ∧ spaceForm s1 = b := by
  obtain ⟨s,rfl,hs⟩ := typeForm_array h
  obtain ⟨s0,s1,rfl,h0,h1⟩ := spaceForm_tensor hs
  exact ⟨s0,s1,rfl,h0,h1⟩

theorem typeForm_real {t : ValTy} (h : typeForm t = .space .real) : t = .space .real := by
  obtain ⟨s,rfl,hs⟩ := typeForm_array h
  cases s <;> simp_all [spaceForm]

theorem of_cofinite {P : Prop} (L : Finset VName) (h : ∀ x, x ∉ L → P) : P := by
  obtain ⟨x,hx⟩ := Infinite.exists_notMem_finset L
  exact h x hx

/-- Evaluation of a space or type retains its constructor form. -/
theorem eval_forms :
    (∀ {Ψ s sv}, ValSpace.EvalS Ψ s sv → spaceForm sv = sourceSpaceForm s) ∧
    (∀ {Ψ t tv}, ValTy.EvalT Ψ t tv → typeForm tv = sourceTypeForm t) := by
  constructor
  all_goals
    intros Ψ s sv h
    refine h.rec
      (motive_1 := fun _ s sv _ => spaceForm sv = sourceSpaceForm s)
      (motive_2 := fun _ t tv _ => typeForm tv = sourceTypeForm t)
      (motive_3 := fun _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ => True)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros <;> first | trivial | simp_all [sourceSpaceForm,sourceTypeForm,spaceForm,typeForm,
    ValTy.openVar,Ty.openVar]
  all_goals exact of_cofinite _ (by assumption)

end GLang.RuntimeValue
