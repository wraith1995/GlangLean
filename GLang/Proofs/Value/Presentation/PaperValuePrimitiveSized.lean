import GLang.Proofs.Value.Presentation.PaperValuePrimitiveExtensionality

/-! Every successful numerical clause allocates the inferred finite-array size.
No environment admissibility premise is needed: invalid operands produce errors.
This supplies the admissibility part of the numerical logical-relation step. -/
namespace GLang.PaperValueDomains

def SizedResult (n : Nat) : Except DimError ValValSem → Prop
  | .error _ => True
  | .ok (.array a) => a.length = n
  | .ok (.fn _ _) => False

private theorem sized_arrayOf (n : Nat) (f : Nat → ℝ) :
    SizedResult n (.ok (.arrayOf n f)) := by
  simp [SizedResult, ValValSem.arrayOf, FlatArray.ofFn]

private theorem sized_bindArray (n : Nat) (r : Except DimError ValValSem)
    (k : FlatArray → Except DimError ValValSem)
    (h : ∀ a, SizedResult n (k a)) :
    SizedResult n (ValValSem.bindArray r k) := by
  cases r with
  | error e => trivial
  | ok v => cases v <;> simp_all [ValValSem.bindArray, SizedResult]

private theorem sized_bindArrays (n : Nat) (r r' : Except DimError ValValSem)
    (k : FlatArray → FlatArray → Except DimError ValValSem)
    (h : ∀ a b, SizedResult n (k a b)) :
    SizedResult n (ValValSem.bindArrays r r' k) :=
  sized_bindArray _ _ _ fun a => sized_bindArray _ _ _ (h a)

private theorem sized_bindArrays3 (n : Nat) (r r' r'' : Except DimError ValValSem)
    (k : FlatArray → FlatArray → FlatArray → Except DimError ValValSem)
    (h : ∀ a b c, SizedResult n (k a b c)) :
    SizedResult n (ValValSem.bindArrays3 r r' r'' k) :=
  sized_bindArray _ _ _ fun a => sized_bindArray _ _ _ fun b =>
    sized_bindArray _ _ _ (h a b)

theorem arrayPrimitive_sized (orc : FFSOracleSem) (w : World) (e : ValExpr)
    (hp : ArrayPrimitive e) :
    SizedResult (ValSpace.dof (orc w.env w.types w.values)
      (ValExpr.inferSpaceCtx w.types e))
      (denotValB_semS orc w.env w.types w.values e) := by
  cases e <;> simp only [ArrayPrimitive] at hp
  all_goals rw [denotValB_semS]
  all_goals first
    | apply sized_bindArrays3; intro a b c
    | apply sized_bindArrays; intro a b
    | apply sized_bindArray; intro a
    | skip
  all_goals repeat' first
    | exact sized_arrayOf _ _
    | exact True.intro
    | split
    | dsimp only
  all_goals simp_all [SizedResult, ValueCanonicalFSV.ResultMatrix.flatten,
    ValExpr.inferSpaceCtx]

/-- Exact sizes and equal numerical results give the full base logical relation.
The result space may be supplied by the caller's typing derivation. -/
theorem arrayPrimitive_related_of_eval_eq (orc : FFSOracleSem) (w w' : World)
    (e : ValExpr) (s : ValSpace) (hp : ArrayPrimitive e)
    (hs : ValSpace.dof (orc w.env w.types w.values)
      (ValExpr.inferSpaceCtx w.types e) = ValSpace.dof (orc w.env w.types w.values) s)
    (hs' : ValSpace.dof (orc w'.env w'.types w'.values)
      (ValExpr.inferSpaceCtx w'.types e) = ValSpace.dof (orc w'.env w'.types w'.values) s)
    (heq : denotValB_semS orc w.env w.types w.values e =
      denotValB_semS orc w'.env w'.types w'.values e) :
    PartialRel (RuntimeRelated orc (.space s) w w')
      (denotValB_semS orc w.env w.types w.values e)
      (denotValB_semS orc w'.env w'.types w'.values e) := by
  have h := arrayPrimitive_sized orc w e hp
  have h' := arrayPrimitive_sized orc w' e hp
  rw [hs] at h
  rw [hs'] at h'
  rw [← heq] at h' ⊢
  cases he : denotValB_semS orc w.env w.types w.values e <;> simp only [he, SizedResult] at h h' ⊢
  case error err => rfl
  case ok v =>
    cases v <;> simp only at h h'
    exact ⟨rfl, h, h'⟩

end GLang.PaperValueDomains
