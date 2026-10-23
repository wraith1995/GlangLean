import GLang.Elaboration.ContextFormation

open GLang

example : Surface.HasType ∅ ∅
    (.app (.inner .real) (.real 2)) (.space (.dual .real)) :=
  .app_linear .real (.dual .real) (Finmap.disjoint_empty ∅)
    (.inner .real) (.real_lit 2)

example : Surface.SValid ∅ (.ker (.inner .real)) :=
  .ker .real (.dual .real) (.inner .real)

example : Surface.HasType ∅ ∅ (.pinv (.inner .real))
    (.space (.tprod (.dual (.dual .real)) .real)) :=
  .pinv_tensor .real (.dual .real) (.inner .real)

example : Surface.HasType ∅ ∅ (.llam .real (.bvar 0)) (.space (.dual .real)) := by
  apply Surface.HasType.llam_real ∅ .real
  intro y _
  simpa [Surface.Term.openVar, Surface.Term.openRec] using
    (Surface.HasType.var_lin (ε := ∅) (x := y) (s := .real))

example : Surface.Basis.BasisValid ∅
    (.proj (.ker (.inner .real)) .one (.dual .one)) :=
  .proj_ker .one (.dual .one rfl) rfl rfl ⟨.inner .real⟩

example : Surface.Basis.BasisValid ∅ (.frame .one .one) :=
  .frame ∅ .one (fun _ _ => .one)

-- Erasure must recurse through terms inside a projected basis.
example : (Basis.proj (.ker .real (.dual .real) (.inner .real))
    .one (.dual .one)).erase =
    Surface.Basis.proj (.ker (.inner .real)) .one (.dual .one) := rfl

-- Actual reconstruction witnesses for examples (not a general lifting theorem).
example : ∃ (e : Term), e.erase = Surface.Term.app (.inner .real) (.real 2) ∧
    Nonempty (HasType ∅ ∅ e (.space (.dual .real))) := by
  refine ⟨.appL .real (.dual .real) (.inner .real) (.real 2), rfl, ?_⟩
  exact ⟨.app_linear .real (.dual .real) (Finmap.disjoint_empty ∅)
    (.inner .real) (.real_lit 2)⟩

#print axioms GLang.SValid.toSurface
#print axioms GLang.TValid.toSurface
#print axioms GLang.SubType.toSurface
#print axioms GLang.HasType.toSurface
#print axioms GLang.Basis.BasisValid.toSurface
#print axioms GLang.InductiveCtxWF.toSurface
