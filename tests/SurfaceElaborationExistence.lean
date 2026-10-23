import GLang.Elaboration.Bases

open GLang GLang.SurfaceElaboration

-- These use actual proved existence, not an assumed Goals record.
example : Goals := complete

private def mapSpace : Surface.Space := .tprod (.dual .real) .real
private def dependentType : Surface.Ty :=
  .piTy (.space mapSpace) (.space (.ker (.bvar 0)))
private def dependentTerm : Surface.Term :=
  .nllam (.space mapSpace) (.zero (.ker (.bvar 0)))

private def dependentKind : Surface.TValid ∅ dependentType (.arrow .base .base) := by
  refine .piTy ∅ (.space (.tprod (.dual .real) .real)) ?_
  intro x hx
  change Surface.TValid (Finmap.insert x (.space mapSpace) ∅)
    (.space (.ker (.var x))) .base
  exact .space (.ker .real .real (.var_nlin (by simp [mapSpace])))

private def dependentTyped : Surface.HasType ∅ ∅ dependentTerm dependentType := by
  refine .nllam ∅ dependentKind ?_
  intro x hx
  change Surface.HasType ∅ (Finmap.insert x (.space mapSpace) ∅)
    (.zero (.ker (.var x))) (.space (.ker (.var x)))
  exact .zero (.ker .real .real (.var_nlin (by simp [mapSpace])))

-- Dependent type annotations are reconstructed beneath the nonlinear binder.
example : ∃ p, TermLift ∅ ∅ dependentTerm dependentType p :=
  termExists InductiveCtxWF.empty dependentTyped

-- Nonlinear application must align inferred annotations before substitution.
example : ∃ p, TermLift ∅ ∅ (.app dependentTerm (.zero mapSpace))
    (.space (.ker (.zero mapSpace))) p := by
  apply termExists InductiveCtxWF.empty
  exact Surface.HasType.app_nonlinear dependentTyped
    (.zero (.tprod (.dual .real) .real))

-- The entirely surface-facing endpoint also reconstructs the context.
example : ∃ (D : LCtx) (E : NLCtx) (e : Term) (T : Ty),
    D.erase = ∅ ∧ E.erase = ∅ ∧ InductiveCtxWF D E ∧
    e.erase = dependentTerm ∧ T.erase = dependentType ∧ Nonempty (HasType D E e T) :=
  typing Surface.InductiveCtxWF.empty dependentTyped

-- Genuine surface promotion is accepted without asking callers for internal
-- freshness of erased implementation annotations.
example (x : Name) : ∃ p, TermLift ∅ (Finmap.singleton x (.space .real))
    (.var x) (.space .real) p := by
  have hw : InductiveCtxWF ∅ (Finmap.singleton x (.space .real)) := by
    simpa using InductiveCtxWF.nonlinear InductiveCtxWF.empty
      Finmap.notMem_empty Finmap.notMem_empty (by simp [Ty.fv,Space.fv]) (TValid.space .real)
  apply termExists hw
  have hf : Surface.PromoteFresh (Finmap.singleton x .real) ∅ ∅ := by
    constructor
    · intro y hy z s hs; simp at hs
    · intro y hy z s hs
      have hz : z = x := by simpa using Finmap.mem_of_lookup_eq_some hs
      subst z
      simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at hs
      subst s
      simp [Surface.Space.fv]
    · intro y hy z t ht; simp at ht
  have hp := Surface.HasType.promote (ε' := ∅) (Δ := ∅)
    (Finmap.singleton x .real) (by intro y hy hn; exact Finmap.notMem_empty hn)
    (by intro y hy hn; exact Finmap.notMem_empty hn) hf
    (by simpa using (Surface.HasType.var_lin (ε := ∅) (x := x) (s := .real)))
  convert hp using 1

-- All four projected-space forms and basis lists share inferred annotations.
example : ∃ B, BasisLift ∅ (.proj (.ker (.inner .real)) .one (.dual .one)) B :=
  basisExists InductiveCtxWF.empty
    (.proj_ker .one (.dual .one rfl) rfl rfl ⟨.inner .real⟩)

example : ∃ B, BasisLift ∅ (.terms [.real 1, .real 2] .one) B := by
  apply basisExists InductiveCtxWF.empty
  refine .terms .one rfl ⟨.real⟩ ?_ (by simp)
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> exact ⟨.real_lit _⟩

example : ∃ B, BasisLift ∅ (.frame .one .one) B :=
  basisExists InductiveCtxWF.empty
    (.frame ∅ .one (fun _ _ => .one))

-- A frame whose projected basis actually depends on its bound map.
example : ∃ B, BasisLift ∅
    (.frame (.tprod (.dual .one) .one)
      (.proj (.ker (.bvar 0)) .one .one)) B := by
  apply basisExists InductiveCtxWF.empty
  refine .frame ∅ (.tprod (.dual .one rfl) .one rfl rfl) ?_
  intro x hx
  change Surface.Basis.BasisValid (Finmap.insert x (.space mapSpace) ∅)
    (.proj (.ker (.var x)) .one .one)
  exact .proj_ker .one .one rfl rfl ⟨.var_nlin (by simp [mapSpace,Surface.Basis.sof])⟩

-- Both linear-lambda result representations are reconstructed.
example : ∃ p, TermLift ∅ ∅ (.llam .real (.bvar 0)) (.space (.dual .real)) p := by
  apply termExists InductiveCtxWF.empty
  apply Surface.HasType.llam_real ∅ .real
  intro y hy
  simpa [Surface.Term.openVar,Surface.Term.openRec] using
    (Surface.HasType.var_lin (ε := ∅) (x := y) (s := .real))

example : ∃ p, TermLift ∅ ∅ (.llam mapSpace (.bvar 0))
    (.space (.tprod (.dual mapSpace) mapSpace)) p := by
  apply termExists InductiveCtxWF.empty
  apply Surface.HasType.llam_tensor ∅ (by simp)
    (.tprod (.dual .real) .real) (.tprod (.dual .real) .real)
  intro y hy
  simpa [Surface.Term.openVar,Surface.Term.openRec] using
    (Surface.HasType.var_lin (ε := ∅) (x := y) (s := mapSpace))

#print axioms complete
#print axioms typing
#print axioms termExists
#print axioms spaceExists
#print axioms typeExists
#print axioms subspaceExists
#print axioms basisExists
#print axioms contextExists
