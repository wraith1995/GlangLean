import GLang.Public.PaperSurfaceResults

open GLang GLang.SurfaceElaboration GLang.PaperSurfaceResults

-- All four projected bases reconstruct uniquely from independent surface
-- derivations, without requiring an internal map or basis as an input.
example (hw : InductiveCtxWF Δ ε)
    (ha : Surface.Basis.BasisValid ε.erase a)
    (hb : Surface.Basis.BasisValid ε.erase b)
    (hta : a.tof = .space s) (htb : b.tof = .space t)
    (he : Surface.HasType ∅ ε.erase e (.space (.tprod (.dual s) t))) :
    (∃! B, BasisLift ε (.proj (.ker e) a b) B) ∧
    (∃! B, BasisLift ε (.proj (.coker e) a b) B) ∧
    (∃! B, BasisLift ε (.proj (.img e) a b) B) ∧
    (∃! B, BasisLift ε (.proj (.coimg e) a b) B) :=
  ⟨basisElaborationUnique hw (.proj_ker ha hb hta htb ⟨he⟩),
   basisElaborationUnique hw (.proj_coker ha hb hta htb ⟨he⟩),
   basisElaborationUnique hw (.proj_img ha hb hta htb ⟨he⟩),
   basisElaborationUnique hw (.proj_coimg ha hb hta htb ⟨he⟩)⟩

-- A genuinely dependent frame: its fiber is the kernel of its bound map.
private def frame : Surface.Basis :=
  .frame (.tprod (.dual .one) .one) (.proj (.ker (.bvar 0)) .one .one)

private theorem frameValid : Surface.Basis.BasisValid ∅ frame := by
  refine .frame ∅ (.tprod (.dual .one rfl) .one rfl rfl) ?_
  intro x _
  change Surface.Basis.BasisValid
    (Finmap.insert x (.space (.tprod (.dual .real) .real)) ∅)
    (.proj (.ker (.var x)) .one .one)
  exact .proj_ker .one .one rfl rfl ⟨.var_nlin (by simp [Surface.Basis.sof])⟩

example : ∃! B, BasisLift ∅ frame B :=
  basisElaborationUnique InductiveCtxWF.empty frameValid

-- No annotated context or separate frame-type-validity premise is supplied.
example : ∃ D E, D.erase = ∅ ∧ E.erase = ∅ ∧ InductiveCtxWF D E ∧
    ∃! B, BasisLift E frame B :=
  basisValidityUnique Surface.InductiveCtxWF.empty frameValid

example (h : Surface.Basis.BasisValid g (.terms [] b)) : False := by
  cases h with | terms _ _ _ _ hn => exact hn rfl

-- Space-only basis operations do not accept a dependent frame.
example (h : Surface.Basis.BasisValid g (.dual (.frame a b))) : False := by
  cases h with | dual _ ht => cases ht

-- Free variables and substitution act on inferred annotations, not the raw
-- visible spelling. These equalities cover any two valid reconstructions.
example (hA : BasisLift ε b A) (hB : BasisLift ε b B) (x : Name) (u : Term) :
    Basis.fv A = Basis.fv B ∧ Basis.subst x u A = Basis.subst x u B := by
  have he := basisLift_unique hA hB
  exact ⟨congrArg Basis.fv he, congrArg (Basis.subst x u) he⟩

example (hw : InductiveCtxWF Δ ε) (ha : TermLift Δ ε e t a)
    (hb : TermLift Δ ε e t b) (x : Name) (u : Term) :
    Term.fv a.1 = Term.fv b.1 ∧ Term.subst x u a.1 = Term.subst x u b.1 := by
  have he := congrArg Prod.fst (termLift_unique hw ha hb)
  exact ⟨congrArg Term.fv he, congrArg (Term.subst x u) he⟩

example (ha : SpaceLift ε s a) (hb : SpaceLift ε s b) (x : Name) (u : Term) :
    Space.fv a = Space.fv b ∧ Space.subst x u a = Space.subst x u b := by
  have he := spaceLift_unique ha hb
  exact ⟨congrArg Space.fv he, congrArg (Space.subst x u) he⟩

example (ha : TypeLift ε t k a) (hb : TypeLift ε t k b) (x : Name) (u : Term) :
    Ty.fv a = Ty.fv b ∧ Ty.subst x u a = Ty.subst x u b := by
  have he := typeLift_unique ha hb
  exact ⟨congrArg Ty.fv he, congrArg (Ty.subst x u) he⟩

-- The map m occurs only in the application's inferred domain annotation.
private def dependentSpace : Space := .ker .real .real (.var "m")
private def hiddenDependency : Term := .appL dependentSpace .real (.var "f") (.var "x")
private def context : NLCtx :=
  Finmap.insert "x" (.space dependentSpace)
    (Finmap.insert "f" (.space (.tprod (.dual dependentSpace) .real))
      (Finmap.singleton "m" (.space (.tprod (.dual .real) .real))))

private theorem contextWF : InductiveCtxWF ∅ context := by
  have hm : InductiveCtxWF ∅
      (Finmap.singleton "m" (.space (.tprod (.dual .real) .real))) := by
    simpa using InductiveCtxWF.nonlinear (x := "m") InductiveCtxWF.empty
      Finmap.notMem_empty Finmap.notMem_empty (by simp [Ty.fv, Space.fv])
      (TValid.space (.tprod (.dual .real) .real))
  have hs : SValid (Finmap.singleton "m" (.space (.tprod (.dual .real) .real)))
      dependentSpace := .ker .real .real (.var_nlin (by simp))
  have hf := InductiveCtxWF.nonlinear (x := "f") hm Finmap.notMem_empty (by simp)
    (by intro y hy; simpa [Ty.fv, Space.fv, Term.fv, dependentSpace] using hy)
    (TValid.space (.tprod (.dual hs) .real))
  exact InductiveCtxWF.nonlinear hf Finmap.notMem_empty (by simp)
    (by intro y hy; simp [Ty.fv, Space.fv, Term.fv, dependentSpace] at hy; simp [hy])
    (TValid.space (.ker .real .real (.var_nlin (by simp))))

private def hiddenTyped : HasType ∅ context hiddenDependency (.space .real) := by
  have hs : SValid context dependentSpace :=
    .ker .real .real (.var_nlin (by simp [context]))
  exact .app_linear hs .real (Finmap.disjoint_empty ∅)
    (.var_nlin (by simp [context])) (.var_nlin (by simp [context]))

example : "m" ∈ Term.fv hiddenDependency ∧ "m" ∉ hiddenDependency.erase.fv := by
  simp [hiddenDependency, dependentSpace, Term.fv, Space.fv,
    Term.erase, Surface.Term.fv]

-- Every other valid reconstruction includes that hidden dependency as well.
example (h : HasType ∅ context e T) (he : e.erase = hiddenDependency.erase) :
    "m" ∈ Term.fv e := by
  have hh := HasType.annotation_unique contextWF h hiddenTyped he
  rw [hh.1]
  simp [hiddenDependency, dependentSpace, Term.fv, Space.fv]

-- Substituting m changes an inferred annotation even though the visible term
-- remains f(x). Dropping the annotation before substitution loses this effect.
example :
    Term.subst "m" (.zero (.tprod (.dual .real) .real)) hiddenDependency ≠ hiddenDependency ∧
    (Term.subst "m" (.zero (.tprod (.dual .real) .real)) hiddenDependency).erase =
      hiddenDependency.erase := by
  simp [hiddenDependency, dependentSpace, Term.subst, Space.subst, Term.erase]

-- Basis substitution also traverses a frame body and a term basis's fallback.
example (x : Name) (u : Term) (a b : Basis) (s : Space) (es : List Term) :
    (Basis.subst x u (.frame a (.terms s es b))).erase =
      Surface.Basis.subst x u.erase (.frame a.erase (.terms (es.map Term.erase) b.erase)) :=
  Basis.erase_subst _ _ _

open Lean Elab Command in
elab "check_frozen_surface_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``spaceElaborationUnique, ``typeElaborationUnique,
      ``subspaceElaborationUnique, ``termElaborationUnique,
      ``basisElaborationUnique, ``basisValidityUnique, ``basisDenotation_eq,
      ``Basis.erase_subst, ``SurfaceElaboration.complete] do
    for ax in ← Lean.collectAxioms decl do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo "Frozen-paper source/basis reconstruction: foundations only."

check_frozen_surface_axioms
