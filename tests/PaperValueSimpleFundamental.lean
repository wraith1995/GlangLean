import GLang.Proofs.Value.Presentation.PaperValueSimpleFundamental
open GLang GLang.PaperValueDomains
namespace SimpleFundamentalTests

def real : SimpleTy := .space .real
def empty : SimpleTy := .space .empty

def identity (t : SimpleTy) : ValExpr := .vlam t.toValTy t.toValTy (.bvar 0)

theorem identity_typed (ε : VName → SimpleTy) (Γ : List SimpleTy) (t : SimpleTy) :
    SimpleHasType ε Γ (identity t) (.arrow t t) :=
  .lam (.bvar rfl)

def higherOrderApplication : ValExpr :=
  .appV (identity (.arrow real real)) (identity real)

theorem higherOrderApplication_typed (ε : VName → SimpleTy) (Γ : List SimpleTy) :
    SimpleHasType ε Γ higherOrderApplication (.arrow real real) :=
  .app (identity_typed ε Γ (.arrow real real)) (identity_typed ε Γ real)

theorem higherOrderReshape_typed (ε : VName → SimpleTy) (Γ : List SimpleTy) :
    SimpleHasType ε Γ
      (.reshap higherOrderApplication (SimpleTy.arrow empty empty).toValTy
        (SimpleTy.arrow real real).toValTy) (.arrow empty empty) :=
  .reshape rfl (higherOrderApplication_typed ε Γ)

example (ε : VName → SimpleTy) (orc : FFSOracleSem) (w w' : World)
    (hw : w.types = []) (hw' : w'.types = [])
    (henv : SimpleNamedRelated ε w.env w'.env) :
    PartialRel (SimpleTy.arrow real real).per.rel
      ((SimpleTy.arrow real real).interpret orc w higherOrderApplication)
      ((SimpleTy.arrow real real).interpret orc w' higherOrderApplication) :=
  (higherOrderApplication_typed ε []).interpret_related orc w w' hw hw' henv
    (by intro n t hn; simp at hn)

-- A fixed-shape primitive can fail: a one-element index space has no summands.
def missingSummand : ValExpr := .vsum .real []

theorem missingSummand_typed (ε : VName → SimpleTy) (Γ : List SimpleTy) :
    SimpleHasType ε Γ missingSummand empty := by
  apply SimpleHasType.primitive (fun _ => SimpleSpace.empty)
  · trivial
  · rfl
  · rfl
  · intro q hq
    simp only [primitiveQuerySpaces, primitiveInputSpaces, missingSummand,
      ValExpr.inferSpaceCtx, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨.empty,rfl⟩
    · exact ⟨.real,rfl⟩
  · intro a ha
    simp [missingSummand, primitiveOperands] at ha

theorem missingSummand_errors (orc : FFSOracleSem) (w : World) :
    denotValB_semS orc w.env w.types w.values missingSummand = .error .mismatch := by
  simp [missingSummand, denotValB_semS, ValSpace.dof_real]

-- Argument failure propagates through actual checked application.
example (orc : FFSOracleSem) (w : World) :
    denotValB_semS orc w.env w.types w.values
      (.appV (identity empty) missingSummand) = .error .mismatch := by
  rw [denotValB_semS.eq_28, missingSummand_errors]
  simp [identity, denotValB_semS]

-- Named values need only their relational contract, not literal callback equality.
example (ε : VName → SimpleTy) (x : VName) (orc : FFSOracleSem) (w w' : World)
    (hw : w.types = []) (hw' : w'.types = [])
    (henv : SimpleNamedRelated ε w.env w'.env) :
    PartialRel (ε x).runtimeRel
      (denotValB_semS orc w.env w.types w.values (.var x (ε x).toValTy))
      (denotValB_semS orc w'.env w'.types w'.values (.var x (ε x).toValTy)) :=
  (SimpleHasType.var [] x).eval_related orc w w' hw hw' henv
    (by intro n t hn; simp at hn)

open Lean Elab Command
elab "check_simple_correspondence_axioms" : command => do
  let foundations := #[``propext, ``Classical.choice, ``Quot.sound]
  let generic := [``SimpleTy.related_iff, ``SimpleTy.related_trans,
    ``SimpleTy.runtimeRelated_iff, ``SimpleTy.runtimeRelated_world_irrel]
  let live := [``SimpleHasType.eval_runtime_related, ``SimpleHasType.interpret_related,
    ``SimpleHasType.interpretClass_eq, ``missingSummand_errors]
  for n in generic ++ live do
    unless (← getConstInfo n) matches .thmInfo _ do
      throwError "Expected a theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless foundations.contains ax || (live.contains n && ax == ``GLang.Matrix.exists_gsvd) do
        throwError "Unexpected simple correspondence axiom in {n}: {ax}"
  logInfo "Simple domain bridges use foundations; evaluated correspondence uses at most existing GSVD existence."
check_simple_correspondence_axioms
end SimpleFundamentalTests
