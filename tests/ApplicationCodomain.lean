import GLang.Proofs.Preservation.ApplicationCodomain

/-! The derived application rules must remain free of project axioms. -/
#print axioms GLang.Operational.applicationCodomain_of_typing
#print axioms GLang.Operational.Unchecked.OpStep.appN_of_typing
#print axioms GLang.Operational.Term.appN_of_history

namespace GLang

/-- A codomain realization determines the result type of application. -/
example {Psi : EvalCtx} {tau0 tau1 : ValTy} :
    ¬ ValTy.EvalT Psi (.space .real) (.piTy tau0 tau1) := by
  intro h
  cases h

end GLang

namespace GLang.ApplicationConstructionTest

open RawCertifiedOperational

private abbrev delta : LCtx := Finmap.insert "linear" .real ∅
private noncomputable abbrev psi : EvalCtx := (∅ : EvalCtx).extend "linear" .one (.rlit 0)

private def history : V2.CtxTele delta ∅ psi :=
  .extend_lin .empty ⟨Finmap.notMem_empty, Finmap.notMem_empty⟩
    (V2.EvalEntryCreation.ofSpace
      ⟨.space .real, by simp [ValExpr.fv], .rlit⟩ rfl) .one rfl

private def functionTyped : HasType ∅ ∅
    (.nllam (.space .real) (.real 1)) (.piTy (.space .real) (.space .real)) :=
  .nllam ∅ (.piTy ∅ (.space .real) (fun _ _ => .space .real))
    (fun _ _ => .real_lit 1)

private def frameValid : Basis.BasisValid (∅ : NLCtx) (.frame .one .one) :=
  .frame ∅ .one (fun _ _ => .one)

private def functionStep : Operational.Term ∅ ∅ psi
    (.nllam (.space .real) (.real 1)) (.frame .one .one)
    (.vlam (.space .real) (.space .real)
      (.reshap (.rlit 1) (.space .real) (.space .real)))
    (.piTy (.space .real) (.space .real)) :=
  .nllam rfl rfl ⟨functionTyped⟩ frameValid
    (.frame frameValid (.space rfl .one .real) ∅
      (fun _ _ => .space rfl .one .real))
    (.space rfl .one .real) ∅
    (fun _ _ => .rlit 1 ⟨.real_lit 1⟩ (.space rfl .one .real))
    (fun _ _ => .space rfl .one .real)

private def argumentStep : Operational.Term ∅ ∅ psi (.real 2) .one
    (.rlit 2) (.space .real) :=
  .rlit 2 ⟨.real_lit 2⟩ (.space rfl .one .real)

/-- Application in a nonempty linear operational context. -/
noncomputable def checkedResult :=
  Operational.Term.appN history functionStep argumentStep

noncomputable def ordinaryResult :=
  Operational.Unchecked.OpStep.appN history frameValid (.real_lit 2)
    functionStep.toUnchecked argumentStep.toUnchecked

example : "linear" ∈ delta := Finmap.mem_insert.mpr (Or.inl rfl)

example : Operational.Term ∅ ∅ psi
    (.appN (.nllam (.space .real) (.real 1)) (.real 2)) .one
    checkedResult.value checkedResult.resultType :=
  checkedResult.derivation

#print axioms Operational.Term.appN
#print axioms Operational.Unchecked.OpStep.appN

end GLang.ApplicationConstructionTest
