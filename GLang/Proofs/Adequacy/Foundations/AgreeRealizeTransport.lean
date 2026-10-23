import GLang.Proofs.Adequacy.Foundations.GlobalProps
import GLang.Proofs.Adequacy.Foundations.Erasure
import GLang.Proofs.Preservation.EvalTKind
import GLang.Proofs.Preservation.PreservationV2Helpers
import GLang.Proofs.Value.Soundness.ValueSoundnessSem

namespace GLang

/-- Context-free valid value types at the same kind have the same `.space`/`.piTy`
    skeleton.  The cofinite codomain premises are compared at one common fresh
    name, then `openRec` is erased because it preserves the skeleton. -/
theorem ValTValidC.sameShape_of_sameKind (k : ValKind) :
    ∀ {τv τv' : ValTy}, ValTValidC τv k → ValTValidC τv' k →
      ValSoundOfDenot.ValTy.SameShape τv τv' := by
  induction k with
  | base =>
      intro τv τv' h h'
      cases h
      cases h'
      trivial
  | arrow k₀ k₁ ih₀ ih₁ =>
      intro τv τv' h h'
      cases h with
      | piTy L h₀ h₁ =>
        cases h' with
        | piTy L' h₀' h₁' =>
          refine ⟨ih₀ h₀ h₀', ?_⟩
          obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ L')
          rw [Finset.mem_union, not_or] at hx
          have hopen := ih₁ (h₁ x hx.1) (h₁' x hx.2)
          exact
            ((ValSoundOfDenot.ValTy.SameShape_openRec 0 (.var x _) _).symm.trans hopen).trans
              (ValSoundOfDenot.ValTy.SameShape_openRec 0 (.var x _) _)

/-- Any two strengthened realizations of one source type, even at different
    source/evaluation contexts, have the same value-type skeleton. -/
theorem S.Ty.sameShape {Γ Γ' : NLCtx} {Ψ Ψ' : EvalCtx} {τ : GLang.Ty} {τv τv' : ValTy}
    (h : S.Ty Γ Ψ τ τv) (h' : S.Ty Γ' Ψ' τ τv') :
    ValSoundOfDenot.ValTy.SameShape τv τv' := by
  have hk : τv.structuralKind = τv'.structuralKind := by
    rw [h.toEvalT.structuralKind_eq_sourceKind, h'.toEvalT.structuralKind_eq_sourceKind]
  exact ValTValidC.sameShape_of_sameKind _ (evalT_valid h.toEvalT).some
    (hk ▸ (evalT_valid h'.toEvalT).some)

end GLang
