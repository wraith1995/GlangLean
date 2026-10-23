import GLang.Proofs.Value.Presentation.PaperValueRecursiveCorrespondence
import GLang.Proofs.Value.Runtime.RuntimeValueQueryFinite
import GLang.Proofs.Value.Runtime.RuntimeValueEmbedding
import Lean

open GLang
namespace GLang.PaperValueGapAudit
noncomputable section

def badMatrix : ValExpr := .mtm 1 1 .empty .real
  (.zero (.tprod .real .real)) (.zero (.tprod .real .real))

def badMatrix_typed : ValHasType ∅ badMatrix (.space (.tprod .real .real)) :=
  .mtm .empty .real (.zero (.tprod .real .real)) (.zero (.tprod .real .real))

theorem badMatrix_fails (ρ : ValEnvSem) :
    denotValB_semS directOracle ρ [] [] badMatrix = .error .mismatch := by
  simp [badMatrix, denotValB_semS, ValValSem.bindArrays, ValValSem.bindArray, ValValSem.arrayOf, ValueShape.mtm,
    ValExpr.inferSpaceCtx]

theorem failed_witness_rank_zero (ρ : ValEnvSem) :
    ffsOperandRank directOracle ρ [] [] (.tprod .real .real) badMatrix = 0 := by
  simp [ffsOperandRank, badMatrix_fails]

theorem failed_witness_kernel_dimension (ρ : ValEnvSem) :
    directOracle ρ [] [] .kernel (.tprod .real .real) badMatrix = 1 := by
  have hv : RuntimeValue.ValCtxValid (∅ : ValCtx) := by
    intro x t h
    simp at h
  have hfinite := RuntimeValue.validSpace_queryFinite hv
    (RuntimeValue.ValSValid.ffs (p := .kernel) .real .real badMatrix_typed.runtime)
  rw [directOracle_spec.rank ρ .kernel (.tprod .real .real) badMatrix (by rfl) hfinite]
  simp [failed_witness_rank_zero, ffsDim]

def illTypedStored : ValExpr := .scale (.zero (.tprod .real .real)) (.rlit 0)

theorem illTypedStored_not_typed (ε : ValCtx) (τ : ValTy) :
    ¬ Nonempty (ValHasType ε illTypedStored τ) := by
  rintro ⟨h⟩
  cases h with
  | scale h0 _ => cases h0

def illTypedStored_entry : V2.EvalEntryCreation ∅ "bad" .one illTypedStored :=
  V2.EvalEntryCreation.ofSpace
    ⟨.space .real, by simp [illTypedStored, ValExpr.fv, ValSpace.fv],
      .scale (.zero (.tprod .real .real)) .rlit⟩ rfl

theorem illTypedStored_history :
    V2.CtxTele ∅ (Finmap.insert "bad" (.space .real) ∅)
      ((∅ : EvalCtx).extend "bad" .one illTypedStored) :=
  .extend_nlin .empty ⟨Finmap.notMem_empty, Finmap.notMem_empty⟩
    illTypedStored_entry .one

theorem illTypedStored_checked :
    Operational.Term ∅ (Finmap.insert "bad" (.space .real) ∅)
      ((∅ : EvalCtx).extend "bad" .one illTypedStored)
      (.var "bad") .one illTypedStored (.space .real) := by
  apply RawCertifiedOperational.C.Term.var_nlin
  · simp [EvalCtx.lookup, EvalCtx.extend]
  · simp [Basis.tof]
  · exact .one
  · exact .space rfl .one .real

theorem checked_with_history_need_not_have_value_typing :
    ∃ (Γ : NLCtx) (Ψ : EvalCtx) (e : Term) (v : ValExpr),
      V2.CtxTele ∅ Γ Ψ ∧
      Operational.Term ∅ Γ Ψ e .one v (.space .real) ∧
      ∀ (ε : ValCtx) (τ : ValTy), ¬ Nonempty (ValHasType ε v τ) :=
  ⟨_, _, _, _, illTypedStored_history, illTypedStored_checked, illTypedStored_not_typed⟩

def failed_witness_space_valid :
    ValSValid ∅ (.ffs .kernel (.tprod .real .real) badMatrix) :=
  .ffs .real .real badMatrix_typed

theorem illTypedStored_succeeds (ρ : ValEnvSem) :
    ∃ a, denotValB_semS directOracle ρ [] [] illTypedStored = .ok (.array a) := by
  simp [illTypedStored, denotValB_semS, ValValSem.bindArrays, ValValSem.bindArray,
    ValValSem.arrayOf, ValExpr.inferSpaceCtx, FlatArray.ofFn, ValueShape.scale, ValSpace.dof]

/-- Pinning the outer inferred type cannot repair an ill-typed operand. -/
theorem illTypedStored_retag_not_typed (ε : ValCtx) (τ target : ValTy) :
    ¬ Nonempty (ValHasType ε (.reshap illTypedStored target target) τ) := by
  rintro ⟨h⟩
  cases h with
  | reshap h _ _ => exact illTypedStored_not_typed ε _ ⟨h⟩

end
end GLang.PaperValueGapAudit

open Lean Elab Command
elab "check_gap_audit_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``GLang.PaperValueGapAudit.badMatrix_fails,
      ``GLang.PaperValueGapAudit.failed_witness_kernel_dimension,
      ``GLang.PaperValueGapAudit.checked_with_history_need_not_have_value_typing,
      ``GLang.PaperValueGapAudit.illTypedStored_succeeds,
      ``GLang.PaperValueGapAudit.illTypedStored_retag_not_typed] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected audit-witness assumption {n}: {ax}"
  logInfo "Semantic gap witnesses compile with no new axioms."
check_gap_audit_axioms

