import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectAssembly
import GLang.Proofs.Value.Presentation.PaperValueNumericSubstitution

namespace GLang.PartialValueSubstitution
open PaperValueDomains

def SpaceAgreement (q q' : PartialFFSOracle) (x : VName) (u : ValExpr) : ValSpace → Prop
  | .empty | .real => True
  | .dsum s t | .tprod s t => SpaceAgreement q q' x u s ∧ SpaceAgreement q q' x u t
  | .ffs p s e => q p s e = q' p (ValSpace.subst x u s) (ValExpr.subst x u e)

mutual
 theorem SpaceAgreement.shapes {q q' : PartialFFSOracle} {x : VName} {u : ValExpr}
    {s : ValSpace} (h : SpaceAgreement q q' x u s) :
    s.shpOfPartial q = (ValSpace.subst x u s).shpOfPartial q' := by
  cases s with
  | empty | real => simp only [ValSpace.subst, ValSpace.shpOfPartial]
  | dsum s t | tprod s t =>
    simp only [ValSpace.subst, ValSpace.shpOfPartial,
      SpaceAgreement.dof h.1, SpaceAgreement.dof h.2]
  | ffs p s e =>
    simp only [ValSpace.subst, ValSpace.shpOfPartial]
    rw [show q p s e = q' p (ValSpace.subst x u s) (ValExpr.subst x u e) from h]
 termination_by 2 * sizeOf s
 decreasing_by all_goals simp_all <;> omega
 theorem SpaceAgreement.dof {q q' : PartialFFSOracle} {x : VName} {u : ValExpr}
    {s : ValSpace} (h : SpaceAgreement q q' x u s) :
    s.dofPartial q = (ValSpace.subst x u s).dofPartial q' := by
  simp only [ValSpace.dofPartial, h.shapes]
 termination_by 2 * sizeOf s + 1
 decreasing_by all_goals simp_all <;> omega
end

/-- Equal partial queries induce equal internal numeric views even on errors;
primitive dimension guards are compared separately before those views run. -/
theorem SpaceAgreement.numbers {q q' : PartialFFSOracle} {x : VName} {u : ValExpr}
    {s : ValSpace} (h : SpaceAgreement q q' x u s) :
    SubstSpaceAgreement (PartialValueEval.numbers q) (PartialValueEval.numbers q') x u s := by
  cases s with
  | empty | real => trivial
  | dsum s t | tprod s t => exact ⟨h.1.numbers,h.2.numbers⟩
  | ffs p s e =>
    change PartialValueEval.numbers q p s e =
      PartialValueEval.numbers q' p (ValSpace.subst x u s) (ValExpr.subst x u e)
    simp only [PartialValueEval.numbers,
      show q p s e = q' p (ValSpace.subst x u s) (ValExpr.subst x u e) from h]
termination_by sizeOf s

theorem SpaceAgreement.dimensions {q q' : PartialFFSOracle} {x : VName} {u : ValExpr}
    (ss : List ValSpace) (h : ∀ s ∈ ss, SpaceAgreement q q' x u s) :
    PartialValueEval.dimensions q ss =
      PartialValueEval.dimensions q' (ss.map (ValSpace.subst x u)) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [PartialValueEval.dimensions, List.map_cons,
      (h s (by simp)).dof, ih (fun t ht => h t (by simp [ht]))]

/-- The actual recursive oracle commutes with one typed substitution step
once the parent space and witness induction hypotheses are available. -/
theorem oracle_step (w w' : World) (x : VName) (u : ValExpr)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr)
    (hf : ValueQueryDependencies.Finite (.space w.types (.ffs p s e)))
    (hf' : ValueQueryDependencies.Finite (.space w'.types
      (.ffs p (ValSpace.subst x u s) (ValExpr.subst x u e))))
    (hs : SpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
      (PartialDirectOracle.oracle w'.env w'.types w'.values) x u s)
    (he : denotValB_partial PartialDirectOracle.oracle w.env w.types w.values e =
      denotValB_partial PartialDirectOracle.oracle w'.env w'.types w'.values
        (ValExpr.subst x u e)) :
    SpaceAgreement (PartialDirectOracle.oracle w.env w.types w.values)
      (PartialDirectOracle.oracle w'.env w'.types w'.values) x u (.ffs p s e) := by
  change PartialDirectOracle.oracle _ _ _ p s e =
    PartialDirectOracle.oracle _ _ _ p (ValSpace.subst x u s) (ValExpr.subst x u e)
  rw [PartialDirectLocality.oracle_eq _ _ _ _ _ _ hf, PartialDirectLocality.oracle_eq _ _ _ _ _ _ hf', hs.shapes, he]

/-- Agreement of every query leaf used by a space, retaining failure. -/
def LeafAgreement (q q' : PartialFFSOracle) : ValSpace → Prop
  | .empty | .real => True
  | .dsum s t | .tprod s t => LeafAgreement q q' s ∧ LeafAgreement q q' t
  | .ffs p s e => q p s e = q' p s e

theorem LeafAgreement.symm (q q' : PartialFFSOracle) : ∀ s, LeafAgreement q q' s → LeafAgreement q' q s
  | .empty, _ | .real, _ => trivial
  | .dsum s t, h | .tprod s t, h => ⟨LeafAgreement.symm q q' s h.1, LeafAgreement.symm q q' t h.2⟩
  | .ffs _ _ _, h => Eq.symm h

theorem LeafAgreement.fresh {orc : PartialFFSOracleSem}
    (hf : PartialDirectFv.OracleFresh orc) (w : World) (y : VName) (v : ValValSem)
    (hΓ : ValTyCtxFresh y w.types) : ∀ (s : ValSpace), y ∉ s.fv →
      LeafAgreement (orc w.env w.types w.values)
        (orc (w.env.update y v) w.types w.values) s
  | .empty, _ | .real, _ => trivial
  | .dsum s t, h | .tprod s t, h => by
    simp only [ValSpace.fv, Finset.mem_union, not_or] at h
    exact ⟨LeafAgreement.fresh hf w y v hΓ s h.1, LeafAgreement.fresh hf w y v hΓ t h.2⟩
  | .ffs p s e, h => by
    simp only [ValSpace.fv, Finset.mem_union, not_or] at h
    exact (hf w.env y v w.types w.values p s e hΓ h.1 h.2).symm

theorem SpaceAgreement.transport {q q' r r' : PartialFFSOracle} {x : VName} {u : ValExpr}
    {s : ValSpace} (h : SpaceAgreement q q' x u s)
    (hl : LeafAgreement q r s) (hr : LeafAgreement q' r' (ValSpace.subst x u s)) :
    SpaceAgreement r r' x u s := by
  cases s with
  | empty | real => trivial
  | dsum s t | tprod s t => exact ⟨h.1.transport hl.1 hr.1,h.2.transport hl.2 hr.2⟩
  | ffs p s e => exact Eq.trans (Eq.symm hl) (Eq.trans h hr)
termination_by sizeOf s

end GLang.PartialValueSubstitution
