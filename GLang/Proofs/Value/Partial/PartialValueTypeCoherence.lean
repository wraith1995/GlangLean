import GLang.Proofs.Value.Partial.PartialValueRelationTransport
import GLang.Proofs.Value.Presentation.PaperValueExtensionality

/-! Syntax-local partial type coherence. The stronger space clause retains
individual FFS observations (hence tensor factors), not only their product. -/
namespace GLang.PartialValueDomains
open PaperValueDomains

def PartialSpaceAgreement (q q' : PartialFFSOracle) : ValSpace → Prop
  | .empty | .real => True
  | .dsum s t | .tprod s t => PartialSpaceAgreement q q' s ∧ PartialSpaceAgreement q q' t
  | .ffs p s e => q p s e = q' p s e

theorem PartialSpaceAgreement.observations (q q' : PartialFFSOracle) (s : ValSpace)
    (h : PartialSpaceAgreement q q' s) :
    s.shpOfPartial q = s.shpOfPartial q' ∧ s.dofPartial q = s.dofPartial q' := by
  cases s with
  | empty | real => simp [ValSpace.shpOfPartial,ValSpace.dofPartial]
  | dsum s t | tprod s t =>
    have hs := PartialSpaceAgreement.observations q q' s h.1
    have ht := PartialSpaceAgreement.observations q q' t h.2
    constructor
    · simp only [ValSpace.shpOfPartial,hs.2,ht.2]
    · simp only [ValSpace.dofPartial,ValSpace.shpOfPartial,hs.2,ht.2]
  | ffs p s e =>
    change q p s e = q' p s e at h
    simp only [ValSpace.dofPartial,ValSpace.shpOfPartial,h]
    trivial
termination_by sizeOf s

/-- The internal numerical projection agrees on these same leaves. It is
used only after the partial dimension guards have succeeded. -/
theorem PartialSpaceAgreement.numbers (q q' : PartialFFSOracle) (s : ValSpace)
    (h : PartialSpaceAgreement q q' s) :
    SpaceOracleAgreement (PartialValueEval.numbers q) (PartialValueEval.numbers q') s := by
  cases s with
  | empty | real => trivial
  | dsum s t | tprod s t =>
    exact ⟨PartialSpaceAgreement.numbers q q' s h.1, PartialSpaceAgreement.numbers q q' t h.2⟩
  | ffs p s e =>
    change q p s e = q' p s e at h
    simp only [SpaceOracleAgreement,PartialValueEval.numbers,h]
termination_by sizeOf s

noncomputable abbrev PartialWorldType (orc : PartialFFSOracleSem) (w : World) (τ : ValTy) :=
  denotValTyPartial orc w.env w.types w.values τ

def PartialRawTypeCoherent (orc : PartialFFSOracleSem) : ValTy → World → World → Prop
  | .space s, w, w' =>
      PartialSpaceAgreement (orc w.env w.types w.values) (orc w'.env w'.types w'.values) s
  | .piTy d c, w, w' =>
      PartialRawTypeCoherent orc d w w' ∧
      ∀ v v', PartialRuntimeRelated d (PartialWorldType orc w d) (PartialWorldType orc w' d) v v' →
        PartialRawTypeCoherent orc c ⟨w.env,d::w.types,v::w.values⟩
          ⟨w'.env,d::w'.types,v'::w'.values⟩

/-- Type formation's stronger raw-fibre condition supplies the exact partial
coherence required by the recursive mathematical-domain theorem. -/
theorem PartialRawTypeCoherent.toCoherent (orc : PartialFFSOracleSem) (τ : ValTy)
    (w w' : World) (h : PartialRawTypeCoherent orc τ w w') :
    PartialCoherent τ (PartialWorldType orc w τ) (PartialWorldType orc w' τ) := by
  cases τ with
  | space s =>
    have hs := (PartialSpaceAgreement.observations _ _ s h).2
    simp only [PartialWorldType,denotValTyPartial,hs]
    cases s.dofPartial (orc w'.env w'.types w'.values) <;> rfl
  | piTy d c =>
    have hd := h.1.toCoherent orc d w w'
    simp only [PartialWorldType,denotValTyPartial]
    cases hD : denotValTyPartial orc w.env w.types w.values d <;>
      cases hE : denotValTyPartial orc w'.env w'.types w'.values d
    · simpa only [PartialWorldType,hD,hE,PartialCoherent] using hd
    · change PartialCoherent d _ _ at hd
      simp only [PartialWorldType,hD,hE] at hd
      cases d <;> exact False.elim hd
    · change PartialCoherent d _ _ at hd
      simp only [PartialWorldType,hD,hE] at hd
      cases d <;> exact False.elim hd
    · constructor
      · simpa only [PartialWorldType,hD,hE] using hd
      · intro a b hab
        have hr := partial_reify_related d _ _ a b hab
        have hv : PartialRuntimeRelated d (PartialWorldType orc w d)
            (PartialWorldType orc w' d) (d.carrierToVal a) (d.carrierToVal b) := by
          simpa only [PartialWorldType,hD,hE] using hr
        exact (h.2 _ _ hv).toCoherent orc c _ _
termination_by sizeOf τ

end GLang.PartialValueDomains
