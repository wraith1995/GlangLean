import GLang.Proofs.Progress.Supporting.CategoryProgress
import GLang.Proofs.Preservation.ValuePreservationV2

namespace GLang
namespace Operational

namespace Cob

/-- Preservation for the literal witness of a supplied unchecked change of
basis.  `SValid Gamma (Basis.sof bSrc)` is the exact source-formation fact
consumed by the mutual preservation induction; no validity fact about the
target is needed merely to establish the witness's matrix shape, value-type
validity, and name scope. -/
theorem ordinaryPreservationCore
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (history : V2.CtxTele Delta Gamma Psi)
    (sourceValid : SValid Gamma (Basis.sof bSrc))
    (step : Operational.Unchecked.EvalBB Psi bSrc env bTgt) :
    CobShapeT Psi env Psi.keyNames := by
  have hplus : V2.EvalCtxValidPlus Psi := history.evalCtxValidPlus
  have hrho : V2.RhoValid Psi Psi.keyNames := hplus.rhoValid_keyNames
  have hkeys : V2.KeyScope Psi Psi.keyNames := V2.keyScope_keyNames Psi
  exact V2.preservation_master.2.2.1 step Delta Gamma Psi.keyNames
    hplus hrho hkeys sourceValid

/-- Basis-valid wrapper around `ordinaryPreservationCore`.  This is the COB
analogue of ordinary term preservation: the caller supplies a creation
history, well-formed source data, and the literal unchecked evaluation whose
result is being classified. -/
theorem ordinaryPreservation
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (history : V2.CtxTele Delta Gamma Psi)
    (sourceValid : Basis.BasisValid Gamma bSrc)
    (step : Operational.Unchecked.EvalBB Psi bSrc env bTgt) :
    CobShapeT Psi env Psi.keyNames := by
  obtain ⟨hsource⟩ := sourceValid.sof_valid
  exact ordinaryPreservationCore history hsource step

/-- Checked change-of-basis progress between two arbitrary compatible valid
space bases.  It is enough to state hereditary space shape for the source:
validity and equality of endpoint types force the target to be a hereditary
space basis as well.

The construction converts both endpoints to their common standard basis,
inverts the target conversion, and composes the two conversions. -/
theorem progressBetween
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis}
    (history : V2.CtxTele Delta Gamma Psi)
    (sourceValid : Basis.BasisValid Gamma bSrc)
    (targetValid : Basis.BasisValid Gamma bTgt)
    (sourceIsSpace : Basis.tof bSrc = .space (Basis.sof bSrc))
    (sameType : Basis.tof bSrc = Basis.tof bTgt) :
    exists env, Operational.Cob Gamma Psi bSrc env bTgt := by
  have targetTofSpace :
      Basis.tof bTgt = .space (Basis.sof bSrc) :=
    sameType.symm.trans sourceIsSpace
  have targetIsSpace : Basis.IsSpaceBasis bTgt :=
    targetValid.isTyBasis.toIsSpaceBasis_of_tof_eq targetTofSpace

  obtain ⟨envSrc, sourceToStd⟩ :=
    Operational.Cob.progressToStandard history sourceValid sourceIsSpace
  obtain ⟨envTgt, targetToStd⟩ :=
    Operational.Cob.progressToStandard history targetValid targetIsSpace.tof_eq

  have sourceToCommon : Operational.Cob Gamma Psi bSrc envSrc
      (Basis.std (Basis.tof bTgt)) := by
    simpa only [sameType] using sourceToStd

  obtain ⟨_kind, ⟨targetTypeValid⟩⟩ := targetValid.tof_tvalid
  have standardValid :
      Basis.BasisValid Gamma (Basis.std (Basis.tof bTgt)) :=
    Basis.std_valid (Basis.tof bTgt) targetTypeValid
  have commonToTarget : Operational.Cob Gamma Psi
      (Basis.std (Basis.tof bTgt)) (.inv envTgt) bTgt :=
    .inverse standardValid targetValid targetToStd

  obtain ⟨sourceSpaceValid⟩ := sourceValid.sof_valid
  obtain ⟨sv, sourceSpace⟩ :=
    Operational.Space.progress history sourceSpaceValid
  exact ⟨_, .trans sourceValid targetValid sourceToCommon commonToTarget
    sourceSpace⟩

end Cob

end Operational
end GLang
