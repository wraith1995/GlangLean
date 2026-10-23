import GLang.Proofs.Progress.CheckedErasure
import GLang.Proofs.Progress.Certificates.RawCertifiedOperationalInterface

/-!
# Concrete preservation adapter for certified ordinary evaluation

`RawCertifiedOperational.C.Term` retains a realized result type as an index.
This file exports two internal preservation views: one existentially hides the
index through the generic preservation-safe interface, while the supporting
exact-index conclusion exposes the same `tauV` carried by the checked trace and
anchors it to the caller-selected basis with `C.TyAt`.  The public metatheorem
instead follows the caller-supplied unchecked trace.

This is a literal adapter: erasure keeps the source term, caller-selected
basis, and produced value unchanged.  Both results reuse the existing
`V2.preservation_term`; exact-index preservation additionally transports its
reshape fact between two realizations of the same source type.
-/

namespace GLang
namespace OperationalStrengthening

/-- The fully indexed ordinary certificate, viewed through the minimal
preservation-facing interface. -/
def rawCertifiedSemantics : CheckedOrdinaryTermSemantics :=
  CheckedOrdinaryTermSemantics.ofIndexed
    RawCertifiedOperational.C.Term
    RawCertifiedOperational.C.Term.erase
    RawCertifiedOperational.C.Term.hasType
    RawCertifiedOperational.C.Term.basisValid

/-- Preservation from exactly the three environment facts consumed by the
threaded preservation motive.  Source typing and requested-basis validity are
already projections of the checked trace, so they are not repeated as public
premises here. -/
theorem rawCertified_preservationCore
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx} {rhoScope : V2.ValScope}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hplus : V2.EvalCtxValidPlus Psi)
    (hrho : V2.RhoValid Psi rhoScope)
    (hkey : V2.KeyScope Psi rhoScope)
    (hchecked : RawCertifiedOperational.C.Term Delta Gamma Psi e b v tauV) :
    CheckedPreservationConclusion Psi rhoScope b v := by
  obtain ⟨htyped⟩ := hchecked.hasType
  obtain ⟨hsof⟩ := hchecked.basisValid.sof_valid
  obtain ⟨hshape, hok, hfvs⟩ :=
    V2.preservation_master.2.2.2 hchecked.erase Delta Gamma rhoScope
      hplus hrho hkey htyped hsof
  exact ⟨hshape, hok, hfvs.trans hkey⟩

/-- Concrete preservation for a certified ordinary term derivation. -/
theorem rawCertified_preservation
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx} {rhoScope : V2.ValScope}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hwfDeltaGamma : V2.CtxWF' Delta Gamma)
    (hwfPsi : V2.EvalCtxValid Psi)
    (hlcPsi : EvalCtxLc Psi)
    (hanchored : V2.EvalCtxLamAnchored Psi)
    (hwfRho : V2.RhoValid Psi rhoScope)
    (htypingEval : V2.TypingImplyEval Delta Gamma Psi)
    (hscope : V2.ScopeImplyVal Delta Gamma rhoScope)
    (hchecked : RawCertifiedOperational.C.Term Delta Gamma Psi e b v tauV) :
    CheckedPreservationConclusion Psi rhoScope b v := by
  exact rawCertified_preservationCore
    (V2.evalCtxValidPlus_of hwfPsi hlcPsi hanchored hwfRho
      htypingEval hscope)
    hwfRho (V2.keyScope_of htypingEval hscope) hchecked

/-- Preservation stated at the exact realized type retained by the checked
trace.  This strengthens `CheckedPreservationConclusion`, whose existential
type realization need not visibly be the checked trace's `tauV`.

The `C.TyAt` and `EvalT` fields connect `tauV` to the caller-selected basis.
The remaining fields are the ordinary preservation facts, with reshape
compatibility transported from the existential realization to this exact one
by structural-kind determinacy.  `ReshapEq` itself is a validity/common-kind
relation, not a numerical dimension equality; the latter belongs to adequacy's
oracle- and consistency-indexed `AgreeDims`. -/
abbrev CheckedPreservationAtConclusion
    (Gamma : NLCtx) (Psi : EvalCtx) (rhoScope : V2.ValScope)
    (b : Basis) (v : ValExpr) (tauV : ValTy) : Prop :=
  RawCertifiedOperational.C.TyAt Gamma Psi b tauV /\
    ValTy.EvalT Psi (Basis.tof b) tauV /\
    ReshapEq (ValExpr.inferType v) tauV /\
    ValTyOk (ValExpr.inferType v) /\
    (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ rhoScope)

/-- Preservation at the realized type retained by a checked evaluation. -/
private theorem rawCertified_preservationAt_of_preservation
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx} {rhoScope : V2.ValScope}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hchecked : RawCertifiedOperational.C.Term Delta Gamma Psi e b v tauV)
    (hpres : CheckedPreservationConclusion Psi rhoScope b v) :
    CheckedPreservationAtConclusion Gamma Psi rhoScope b v tauV := by
  obtain ⟨⟨tauV', heval', hreshape⟩, hok, hfvs⟩ := hpres
  obtain ⟨k, ⟨hinfer⟩, ⟨hvalid'⟩⟩ := hreshape
  have heval : ValTy.EvalT Psi (Basis.tof b) tauV := hchecked.toEvalT
  have hkind : (ValExpr.inferType v).structuralKind = tauV.structuralKind := by
    calc
      (ValExpr.inferType v).structuralKind = k :=
        (ValTValidC.kind_eq_structural hinfer).symm
      _ = tauV'.structuralKind := ValTValidC.kind_eq_structural hvalid'
      _ = tauV.structuralKind := heval'.structuralKind_determined heval
  have hreshapeAt : ReshapEq (ValExpr.inferType v) tauV :=
    ReshapEq.of_valid_eqStructKind hinfer (evalT_valid heval).some hkind
  exact ⟨hchecked.tyAt, heval, hreshapeAt, hok, hfvs⟩

/-- Exact-index preservation from the actual threaded motive inputs. -/
theorem rawCertified_preservationAtCore
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx} {rhoScope : V2.ValScope}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hplus : V2.EvalCtxValidPlus Psi)
    (hrho : V2.RhoValid Psi rhoScope)
    (hkey : V2.KeyScope Psi rhoScope)
    (hchecked : RawCertifiedOperational.C.Term Delta Gamma Psi e b v tauV) :
    CheckedPreservationAtConclusion Gamma Psi rhoScope b v tauV :=
  rawCertified_preservationAt_of_preservation hchecked
    (rawCertified_preservationCore hplus hrho hkey hchecked)

/-- Exact-index preservation for the concrete checked operational judgment.
No stronger premise is needed than for ordinary preservation: every checked
term node already carries `C.TyAt Gamma Psi b tauV`, and erases it to an
evaluation of `Basis.tof b` at exactly `tauV`. -/
theorem rawCertified_preservationAt
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx} {rhoScope : V2.ValScope}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hwfDeltaGamma : V2.CtxWF' Delta Gamma)
    (hwfPsi : V2.EvalCtxValid Psi)
    (hlcPsi : EvalCtxLc Psi)
    (hanchored : V2.EvalCtxLamAnchored Psi)
    (hwfRho : V2.RhoValid Psi rhoScope)
    (htypingEval : V2.TypingImplyEval Delta Gamma Psi)
    (hscope : V2.ScopeImplyVal Delta Gamma rhoScope)
    (hchecked : RawCertifiedOperational.C.Term Delta Gamma Psi e b v tauV) :
    CheckedPreservationAtConclusion Gamma Psi rhoScope b v tauV := by
  exact rawCertified_preservationAtCore
    (V2.evalCtxValidPlus_of hwfPsi hlcPsi hanchored hwfRho
      htypingEval hscope)
    hwfRho (V2.keyScope_of htypingEval hscope) hchecked

/-- The remaining progress obligation, specialized to the concrete checked
judgment.  Proving this constructs the hereditary side-condition certificate;
its projection to the current public progress theorem is already available as
`CheckedProgress.toOrdinary`. -/
abbrev RawCertifiedProgress : Prop :=
  CheckedProgress rawCertifiedSemantics

/-- A concrete checked-progress proof implies the unchanged ordinary progress
statement by literal erasure. -/
theorem RawCertifiedProgress.toOrdinary
    (hprogress : RawCertifiedProgress)
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {e : GLang.Term} {tau : Ty} {b : Basis}
    (htele : V2.CtxTele Delta Gamma Psi)
    (hwfDeltaGamma : V2.CtxWF' Delta Gamma)
    (hwfPsi : V2.EvalCtxValid Psi)
    (hlcPsi : EvalCtxLc Psi)
    (hanchored : V2.EvalCtxLamAnchored Psi)
    (htypingEval : V2.TypingImplyEval Delta Gamma Psi)
    (htyped : HasType Delta Gamma e tau)
    (hbasis : Basis.BasisValid Gamma b)
    (hisTyBasis : Basis.IsTyBasis b)
    (htof : Basis.tof b = tau) :
    exists v, ValExpr.OpStep Psi e b v :=
  CheckedProgress.toOrdinary rawCertifiedSemantics hprogress htele
    hwfDeltaGamma hwfPsi hlcPsi hanchored htypingEval htyped hbasis
    hisTyBasis htof

end OperationalStrengthening
end GLang
