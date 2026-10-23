import GLang.Proofs.Adequacy.OrdinaryBridge

namespace GLang
namespace OperationalStrengthening

/-- The part of a context-indexed checked operational semantics needed by
preservation.  An implementation may carry more indices (in particular the
exact realized result type needed by adequacy); those can be existentially
hidden in `term`.

`term` lives in `Prop`, matching the operational judgments.  Source typing is
returned under `Nonempty` because `HasType` is `Type`-valued. -/
structure CheckedOrdinaryTermSemantics where
  term : LCtx -> NLCtx -> EvalCtx -> GLang.Term -> Basis -> ValExpr -> Prop
  erase : forall {Delta Gamma Psi e b v},
    term Delta Gamma Psi e b v -> ValExpr.OpStep Psi e b v
  hasType : forall {Delta Gamma Psi e b v},
    term Delta Gamma Psi e b v ->
      Nonempty (HasType Delta Gamma e (Basis.tof b))
  basisValid : forall {Delta Gamma Psi e b v},
    term Delta Gamma Psi e b v -> Basis.BasisValid Gamma b

/-- Package a checked term judgment which retains its realized result type as
an index.  The preservation-facing interface does not need that index, so it is
hidden existentially; the exact adequacy lift can recover it below.

This is the intended adapter for the constructor-mirroring checked judgments:
their concrete integration needs only the three projections supplied here. -/
def CheckedOrdinaryTermSemantics.ofIndexed
    (termAt : LCtx -> NLCtx -> EvalCtx -> GLang.Term -> Basis ->
      ValExpr -> ValTy -> Prop)
    (erase : forall {Delta Gamma Psi e b v tauV},
      termAt Delta Gamma Psi e b v tauV -> ValExpr.OpStep Psi e b v)
    (hasType : forall {Delta Gamma Psi e b v tauV},
      termAt Delta Gamma Psi e b v tauV ->
        Nonempty (HasType Delta Gamma e (Basis.tof b)))
    (basisValid : forall {Delta Gamma Psi e b v tauV},
      termAt Delta Gamma Psi e b v tauV -> Basis.BasisValid Gamma b) :
    CheckedOrdinaryTermSemantics where
  term Delta Gamma Psi e b v :=
    exists tauV, termAt Delta Gamma Psi e b v tauV
  erase := by
    rintro Delta Gamma Psi e b v ⟨tauV, h⟩
    exact erase h
  hasType := by
    rintro Delta Gamma Psi e b v ⟨tauV, h⟩
    exact hasType h
  basisValid := by
    rintro Delta Gamma Psi e b v ⟨tauV, h⟩
    exact basisValid h

abbrev CheckedPreservationConclusion
    (Psi : EvalCtx) (rhoScope : V2.ValScope) (b : Basis) (v : ValExpr) : Prop :=
  (exists tauV, ValTy.EvalT Psi (Basis.tof b) tauV /\
      ReshapEq (ValExpr.inferType v) tauV) /\
    ValTyOk (ValExpr.inferType v) /\
    (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ rhoScope)

/-- Preservation for a checked ordinary trace is exactly existing preservation
after literal erasure.  In particular, installing the checked trace as a side
condition cannot invalidate or weaken preservation. -/
theorem CheckedOrdinaryTermSemantics.preservation
    (C : CheckedOrdinaryTermSemantics)
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx} {rhoScope : V2.ValScope}
    {e : GLang.Term} {b : Basis} {v : ValExpr}
    (hwfDeltaGamma : V2.CtxWF' Delta Gamma)
    (hwfPsi : V2.EvalCtxValid Psi)
    (hlcPsi : EvalCtxLc Psi)
    (hanchored : V2.EvalCtxLamAnchored Psi)
    (hwfRho : V2.RhoValid Psi rhoScope)
    (htypingEval : V2.TypingImplyEval Delta Gamma Psi)
    (hscope : V2.ScopeImplyVal Delta Gamma rhoScope)
    (hchecked : C.term Delta Gamma Psi e b v) :
    CheckedPreservationConclusion Psi rhoScope b v := by
  obtain ⟨htyped⟩ := C.hasType hchecked
  exact V2.preservation_term hwfDeltaGamma hwfPsi hlcPsi hanchored hwfRho
    htypingEval hscope htyped (C.basisValid hchecked) (C.erase hchecked)

/-- An ordinary adequacy call together with the hereditary, context-indexed
trace certificate for its *same* result `v`. -/
structure CheckedRawAdequacyCall (C : CheckedOrdinaryTermSemantics)
    (orc : FFSOracleSem) (rho : ValEnvSem)
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (e : GLang.Term) (b : Basis)
    (v : ValExpr) : Prop where
  raw : RawAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v
  checked : C.term Delta Gamma Psi e b v

theorem CheckedRawAdequacyCall.erase_checked
    (call : CheckedRawAdequacyCall C orc rho Delta Gamma Psi GammaV sigma e b v) :
    ValExpr.OpStep Psi e b v :=
  C.erase call.checked

/-- What an exact checked implementation must additionally provide for the
adequacy bridge.  This is deliberately separate from the preservation
interface: exact realized-type coordination is not needed by preservation. -/
def CheckedExactLift (C : CheckedOrdinaryTermSemantics) : Prop :=
  forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr},
    C.term Delta Gamma Psi e b v ->
      exists tauV, S.Term Delta Gamma Psi e b v tauV

/-- A checked exact lift immediately closes the preferred bridge for checked
ordinary calls, preserving the caller's literal result. -/
theorem exactLift_checkedCall
    (C : CheckedOrdinaryTermSemantics) (hlift : CheckedExactLift C)
    (call : CheckedRawAdequacyCall C orc rho Delta Gamma Psi GammaV sigma e b v) :
    exists tauV, S.Term Delta Gamma Psi e b v tauV :=
  hlift call.checked

/-- Progress with a hereditary checked result.  This mirrors the hypotheses of
the current public `V2.progress`; it is a proof target for the checked
operational implementation, not a postulate. -/
def CheckedProgress (C : CheckedOrdinaryTermSemantics) : Prop :=
  forall {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {e : GLang.Term} {tau : Ty} {b : Basis},
    V2.CtxTele Delta Gamma Psi ->
    V2.CtxWF' Delta Gamma ->
    V2.EvalCtxValid Psi ->
    EvalCtxLc Psi ->
    V2.EvalCtxLamAnchored Psi ->
    V2.TypingImplyEval Delta Gamma Psi ->
    HasType Delta Gamma e tau ->
    Basis.BasisValid Gamma b ->
    Basis.IsTyBasis b ->
    Basis.tof b = tau ->
    exists v, C.term Delta Gamma Psi e b v

/-- Checked progress conservatively extends current progress: forgetting the
certificate returns the same ordinary evaluation statement. -/
theorem CheckedProgress.toOrdinary
    (C : CheckedOrdinaryTermSemantics) (hprogress : CheckedProgress C)
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
    exists v, ValExpr.OpStep Psi e b v := by
  obtain ⟨v, hchecked⟩ := hprogress htele hwfDeltaGamma hwfPsi hlcPsi
    hanchored htypingEval htyped hbasis hisTyBasis htof
  exact ⟨v, C.erase hchecked⟩

end OperationalStrengthening
end GLang
