import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLiftAdapter
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLower
import GLang.Proofs.Progress.Certificates.RawCertifiedPublicProgress
import GLang.Proofs.Adequacy.Foundations.Public
import GLang.Proofs.Preservation.Context

/-! # Operational interfaces

Context-indexed checked evaluation judgments and their erasure to ordinary
evaluation, with the premises used by progress and adequacy. -/

namespace GLang
namespace Operational

/-! ## Canonical checked judgments -/

/-- Canonical space evaluation, indexed by its source typing context. -/
abbrev Space := RawCertifiedOperational.C.Space

/-- Canonical type evaluation, indexed by its source typing context. -/
abbrev Ty := RawCertifiedOperational.C.Ty

/-- Canonical exact-basis type evaluation. -/
abbrev TyAt := RawCertifiedOperational.C.TyAt

/-- Canonical checked change-of-basis evaluation. -/
abbrev Cob := RawCertifiedOperational.C.Cob

/-- Canonical checked term evaluation, retaining its exact realized type. -/
abbrev Term := RawCertifiedOperational.C.Term

/-! ## Call boundaries for progress and soundness -/

/-- One root-only reanchoring boundary for checked progress.  Source
evaluation is constructed at the literal standard basis; this capability
moves that completed checked result to the requested basis.  Space instances
are ordinary checked COBs, while frame instances are higher-order term
transports. -/
abbrev RootBasisBoundary :=
  RawCertifiedPublicProgress.CheckedRootBasisBoundary

/-- Unary syntax evidence sufficient to implement a requested root basis
boundary.  It follows the structure of that one basis and contains no paired
standard-conversion obligation. -/
abbrev RootBasisLocalFinite
    (Psi : EvalCtx) {Gamma : NLCtx} {requested : Basis}
    (hrequested : Basis.BasisValid Gamma requested) : Prop :=
  RawCertifiedCobProgressMutualSpike.CheckedLocalSideBasisFinite
    Psi hrequested

namespace RootBasisBoundary

/-- The boundary for a literal standard basis is reflexive. -/
theorem standard
    {Gamma : NLCtx} {Psi : EvalCtx} {tau : GLang.Ty} {k : Kind}
    (htau : TValid Gamma tau k) :
    Operational.RootBasisBoundary Gamma Psi (Basis.std tau) :=
  RawCertifiedPublicProgress.checkedRootBasisBoundary_standard htau

/-- Build the semantic root reanchoring boundary from one unary basis-local
certificate and the evaluator invariants needed to execute its checked COB. -/
theorem ofLocalFinite
    {Gamma : NLCtx} {Psi : EvalCtx} {requested : Basis}
    (hcarrier : V2.PCarrier Psi)
    (hcovered : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hrequested : Basis.BasisValid Gamma requested)
    (hlocal : Operational.RootBasisLocalFinite Psi hrequested) :
    Operational.RootBasisBoundary Gamma Psi requested :=
  RawCertifiedPublicProgress.checkedRootBasisBoundary_of_localSide
    hcarrier hcovered hstored hrequested hlocal

end RootBasisBoundary

/-- The semantic-free joint creation history for source contexts and their
runtime evaluator.  Each entry is checked at the prefix at which it was
created; no oracle, denotation, finite-depth certificate, or adequacy fact is
part of this relation. -/
abbrev ContextHistory := TypedContext

/-- The public progress boundary.  A well-formed operational creation history,
typing of the source term, and validity of the requested result basis suffice
to construct a context-indexed checked evaluation.  All exact lookup anchors,
finite syntax traversals, recursion depths, and basis transports are derived
inside the proof. -/
structure ProgressCall
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (e : GLang.Term) (b : Basis) : Type where
  history : V2.CtxTele Delta Gamma Psi
  typed : HasType Delta Gamma e (Basis.tof b)
  basisValid : Basis.BasisValid Gamma b

abbrev UncheckedProgressCall := RawCertifiedCallProgress.OrdinaryProgressCall

theorem ProgressCall.isTyBasis
    (call : ProgressCall Delta Gamma Psi e b) : Basis.IsTyBasis b :=
  call.basisValid.isTyBasis

/-- The unary judgment-local admissibility condition for checked progress. -/
abbrev CheckedProgressAdmissible
    (Psi : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : GLang.Term} {tau : GLang.Ty}
    (ht : HasType Delta Gamma e tau)
    {b : Basis} (_basisValid : Basis.BasisValid Gamma b) : Prop :=
  RawCertifiedLocalizedCallCertificate.CheckedJudgmentLocalCallFinite
    Psi ht _basisValid

abbrev LocalCallFinite := Operational.CheckedProgressAdmissible

structure LocalCertificateProgressCall
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (e : GLang.Term) (b : Basis) : Type where
  carrier : V2.PCarrier Psi
  varsCovered : V2.VarsCovered Delta Gamma Psi
  storedWF : V2.StoredWF Psi
  ctxWF : V2.CtxWF' Delta Gamma
  typed : HasType Delta Gamma e (Basis.tof b)
  basisValid : Basis.BasisValid Gamma b
  localFinite : Operational.CheckedProgressAdmissible Psi typed basisValid

/-- Accessor for the hereditary shape implied by validity. -/
theorem LocalCertificateProgressCall.isTyBasis
    (call : LocalCertificateProgressCall Delta Gamma Psi e b) :
    Basis.IsTyBasis b :=
  call.basisValid.isTyBasis

abbrev CheckedProgressCall := Operational.ProgressCall

/-- The richer boundary for checked progress followed by adequacy.  Raw
consistency supplies the same semantic-free history used by `ProgressCall`;
the oracle and denotational consistency fields appear here only because the
conclusion also states denotational adequacy. -/
structure SoundnessCall (orc : FFSOracleSem) (rho : ValEnvSem)
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx) (GammaV : ValCtx)
    (sigma : DEnv) (e : GLang.Term) (b : Basis) : Type where
  oracle : RawApplicationOracleSpec orc
  consistent : RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho
  typed : HasType Delta Gamma e (Basis.tof b)
  basisValid : Basis.BasisValid Gamma b

/-- Accessor for the hereditary shape implied by validity. -/
theorem SoundnessCall.isTyBasis
    (call : SoundnessCall orc rho Delta Gamma Psi GammaV sigma e b) :
    Basis.IsTyBasis b :=
  call.basisValid.isTyBasis

/-- Descriptive spelling of `SoundnessCall`, used by the canonical existential
checked-progress-and-adequacy theorem. -/
abbrev ProgressAdequacyCall := Operational.SoundnessCall

/-- Internal semantic-call view used by the checked adequacy implementation. -/
def SoundnessCall.toRaw
    (call : SoundnessCall orc rho Delta Gamma Psi GammaV sigma e b) :
    OperationalStrengthening.RawProgressCall
      orc rho Delta Gamma Psi GammaV sigma e b where
  oracle := call.oracle
  consistent := call.consistent
  typed := ⟨call.typed⟩
  basisValid := call.basisValid

/-- Every soundness call forgets its denotational fields to the strictly
smaller operational progress boundary. -/
def SoundnessCall.toProgressCall
    (call : SoundnessCall orc rho Delta Gamma Psi GammaV sigma e b) :
    ProgressCall Delta Gamma Psi e b where
  history := call.consistent.context.erase
  typed := call.typed
  basisValid := call.basisValid

namespace Unchecked

abbrev EvalS := ValSpace.EvalS

abbrev EvalT := ValTy.EvalT

abbrev EvalBB := Basis.EvalBB

abbrev OpStep := ValExpr.OpStep

end Unchecked

namespace Legacy

abbrev EvalS := Unchecked.EvalS
abbrev EvalT := Unchecked.EvalT
abbrev EvalBB := Unchecked.EvalBB
abbrev OpStep := Unchecked.OpStep

end Legacy

/-! ## Literal checked-to-unchecked projections -/

theorem Space.toUnchecked
    (h : Operational.Space Gamma Psi s sv) :
    Unchecked.EvalS Psi s sv :=
  RawCertifiedOperational.C.Space.erase h

theorem Ty.toUnchecked
    (h : Operational.Ty Gamma Psi tau tauv) :
    Unchecked.EvalT Psi tau tauv :=
  RawCertifiedOperational.C.Ty.erase h

theorem TyAt.toUnchecked
    (h : Operational.TyAt Gamma Psi b tauv) :
    Unchecked.EvalT Psi (Basis.tof b) tauv :=
  RawCertifiedOperational.C.TyAt.erase h

theorem Cob.toUnchecked
    (h : Operational.Cob Gamma Psi b0 env b1) :
    Unchecked.EvalBB Psi b0 env b1 :=
  RawCertifiedOperational.C.Cob.erase h

/-- Literal erasure preserves the term, selected basis, and produced value. -/
theorem Term.toUnchecked
    (h : Operational.Term Delta Gamma Psi e b v tauv) :
    Unchecked.OpStep Psi e b v :=
  RawCertifiedOperational.C.Term.erase h

/-- The erased realized-type derivation retained by a canonical term node. -/
theorem Term.toUncheckedType
    (h : Operational.Term Delta Gamma Psi e b v tauv) :
    Unchecked.EvalT Psi (Basis.tof b) tauv :=
  RawCertifiedOperational.C.Term.toEvalT h

/-! ## Preservation at the canonical API -/

/-- Canonical checked preservation from exactly the environment facts threaded
through the preservation induction.  The checked trace itself supplies source
typing and requested-basis validity. -/
theorem Term.preservationCore
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {rhoScope : V2.ValScope} {e : GLang.Term} {b : Basis}
    {v : ValExpr} {tauV : ValTy}
    (hplus : V2.EvalCtxValidPlus Psi)
    (hrho : V2.RhoValid Psi rhoScope)
    (hkey : V2.KeyScope Psi rhoScope)
    (h : Operational.Term Delta Gamma Psi e b v tauV) :
    OperationalStrengthening.CheckedPreservationConclusion
      Psi rhoScope b v :=
  OperationalStrengthening.rawCertified_preservationCore
    hplus hrho hkey h

theorem Term.preservation
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {rhoScope : V2.ValScope} {e : GLang.Term} {b : Basis}
    {v : ValExpr} {tauV : ValTy}
    (hwfDeltaGamma : V2.CtxWF' Delta Gamma)
    (hwfPsi : V2.EvalCtxValid Psi)
    (hlcPsi : EvalCtxLc Psi)
    (hanchored : V2.EvalCtxLamAnchored Psi)
    (hwfRho : V2.RhoValid Psi rhoScope)
    (htypingEval : V2.TypingImplyEval Delta Gamma Psi)
    (hscope : V2.ScopeImplyVal Delta Gamma rhoScope)
    (h : Operational.Term Delta Gamma Psi e b v tauV) :
    OperationalStrengthening.CheckedPreservationConclusion
      Psi rhoScope b v := by
  exact Term.preservationCore
    (V2.evalCtxValidPlus_of hwfPsi hlcPsi hanchored hwfRho
      htypingEval hscope)
    hwfRho (V2.keyScope_of htypingEval hscope) h

/-- Exact-index preservation from the same pared environment boundary as
`Term.preservationCore`. -/
theorem Term.preservationAtCore
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {rhoScope : V2.ValScope} {e : GLang.Term} {b : Basis}
    {v : ValExpr} {tauV : ValTy}
    (hplus : V2.EvalCtxValidPlus Psi)
    (hrho : V2.RhoValid Psi rhoScope)
    (hkey : V2.KeyScope Psi rhoScope)
    (h : Operational.Term Delta Gamma Psi e b v tauV) :
    OperationalStrengthening.CheckedPreservationAtConclusion
      Gamma Psi rhoScope b v tauV :=
  OperationalStrengthening.rawCertified_preservationAtCore
    hplus hrho hkey h

theorem Term.preservationAt
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {rhoScope : V2.ValScope} {e : GLang.Term} {b : Basis}
    {v : ValExpr} {tauV : ValTy}
    (hwfDeltaGamma : V2.CtxWF' Delta Gamma)
    (hwfPsi : V2.EvalCtxValid Psi)
    (hlcPsi : EvalCtxLc Psi)
    (hanchored : V2.EvalCtxLamAnchored Psi)
    (hwfRho : V2.RhoValid Psi rhoScope)
    (htypingEval : V2.TypingImplyEval Delta Gamma Psi)
    (hscope : V2.ScopeImplyVal Delta Gamma rhoScope)
    (h : Operational.Term Delta Gamma Psi e b v tauV) :
    OperationalStrengthening.CheckedPreservationAtConclusion
      Gamma Psi rhoScope b v tauV := by
  exact Term.preservationAtCore
    (V2.evalCtxValidPlus_of hwfPsi hlcPsi hanchored hwfRho
      htypingEval hscope)
    hwfRho (V2.keyScope_of htypingEval hscope) h

theorem Space.toStrengthened
    (h : Operational.Space Gamma Psi s sv) :
    S.Space Gamma Psi s sv :=
  RawCertifiedOperational.C.Space.toS h

theorem Ty.toStrengthened
    (h : Operational.Ty Gamma Psi tau tauv) :
    S.Ty Gamma Psi tau tauv :=
  RawCertifiedOperational.C.Ty.toS h

theorem TyAt.toStrengthened
    (h : Operational.TyAt Gamma Psi b tauv) :
    S.TyAt Gamma Psi b tauv :=
  RawCertifiedOperational.C.TyAt.toS h

theorem Cob.toStrengthened
    (h : Operational.Cob Gamma Psi b0 env b1) :
    S.Cob Gamma Psi b0 env b1 :=
  RawCertifiedOperational.C.Cob.toS h

/-- Exact strengthening preserves the source, basis, result value, and
realized result type definitionally. -/
theorem Term.toStrengthened
    (h : Operational.Term Delta Gamma Psi e b v tauv) :
    S.Term Delta Gamma Psi e b v tauv :=
  RawCertifiedOperational.C.Term.toS h

theorem Space.ofStrengthened
    (h : S.Space Gamma Psi s sv) :
    Operational.Space Gamma Psi s sv :=
  RawCertifiedOperational.S.Space.toC h

theorem Ty.ofStrengthened
    (h : S.Ty Gamma Psi tau tauv) :
    Operational.Ty Gamma Psi tau tauv :=
  RawCertifiedOperational.S.Ty.toC h

theorem TyAt.ofStrengthened
    (h : S.TyAt Gamma Psi b tauv) :
    Operational.TyAt Gamma Psi b tauv :=
  RawCertifiedOperational.S.TyAt.toC h

theorem Cob.ofStrengthened
    (h : S.Cob Gamma Psi b0 env b1) :
    Operational.Cob Gamma Psi b0 env b1 :=
  RawCertifiedOperational.S.Cob.toC h

theorem Term.ofStrengthened
    (h : S.Term Delta Gamma Psi e b v tauv) :
    Operational.Term Delta Gamma Psi e b v tauv :=
  RawCertifiedOperational.S.Term.toC h

/-! ## Adequacy at the canonical API -/

/-- Canonical checked-space adequacy.  The value-space shape produced by the
checked evaluation is exactly the denotational source-space shape. -/
theorem Space.adequacy
    (orc : FFSOracleSem) (hspec : Adequacy.OracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : GLang.Space} {sv : ValSpace}
    (h : Operational.Space Gamma Psi s sv) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      ValSpace.shpOf (orc rho [] []) sv = srcShp sigma [] s :=
  Adequacy.space orc hspec h.toStrengthened

theorem Term.adequacyResult
    (orc : FFSOracleSem) (hspec : Adequacy.OracleSpec orc)
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (h : Operational.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      ResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) :=
  OperationalStrengthening.rawCertified_adequacy_term orc hspec h

/-- Canonical checked term adequacy.  Both conjuncts are derived from the same
checked trace, exact realized type, basis, and consistency witness. -/
theorem Term.adequacy
    (orc : FFSOracleSem) (hspec : Adequacy.OracleSpec orc)
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (h : Operational.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      ResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (denotValB_semS orc rho [] [] v) /\
        AgreeDims orc sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) := by
  intro sigma GammaV hconsistent
  exact ⟨Term.adequacyResult orc hspec h sigma GammaV hconsistent,
    OperationalStrengthening.rawCertified_adequacy_dims orc hspec h.tyAt
      Delta sigma GammaV hconsistent⟩

/-- Change-of-basis adequacy for the canonical operational judgment. -/
theorem Cob.adequacy
    (orc : FFSOracleSem) (hspec : Adequacy.OracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (h : Operational.Cob Gamma Psi bSrc env bTgt) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      CobAgree orc sigma rho bSrc bTgt env :=
  OperationalStrengthening.rawCertified_adequacy_cob orc hspec h

/-- Exact-basis dimension adequacy for the canonical type anchor. -/
theorem TyAt.adequacyDims
    (orc : FFSOracleSem) (hspec : Adequacy.OracleSpec orc)
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {tauV : ValTy}
    (h : Operational.TyAt Gamma Psi b tauV) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent orc Delta Gamma Psi GammaV sigma rho ->
      AgreeDims orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) :=
  OperationalStrengthening.rawCertified_adequacy_dims orc hspec h

/-! ## Checked progress by default, explicit unchecked erasure, and soundness -/

/-- Canonical progress constructs a context-indexed checked result from only
the semantic-free creation history, source typing, and validity of the
requested basis.  The final identity retag pins both syntactic inferers to the
exact realized type retained by the checked trace. -/
theorem Term.progress
    (call : Operational.ProgressCall
      Delta Gamma Psi e b) :
    exists v tauv,
      Operational.Term Delta Gamma Psi e b v tauv /\
      ValExpr.inferType v = tauv /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauv := by
  obtain ⟨v, tauv, hchecked⟩ :=
    RawCertifiedPublicProgress.checked_progress
      call.history call.typed call.basisValid
  let hready : Operational.Term Delta Gamma Psi e b
      (.reshap v tauv tauv) tauv :=
    RawCertifiedProgressScratch.retag hchecked hchecked.tyAt
  exact ⟨.reshap v tauv tauv, tauv, hready, rfl, rfl⟩

theorem Term.ordinaryProgress
    (call : Operational.ProgressCall Delta Gamma Psi e b) :
    exists v, Unchecked.OpStep Psi e b v := by
  obtain ⟨v, _tauv, hchecked, _hinfer, _hinferSpace⟩ := Term.progress call
  exact ⟨v, hchecked.erase⟩

theorem Term.uncheckedProgress
    (call : Operational.UncheckedProgressCall Delta Gamma Psi e b) :
    exists v, Unchecked.OpStep Psi e b v :=
  RawCertifiedPublicProgress.ordinary_progress call

/-- Forgetting the denotational fields of a soundness call gives canonical
checked progress. -/
theorem Term.progressOfSoundnessCall
    (call : Operational.SoundnessCall
      orc rho Delta Gamma Psi GammaV sigma e b) :
    exists v tauv,
      Operational.Term Delta Gamma Psi e b v tauv /\
      ValExpr.inferType v = tauv /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauv :=
  Term.progress call.toProgressCall

theorem Term.checkedProgress
    (call : Operational.CheckedProgressCall Delta Gamma Psi e b) :
    exists v tauv,
      Operational.Term Delta Gamma Psi e b v tauv /\
      ValExpr.inferType v = tauv /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauv :=
  Term.progress call

theorem Term.checkedProgressFromLocalCertificate
    (call : Operational.LocalCertificateProgressCall Delta Gamma Psi e b) :
    exists v tauv,
      Operational.Term Delta Gamma Psi e b v tauv /\
      ValExpr.inferType v = tauv /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauv := by
  obtain ⟨typed, localFinite⟩ := call.localFinite
  obtain ⟨v, tauv, hchecked⟩ :=
    RawCertifiedDepthAssemblyLocal.checked_progress_localFinite
      RawCertifiedOperational.RenameProof.checkedRenameLaws
      RawCertifiedOperational.checkedTyAtAppCut
      typed call.basisValid call.isTyBasis localFinite
      call.carrier call.varsCovered call.storedWF call.ctxWF
  let hready : Operational.Term Delta Gamma Psi e b
      (.reshap v tauv tauv) tauv :=
    RawCertifiedProgressScratch.retag hchecked hchecked.tyAt
  exact ⟨.reshap v tauv tauv, tauv, hready, rfl, rfl⟩

theorem Term.checkedProgressOfSoundnessCall
    (call : Operational.SoundnessCall
      orc rho Delta Gamma Psi GammaV sigma e b) :
    exists v tauv,
      Operational.Term Delta Gamma Psi e b v tauv /\
      ValExpr.inferType v = tauv /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauv :=
  Term.progressOfSoundnessCall call

/-- Explicit ordinary erasure of progress projected from a soundness call. -/
theorem Term.ordinaryProgressOfSoundnessCall
    (call : Operational.SoundnessCall
      orc rho Delta Gamma Psi GammaV sigma e b) :
    exists v, Unchecked.OpStep Psi e b v := by
  obtain ⟨v, _tauv, hchecked, _hinfer, _hinferSpace⟩ :=
    Term.progressOfSoundnessCall call
  exact ⟨v, hchecked.erase⟩

/-- Existential checked progress followed by adequacy for one soundness call. -/
theorem Term.progressAndAdequacy
    (call : Operational.ProgressAdequacyCall
      orc rho Delta Gamma Psi GammaV sigma e b) :
    exists v tauv,
      Operational.Term Delta Gamma Psi e b v tauv /\
      ValExpr.inferType v = tauv /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauv /\
      Unchecked.OpStep Psi e b v /\
      S.Term Delta Gamma Psi e b v tauv /\
      ResultAgree orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) /\
      AgreeDims orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) := by
  obtain ⟨v, tauv, hchecked, hinfer, hinferSpace⟩ :=
    Term.checkedProgressOfSoundnessCall call
  obtain ⟨hresult, hdims⟩ :=
    hchecked.adequacy orc call.oracle sigma GammaV call.consistent
  exact ⟨v, tauv, hchecked, hinfer, hinferSpace, hchecked.erase,
    hchecked.toStrengthened, hresult, hdims⟩

theorem Term.soundness
    (call : Operational.SoundnessCall
      orc rho Delta Gamma Psi GammaV sigma e b) :
    exists v tauv,
      Operational.Term Delta Gamma Psi e b v tauv /\
      ValExpr.inferType v = tauv /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauv /\
      Unchecked.OpStep Psi e b v /\
      S.Term Delta Gamma Psi e b v tauv /\
      ResultAgree orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) /\
      AgreeDims orc sigma rho [] [] [] (Basis.tof b) tauv
        (denotBasis sigma b) :=
  Term.progressAndAdequacy call

end Operational
end GLang
