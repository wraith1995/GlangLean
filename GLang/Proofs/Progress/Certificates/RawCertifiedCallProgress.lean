import GLang.Proofs.Progress.Certificates.RawCertifiedLocalProgressMaster
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactBasisTyProgress
import GLang.Proofs.Adequacy.OrdinaryBridge
import GLang.Proofs.Progress.Supporting.ProgressCobPaper

namespace GLang
namespace RawCertifiedCallProgress

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedPiBasisTransport
open RawCertifiedLocalProgressMaster
open RawCertifiedExactBasisTyProgress

/-- Current raw consistency implies ordinary standard completeness without
passing through `CtxTele`.  The induction is the actual entry-creation order.
For a new space entry `stdComplete_extend` uses checked-independent ordinary
COB progress at the established prefix carrier.  For a new frame entry,
`pi_entry_transport` uses the same prefix carrier and transports the literal
new variable across a one-key evaluator extension.  Its proof does not inspect
the stored value beyond the local-closure premise already in `RawConsistent`,
so the allowed self-placeholder case is covered. -/
theorem rawConsistent_stdComplete :
    forall {orc : FFSOracleSem}
      {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
      {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem},
      RawConsistent orc Delta Gamma Psi GammaV sigma rho ->
      V2.StdComplete Psi := by
  intro orc Delta Gamma Psi GammaV sigma rho hraw
  induction hraw with
  | empty =>
      exact ⟨fun x b hmem => absurd hmem Finmap.notMem_empty,
        fun x b hmem _ _ _ => absurd hmem Finmap.notMem_empty⟩
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauv xs s yv
      hprefix hx htof hb hTy hinfer hinferSpace hfvv hlc hnr
      hxs hden hagree hdims ih =>
      have hP : V2.PCarrier Psi :=
        ⟨rawConsistent_evalCtxValidPlus_for_bridge hprefix, ih⟩
      have hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi :=
        (V2.varsCovered_of
          (rawConsistent_typingImplyEval_for_bridge hprefix)).drop_lin
      have hev : ValTy.EvalT Psi (Basis.tof b) (ValExpr.inferType v) := by
        rw [hinfer]
        exact hTy
      exact V2.stdComplete_extend hP hcov hb hb.isTyBasis
        (hprefix.freshEvalName hx b) hev
        (fun b0 b1 heq => by
          rw [heq] at htof
          simp [Basis.tof] at htof)
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauv xs yv
      hprefix hx hb hTy hinfer hinferSpace hfvv hlc hnr
      hxs hden hagree hdims _hanchor ih =>
      have hP : V2.PCarrier Psi :=
        ⟨rawConsistent_evalCtxValidPlus_for_bridge hprefix, ih⟩
      have hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi :=
        (V2.varsCovered_of
          (rawConsistent_typingImplyEval_for_bridge hprefix)).drop_lin
      have hev : ValTy.EvalT Psi (Basis.tof b) (ValExpr.inferType v) := by
        rw [hinfer]
        exact hTy
      exact V2.stdComplete_extend hP hcov hb hb.isTyBasis
        (hprefix.freshEvalName hx b) hev
        (fun b0 b1 heq => by
          subst b
          have hvar : ValExpr.OpStep
              (Psi.extend x (.frame b0 b1) v) (.var x)
              (.frame b0 b1) v :=
            .var (by simp [EvalCtx.lookup, EvalCtx.extend,
              Finmap.lookup_insert])
          obtain ⟨k, ⟨hvalid⟩⟩ := hb.tof_tvalid
          exact V2.transportN (Ty.size (Basis.tof (.frame b0 b1)))
            Gamma Psi _ (.var x) (.frame b0 b1)
            (Basis.std (Basis.tof (.frame b0 b1))) v
            hP hcov hprefix.storedWF
            (.step (.refl _) (hprefix.freshEvalName hx _) hlc)
            hb hb.isTyBasis (Basis.std_valid _ hvalid)
            (Basis.isTyBasis_std _) (Basis.tof_std _) le_rfl hvar)
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauv xs yv
      hprefix hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc
      hxs hden hagree hdims _hanchor ih =>
      have hP : V2.PCarrier Psi :=
        ⟨rawConsistent_evalCtxValidPlus_for_bridge hprefix, ih⟩
      have hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi :=
        (V2.varsCovered_of
          (rawConsistent_typingImplyEval_for_bridge hprefix)).drop_lin
      have hev : ValTy.EvalT Psi (Basis.tof b) (ValExpr.inferType v) := by
        rw [hinfer]
        exact hTy
      exact V2.stdComplete_extend hP hcov hb hb.isTyBasis hkey hev
        (fun b0 b1 heq => by
          subst b
          have hvar : ValExpr.OpStep
              (Psi.extend x (.frame b0 b1) v) (.var x)
              (.frame b0 b1) v :=
            .var (by simp [EvalCtx.lookup, EvalCtx.extend,
              Finmap.lookup_insert])
          obtain ⟨k, ⟨hvalid⟩⟩ := hb.tof_tvalid
          exact V2.transportN (Ty.size (Basis.tof (.frame b0 b1)))
            Gamma Psi _ (.var x) (.frame b0 b1)
            (Basis.std (Basis.tof (.frame b0 b1))) v
            hP hcov hprefix.storedWF
            (.step (.refl _) hkey hlc)
            hb hb.isTyBasis (Basis.std_valid _ hvalid)
            (Basis.isTyBasis_std _) (Basis.tof_std _) le_rfl hvar)

/-- The full ordinary carrier used by the checked progress master follows
directly from raw consistency. -/
theorem rawConsistent_pCarrier
    (hraw : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    V2.PCarrier Psi :=
  ⟨rawConsistent_evalCtxValidPlus_for_bridge hraw,
    rawConsistent_stdComplete hraw⟩

/-- The exact operational assumptions used by ordinary progress.

This boundary deliberately contains no denotational environment, oracle, or
adequacy consistency proof.  Those belong to checked soundness, not to the
claim that an ordinary well-typed term can take a step at a valid requested
basis. -/
structure OrdinaryProgressCall
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (e : Term) (b : Basis) : Prop where
  carrier : V2.PCarrier Psi
  varsCovered : V2.VarsCovered Delta Gamma Psi
  storedWF : V2.StoredWF Psi
  typed : Nonempty (HasType Delta Gamma e (Basis.tof b))
  basisValid : Basis.BasisValid Gamma b

theorem OrdinaryProgressCall.isTyBasis
    (call : OrdinaryProgressCall Delta Gamma Psi e b) :
    Basis.IsTyBasis b :=
  call.basisValid.isTyBasis

/-- Ordinary progress from only its operational premises.  Evaluation first
uses the standard basis guaranteed by `carrier`, then transports that exact
ordinary result to the caller's valid requested basis. -/
theorem ordinary_progress
    (call : OrdinaryProgressCall Delta Gamma Psi e b) :
    exists v, ValExpr.OpStep Psi e b v := by
  obtain ⟨vStd, hStd⟩ :=
    V2.opStep_of_hasType_std call.carrier call.varsCovered call.typed
  obtain ⟨_k, ⟨hvalid⟩⟩ := call.basisValid.tof_tvalid
  exact V2.basis_transport Gamma Psi e
    (Basis.std (Basis.tof b)) b vStd
    call.carrier call.varsCovered.drop_lin call.storedWF
    (Basis.std_valid _ hvalid) (Basis.isTyBasis_std _)
    call.basisValid call.isTyBasis (by simp) hStd

/-- Ordinary progress at the requested basis, obtained from standard progress and basis conversion. -/
theorem ordinary_progress_of_rawProgressCall
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b) :
    exists v, ValExpr.OpStep Psi e b v :=
  ordinary_progress {
    carrier := rawConsistent_pCarrier call.consistent.raw
    varsCovered := V2.varsCovered_of
      (rawConsistent_typingImplyEval_for_bridge call.consistent.raw)
    storedWF := call.consistent.raw.storedWF
    typed := call.typed
    basisValid := call.basisValid }

/-- Honest call-shaped checked progress, with both remaining checked mutual
inputs displayed. -/
theorem checked_progress_of_rawProgressCall
    (laws : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    (hexact : CheckedExactBasisTyProgress)
    (htransport : CheckedBasisTransportWF)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (hside : CheckedLocalSideBases Psi ht) :
    exists v tauv, C.Term Delta Gamma Psi e b v tauv := by
  have hroot : CheckedStdStoreRoot Psi :=
    checkedStdStoreRoot_of_rawConsistent_and_transport
      htransport call.consistent.raw
  exact checked_progress_at_root_basis laws happCut hexact htransport hroot
    ht hside (rawConsistent_pCarrier call.consistent.raw)
    (V2.varsCovered_of
      (rawConsistent_typingImplyEval_for_bridge call.consistent.raw))
    (rawConsistent_ctxWF_for_bridge call.consistent.raw)
    call.basisValid call.isTyBasis

/-- Specialization which constructs checked transport from checked COB
progress and the two reviewed higher-order laws. -/
theorem checked_progress_of_rawProgressCall_of_cob
    (laws : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    (hcob : CheckedCobToStd)
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b)
    (ht : HasType Delta Gamma e (Basis.tof b))
    (hside : CheckedLocalSideBases Psi ht) :
    exists v tauv, C.Term Delta Gamma Psi e b v tauv :=
  checked_progress_of_rawProgressCall laws happCut
    (checkedExactBasisTyProgress_of_cob hcob laws)
    (checkedBasisTransportWF_of_arbitraryRename hcob laws happCut)
    call ht hside

end RawCertifiedCallProgress
end GLang
