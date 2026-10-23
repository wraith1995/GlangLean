import GLang.Proofs.Progress.Certificates.Context.RawCertifiedCtxTeleProgress

namespace GLang
namespace RawCertifiedCtxTeleCategoryProgress

open RawCertifiedOperational
open OperationalStrengthening
open RawCertifiedHereditaryStore
open RawCertifiedPairFreeStandardCertificate
open RawCertifiedPairFreeStandardStore
open RawCertifiedPairFreeStandardCreationPrefixLayer
open RawCertifiedPairFreeStandardNatProgress
open RawCertifiedCtxTeleProgress

/-- Every valid requested basis has an exact checked type realization under a
semantic-free creation history. -/
theorem checkedTyAt
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi)
    {b : Basis} (hb : Basis.BasisValid Gamma b) :
    exists tauV, C.TyAt Gamma Psi b tauV := by
  obtain ⟨storeDepth, store⟩ :=
    CheckedFreeStdFreshDepthQuadSelectedStore.exists_atDepth
      (checkedFreeStdFreshDepthQuadSelectedStore htele)
  have package : CheckedFreeStdFreshDepthQuadFinite Psi Gamma b :=
    checkedFreeStdCreationPrefixLayerBuilder (ctxWFPrime htele)
      (typingImplyEval htele) ⟨storeDepth, store⟩ hb
  obtain ⟨depth, quad⟩ := package.toRoot
    (RawCertifiedWorldBinderProgress.ctxWF_dropLin (ctxWFPrime htele))
  let services := checkedFreeStdDepthServices_all
    RawCertifiedOperational.RenameProof.checkedRenameLaws
    RawCertifiedOperational.checkedTyAtAppCut depth
  exact services.targetExact Psi htele.storedWF Gamma Psi b b quad.self
    hb hb (CheckedStdFuture.refl Psi)
    (checkedExactLookupStore htele)
    (htele.pCarrier V2.pi_entry_transport) htele.varsCovered.drop_lin
    htele.storedWF Delta (ctxWFPrime htele) hb.isTyBasis hb.isTyBasis rfl

/-- Exact checked type progress, restated at the source type named by the
requested basis. -/
theorem checkedTyAtSource
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi)
    {tau : Ty}
    {b : Basis} (hb : Basis.BasisValid Gamma b)
    (htof : Basis.tof b = tau) :
    exists tauV, C.TyAt Gamma Psi b tauV /\ C.Ty Gamma Psi tau tauV := by
  obtain ⟨tauV, htyAt⟩ := checkedTyAt htele hb
  have hty : C.Ty Gamma Psi (Basis.tof b) tauV :=
    RawCertifiedOperational.S.Ty.toC
      (RawCertifiedOperational.C.TyAt.toS htyAt).toTy
  rw [htof] at hty
  exact ⟨tauV, htyAt, hty⟩

/-- A valid source type is realized by the canonical checked type evaluator.
Its standard basis supplies the exact dependent-frame choices internally. -/
theorem checkedTy
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi)
    {tau : Ty} {k : Kind} (htau : TValid Gamma tau k) :
    exists tauV, C.Ty Gamma Psi tau tauV := by
  let b := Basis.std tau
  have hb : Basis.BasisValid Gamma b := Basis.std_valid _ htau
  obtain ⟨tauV, _htyAt, hty⟩ :=
    checkedTyAtSource (tau := tau) htele hb (by simp [b])
  exact ⟨tauV, hty⟩

/-- A valid source space is realized by the canonical checked space evaluator.
This is the base-kind specialization of exact checked type progress. -/
theorem checkedSpace
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi)
    {s : Space} (hs : SValid Gamma s) :
    exists sv, C.Space Gamma Psi s sv := by
  let b := Basis.std (.space s)
  have hb : Basis.BasisValid Gamma b := Basis.std_valid _ (.space hs)
  obtain ⟨tauV, htyAt⟩ := checkedTyAt htele hb
  obtain ⟨sv, htauV, hspace⟩ :=
    RawCertifiedProgressScratch.checkedTyAt_space_inv
      (b := b) (s := s) (by simp [b]) htyAt
  subst tauV
  exact ⟨sv, by simpa [b, Basis.std] using hspace⟩

/-- A valid hereditary space basis converts to the literal standard basis of
its source type in the canonical checked COB judgment. -/
theorem checkedCobToStandard
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi)
    {b : Basis} (hb : Basis.BasisValid Gamma b)
    (htof : Basis.tof b = .space (Basis.sof b)) :
    exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b)) := by
  have hspace := hb.isTyBasis.toIsSpaceBasis_of_tof_eq htof
  obtain ⟨storeDepth, store⟩ :=
    CheckedFreeStdFreshDepthQuadSelectedStore.exists_atDepth
      (checkedFreeStdFreshDepthQuadSelectedStore htele)
  have package : CheckedFreeStdFreshDepthQuadFinite Psi Gamma b :=
    checkedFreeStdCreationPrefixLayerBuilder (ctxWFPrime htele)
      (typingImplyEval htele) ⟨storeDepth, store⟩ hb
  obtain ⟨depth, quad⟩ := package.toRoot
    (RawCertifiedWorldBinderProgress.ctxWF_dropLin (ctxWFPrime htele))
  let services := checkedFreeStdDepthServices_all
    RawCertifiedOperational.RenameProof.checkedRenameLaws
    RawCertifiedOperational.checkedTyAtAppCut depth
  obtain ⟨kind, ⟨htau⟩⟩ := hb.tof_tvalid
  have hstd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
    Basis.std_valid _ htau
  have hstdSpace : Basis.IsSpaceBasis (Basis.std (Basis.tof b)) := by
    rw [hspace.std_tof_eq]
    exact Basis.isSpaceBasis_stdSpace (Basis.sof b)
  exact (services.spaceCob Psi htele.storedWF Gamma Psi b
    (Basis.std (Basis.tof b)) quad.toStd hb hstd
    (CheckedStdFuture.refl Psi) (checkedExactLookupStore htele)
    (htele.pCarrier V2.pi_entry_transport) htele.varsCovered.drop_lin
    (RawCertifiedWorldBinderProgress.ctxWF_dropLin (ctxWFPrime htele))
    hspace hstdSpace).1

end RawCertifiedCtxTeleCategoryProgress
end GLang
