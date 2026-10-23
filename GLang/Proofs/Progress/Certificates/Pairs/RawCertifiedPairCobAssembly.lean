import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairServices
import GLang.Proofs.Progress.Certificates.RawCertifiedGenericCobSyntax

/-!
# Pair-local COB successor assembly

This file isolates the final source/basis cross step.  A positive-depth
pair whose endpoints are space bases cannot be in the frame branch, so its
two endpoint syntax-layer certificates can be fed independently to the
generic COB constructor.  The imported generic COB constructor consumes
those two endpoint layers.
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 6000

namespace GLang
namespace RawCertifiedPairCobAssembly

open RawCertifiedOperational
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedSelectedProgressMaster
open RawCertifiedPairCertificate
open RawCertifiedPairServices
open RawCertifiedGenericCobSyntax

/-- The non-frame payload exposed by a positive pair when both endpoints
are known to be space bases. -/
theorem checkedPairBasisDepth_space_parts
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {source target : Basis}
    (pair : CheckedPairBasisDepth Psi0 (n + 1) Gamma source target)
    (hiSource : Basis.IsSpaceBasis source)
    (hiTarget : Basis.IsSpaceBasis target) :
    Basis.tof target = Basis.tof source /\
    CheckedLocalSideBasisSyntaxLayer Psi0
      (fun Psi' {Gamma'} {b} _hb =>
        CheckedPairBasisDepth Psi' n Gamma' b
          (Basis.std (Basis.tof b))) Gamma source /\
    CheckedLocalSideBasisSyntaxLayer Psi0
      (fun Psi' {Gamma'} {b} _hb =>
        CheckedPairBasisDepth Psi' n Gamma' b
          (Basis.std (Basis.tof b))) Gamma target := by
  cases source <;> cases target <;>
    simp only [CheckedPairBasisDepth, Basis.IsSpaceBasis]
      at pair hiSource hiTarget ⊢ <;>
    aesop

/-- The single mutual step: source progress for the preceding pair depth
constructs COB for both endpoints of every positive-depth space pair. -/
theorem checkedPairSpaceCobDepth_succ_of_termProgress
    (n : Nat)
    (hprogress : forall (Psi0 : EvalCtx), V2.StoredWF Psi0 ->
      CheckedTermProgressWith (CheckedPairSelectedAt Psi0 n) Psi0) :
    CheckedPairSpaceCobDepth (n + 1) := by
  intro Psi0 hrootStored Gamma Psi source target pair hsource htarget hfuture
    hP hcov hwf hiSource hiTarget
  obtain ⟨_htof, sourceSide, targetSide⟩ :=
    checkedPairBasisDepth_space_parts pair hiSource hiTarget
  have endpointCob : CheckedCobToStdSyntax
      (fun Psi' => CheckedPairSelectedAt Psi' n) Psi0 :=
    checkedCobToStdSyntax_of_selectedTermProgress
      (hprogress Psi0 hrootStored)
  constructor
  · apply endpointCob hsource
    · simpa only [CheckedPairSelectedAt] using sourceSide
    · exact hfuture
    · exact hP
    · exact hcov
    · exact hwf
    · exact hiSource
  · apply endpointCob htarget
    · simpa only [CheckedPairSelectedAt] using targetSide
    · exact hfuture
    · exact hP
    · exact hcov
    · exact hwf
    · exact hiTarget

end RawCertifiedPairCobAssembly
end GLang
