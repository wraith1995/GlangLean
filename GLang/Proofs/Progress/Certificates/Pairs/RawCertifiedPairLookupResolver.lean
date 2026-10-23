import GLang.Proofs.Adequacy.Raw.Context.RawConsistentRankedLookup
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairDepthMonotonicity

/-!
# Variable-leaf resolver for automatic pair certificates

The source-tree construction and the stored-basis construction meet only at
a variable leaf.  This module records that seam without assuming the final
local-call certificate.

An exact lookup in a standard-only future has two cases: an unchanged root
entry, or a new literal standard basis.  Consequently a leaf needs only a
pair for each root entry and a self-pair for the source type of a new standard
entry.  `RawConsistent` supplies basis validity in both cases.
-/

namespace GLang
namespace RawCertifiedPairLookupResolver

open OperationalStrengthening
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate
open RawCertifiedPairDepthMonotonicity

/-- Fixed-depth pairs for the entries of one raw-consistent root, stable under
the nonlinear source-context extensions introduced by source binders. -/
def RootSelectedPairsAt (Psi0 : EvalCtx) (Gamma0 : NLCtx)
    (depth : Nat) : Prop :=
  forall {x : VName} {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi0 (x, b) = some v ->
    forall {Gamma : NLCtx}, NLCtxIncl Gamma0 Gamma ->
      CheckedPairBasisDepth Psi0 depth Gamma b
        (Basis.std (Basis.tof b))

/-- The one fixed-depth standard self-pair needed by a particular variable
leaf.  Keeping the source type explicit avoids the false uniform claim that
one depth handles every type in the language. -/
def StandardSelfAt (Psi0 : EvalCtx) (depth : Nat)
    (Gamma : NLCtx) (tau : Ty) : Prop :=
  CheckedPairBasisDepth Psi0 depth Gamma
    (Basis.std tau) (Basis.std tau)

/-- Root-entry availability persists when the common numeric depth is raised. -/
theorem RootSelectedPairsAt.monoDepth
    {Psi0 : EvalCtx} {Gamma0 : NLCtx} {n m : Nat}
    (hnm : n ≤ m) (h : RootSelectedPairsAt Psi0 Gamma0 n) :
    RootSelectedPairsAt Psi0 Gamma0 m := by
  intro x b v hlookup Gamma hGamma
  exact pairDepth_mono hnm (h hlookup hGamma)

/-- The same numeric lift for one standard self-pair. -/
theorem StandardSelfAt.monoDepth
    {Psi0 : EvalCtx} {Gamma : NLCtx} {tau : Ty} {n m : Nat}
    (hnm : n ≤ m) (h : StandardSelfAt Psi0 n Gamma tau) :
    StandardSelfAt Psi0 m Gamma tau :=
  pairDepth_mono hnm h

/-- The linear-variable leaf is discharged by the root/standard lookup split.
The well-formed local context supplies formation of its source space. -/
theorem var_lin
    {orc : FFSOracleSem}
    {Delta0 : LCtx} {Gamma0 : NLCtx} {Psi0 : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (hconsistent : RawConsistent orc Delta0 Gamma0 Psi0 GammaV sigma rho)
    {depth : Nat}
    (hrootPairs : RootSelectedPairsAt Psi0 Gamma0 depth)
    {Gamma : NLCtx} (hGamma : NLCtxIncl Gamma0 Gamma)
    {x : VName} {s : Space}
    (hwf : V2.CtxWF' (Finmap.singleton x s) Gamma)
    (hstandard : StandardSelfAt Psi0 depth Gamma (.space s)) :
    CheckedLocalTermSideBasisWith
      (CheckedPairSelectedAt Psi0 depth) Psi0
      (HasType.var_lin :
        HasType (Finmap.singleton x s) Gamma (.var x) (.space s)) := by
  intro Psi hfuture
  refine ⟨?_, ?_⟩
  · intro hcov
    obtain ⟨b, hmem, htof⟩ :=
      hcov.1 x s Finmap.lookup_singleton_eq
    obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp hmem
    obtain ⟨hs⟩ := hwf.lin_valid x s Finmap.lookup_singleton_eq
    have htofv : TValid Gamma (Basis.tof b) .base := by
      rw [htof]
      exact .space hs
    have hb := hfuture.lookup_basisValid_of_rawConsistent
      hconsistent hlookup hGamma htofv
    refine ⟨b, v, hlookup, htof, hb, ?_⟩
    rcases RawConsistentRank.CheckedStdFuture.lookup_root_or_standard
        hfuture hlookup with hroot | hextra
    · exact hrootPairs hroot hGamma
    · obtain ⟨_hnotRoot, hstd, _hfresh⟩ := hextra
      change CheckedPairBasisDepth Psi0 depth Gamma b
        (Basis.std (Basis.tof b))
      exact Eq.mpr
        (congrArg
          (fun source => CheckedPairBasisDepth Psi0 depth Gamma source
            (Basis.std (Basis.tof b))) hstd)
        (by simpa only [htof] using hstandard)
  · intro b v hlookup htof
    obtain ⟨hs⟩ := hwf.lin_valid x s Finmap.lookup_singleton_eq
    have htofv : TValid Gamma (Basis.tof b) .base := by
      rw [htof]
      exact .space hs
    exact hfuture.lookup_basisValid_of_rawConsistent
      hconsistent hlookup hGamma htofv

/-- Nonlinear variables use the same split.  Here formation of the source
type is recovered from the nonlinear binding in the well-formed context. -/
theorem var_nlin
    {orc : FFSOracleSem}
    {Delta0 : LCtx} {Gamma0 : NLCtx} {Psi0 : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (hconsistent : RawConsistent orc Delta0 Gamma0 Psi0 GammaV sigma rho)
    {depth : Nat}
    (hrootPairs : RootSelectedPairsAt Psi0 Gamma0 depth)
    {Gamma : NLCtx} (hGamma : NLCtxIncl Gamma0 Gamma)
    {x : VName} {tau : Ty} (hlookupGamma : Gamma.lookup x = some tau)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hstandard : StandardSelfAt Psi0 depth Gamma tau) :
    CheckedLocalTermSideBasisWith
      (CheckedPairSelectedAt Psi0 depth) Psi0
      (HasType.var_nlin hlookupGamma :
        HasType (∅ : LCtx) Gamma (.var x) tau) := by
  intro Psi hfuture
  refine ⟨?_, ?_⟩
  · intro hcov
    obtain ⟨b, hmem, htof⟩ := hcov.2 x tau hlookupGamma
    obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp hmem
    obtain ⟨k, ⟨htau⟩⟩ := hwf.nl_valid x tau hlookupGamma
    have htofv : TValid Gamma (Basis.tof b) k := by
      rw [htof]
      exact htau
    have hb := hfuture.lookup_basisValid_of_rawConsistent
      hconsistent hlookup hGamma htofv
    refine ⟨b, v, hlookup, htof, hb, ?_⟩
    rcases RawConsistentRank.CheckedStdFuture.lookup_root_or_standard
        hfuture hlookup with hroot | hextra
    · exact hrootPairs hroot hGamma
    · obtain ⟨_hnotRoot, hstd, _hfresh⟩ := hextra
      change CheckedPairBasisDepth Psi0 depth Gamma b
        (Basis.std (Basis.tof b))
      exact Eq.mpr
        (congrArg
          (fun source => CheckedPairBasisDepth Psi0 depth Gamma source
            (Basis.std (Basis.tof b))) hstd)
        (by simpa only [htof] using hstandard)
  · intro b v hlookup htof
    obtain ⟨k, ⟨htau⟩⟩ := hwf.nl_valid x tau hlookupGamma
    have htofv : TValid Gamma (Basis.tof b) k := by
      rw [htof]
      exact htau
    exact hfuture.lookup_basisValid_of_rawConsistent
      hconsistent hlookup hGamma htofv

end RawCertifiedPairLookupResolver
end GLang
