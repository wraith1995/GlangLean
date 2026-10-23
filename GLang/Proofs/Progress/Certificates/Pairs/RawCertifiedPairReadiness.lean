import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairCertificate
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedFutureLookupValidity

/-!
# Root/context readiness for dependent standard self pairs

This module packages exactly the two closure properties consumed by a
dependent-frame callback: rebasing in a standard-only future of the evaluator
root, and weakening the nonlinear source context.  The package is a strict
refinement of `CheckedPairBasisDepth`; it projects to that existing public
certificate at the original root and context.

No unrestricted monotonicity theorem for `CheckedPairBasisDepth` is claimed.
Instead, readiness is evidence supplied for the particular canonical pair
being constructed.
-/

namespace GLang
namespace RawCertifiedPairReadiness

open OperationalStrengthening
open RawCertifiedHereditaryStore
open RawCertifiedPairCertificate

/-- A concrete pair certificate together with precisely the future-root and
nonlinear-context stability that dependent standard self construction needs.

The quantifiers range only over futures/extensions of this pair's own root and
source context.  Thus this is a refinement carried by one pair, not a false
global transport principle for arbitrary proof-indexed certificates. -/
def CheckedPairReady (Psi : EvalCtx) (n : Nat) (Gamma : NLCtx)
    (source target : Basis) : Prop :=
  forall {Psi' : EvalCtx} {Gamma' : NLCtx},
    CheckedStdFuture Psi Psi' ->
    NLCtxIncl Gamma Gamma' ->
    CheckedPairBasisDepth Psi' n Gamma' source target

/-- Forget readiness and recover the existing certificate unchanged. -/
theorem CheckedPairReady.toDepth
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {source target : Basis}
    (h : CheckedPairReady Psi n Gamma source target) :
    CheckedPairBasisDepth Psi n Gamma source target :=
  h (CheckedStdFuture.refl Psi) (NLCtxIncl.refl Gamma)

/-- A ready pair may be used at any standard-only future evaluator root. -/
theorem CheckedPairReady.atFuture
    {Psi Psi' : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {source target : Basis}
    (h : CheckedPairReady Psi n Gamma source target)
    (hfuture : CheckedStdFuture Psi Psi') :
    CheckedPairBasisDepth Psi' n Gamma source target :=
  h hfuture (NLCtxIncl.refl Gamma)

/-- A ready pair may be used after extending its nonlinear source context. -/
theorem CheckedPairReady.atNLCtx
    {Psi : EvalCtx} {n : Nat} {Gamma Gamma' : NLCtx}
    {source target : Basis}
    (h : CheckedPairReady Psi n Gamma source target)
    (hle : NLCtxIncl Gamma Gamma') :
    CheckedPairBasisDepth Psi n Gamma' source target :=
  h (CheckedStdFuture.refl Psi) hle

/-- Readiness itself is stable when its evaluator root is rebased forward. -/
theorem CheckedPairReady.rebase
    {Psi Psi' : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {source target : Basis}
    (h : CheckedPairReady Psi n Gamma source target)
    (hfuture : CheckedStdFuture Psi Psi') :
    CheckedPairReady Psi' n Gamma source target := by
  intro Psi'' Gamma'' hfuture' hle
  exact h (CheckedStdFuture.trans hfuture hfuture') hle

/-- Readiness itself is stable under nonlinear-context inclusion. -/
theorem CheckedPairReady.nlMono
    {Psi : EvalCtx} {n : Nat} {Gamma Gamma' : NLCtx}
    {source target : Basis}
    (h : CheckedPairReady Psi n Gamma source target)
    (hle : NLCtxIncl Gamma Gamma') :
    CheckedPairReady Psi n Gamma' source target := by
  intro Psi'' Gamma'' hfuture hle'
  exact h hfuture (NLCtxIncl.trans hle hle')

/-- The fresh insertion needed below a dependent frame is one ordinary
instance of readiness's nonlinear-context closure. -/
theorem CheckedPairReady.freshInsert
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {source target : Basis} {y : Name} {tau : Ty}
    (h : CheckedPairReady Psi n Gamma source target)
    (hy : y ∉ Gamma) :
    CheckedPairReady Psi n (Finmap.insert y tau Gamma) source target :=
  h.nlMono ((NLCtxIncl.refl Gamma).insert_right hy tau)

/-- The exact combined elimination used in a dependent-frame callback:
advance the evaluator root and install one fresh source binder. -/
theorem CheckedPairReady.atFutureFreshInsert
    {Psi Psi' : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {source target : Basis} {y : Name} {tau : Ty}
    (h : CheckedPairReady Psi n Gamma source target)
    (hfuture : CheckedStdFuture Psi Psi')
    (hy : y ∉ Gamma) :
    CheckedPairBasisDepth Psi' n (Finmap.insert y tau Gamma)
      source target :=
  h hfuture ((NLCtxIncl.refl Gamma).insert_right hy tau)

/-- Dependent standard self construction with local readiness evidence.

The opened codomain is already constructed in its binder-extended source
context.  Its readiness is used only to rebase to the callback world.  The
domain pair is constructed outside the binder, so its readiness supplies both
the fresh context insertion and the callback-world rebase. -/
theorem checkedStdPiSelf_of_ready
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {tau0 tau1 : Ty} {k0 k1 : Kind} {L : Finset Name}
    (h0 : TValid Gamma tau0 k0)
    (hbody : forall y, y ∉ L ->
      TValid (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1)
    (domainReady : CheckedPairReady Psi (n + 1) Gamma
      (Basis.std tau0) (Basis.std tau0))
    (bodyReady : forall y (_hy : y ∉ L),
      CheckedPairReady Psi (n + 1) (Finmap.insert y tau0 Gamma)
        (Basis.std (Ty.openVar y tau1))
        (Basis.std (Ty.openVar y tau1))) :
    CheckedPairBasisDepth Psi (n + 1) Gamma
      (Basis.std (.piTy tau0 tau1)) (Basis.std (.piTy tau0 tau1)) := by
  let avoid : Finset Name := L ∪ Gamma.keys
  have hdomValid : Basis.BasisValid Gamma (Basis.std tau0) :=
    Basis.std_valid tau0 h0
  have hbodyValid : forall y, y ∉ avoid ->
      Basis.BasisValid (Finmap.insert y (Basis.tof (Basis.std tau0)) Gamma)
        (Basis.openVar y (Basis.std tau1)) := by
    intro y hy
    have hyParts : y ∉ L ∧ y ∉ Gamma.keys := by
      simpa only [avoid, Finset.mem_union, not_or] using hy
    rw [← Basis.std_openVar]
    simpa only [Basis.tof_std] using
      Basis.std_valid _ (hbody y hyParts.1)
  simp only [Basis.std]
  unfold CheckedPairBasisDepth
  refine ⟨rfl, rfl, avoid, avoid, hdomValid, hdomValid,
    hbodyValid, hbodyValid, domainReady.toDepth, domainReady.toDepth,
    ?_, ?_, ?_⟩
  · intro Psi' hfuture y hyPsi hyAvoid tauV hTyAt
    have hyParts : y ∉ L ∧ y ∉ Gamma.keys := by
      simpa only [avoid, Finset.mem_union, not_or] using hyAvoid
    have hfutureX : CheckedStdFuture Psi
        (Psi'.extend y (Basis.std tau0) (.var y tauV)) :=
      CheckedStdFuture.extend_std hfuture hyPsi tau0 (.var y tauV)
    simpa only [Basis.tof_std, Basis.std_openVar] using
      CheckedPairReady.atFuture (bodyReady y hyParts.1) hfutureX
  · intro Psi' hfuture y hyPsi hyAvoid tauV hTyAt
    have hyParts : y ∉ L ∧ y ∉ Gamma.keys := by
      simpa only [avoid, Finset.mem_union, not_or] using hyAvoid
    have hfutureX : CheckedStdFuture Psi
        (Psi'.extend y (Basis.std tau0) (.var y tauV)) :=
      CheckedStdFuture.extend_std hfuture hyPsi tau0 (.var y tauV)
    simpa only [Basis.tof_std, Basis.std_openVar] using
      CheckedPairReady.atFuture (bodyReady y hyParts.1) hfutureX
  · intro Psi' hfuture y hyPsi hySource hyTarget tauV hTyAt
    have hyParts : y ∉ L ∧ y ∉ Gamma.keys := by
      simpa only [avoid, Finset.mem_union, not_or] using hySource
    have hyGamma : y ∉ Gamma := by
      exact fun hyMem => hyParts.2 (Finmap.mem_keys.mpr hyMem)
    have hfutureX : CheckedStdFuture Psi
        (Psi'.extend y (Basis.std tau0) (.var y tauV)) :=
      CheckedStdFuture.extend_std hfuture hyPsi tau0 (.var y tauV)
    constructor
    · simpa only [Basis.tof_std] using
        domainReady.atFutureFreshInsert hfutureX hyGamma
    · simpa only [Basis.tof_std, Basis.std_openVar] using
        CheckedPairReady.atFuture (bodyReady y hyParts.1) hfutureX

end RawCertifiedPairReadiness
end GLang
