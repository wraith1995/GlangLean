import GLang.Proofs.Progress.Certificates.Context.RawCertifiedConsistentPairStore

/-!
# Uniform numeric depth for finite exact-pair stores

The construction store assigns each evaluator entry a depth that is already
uniform over all fresh future worlds and well-formed nonlinear-context
extensions.  Since an evaluator is finite, those pointwise depths have a
finite supremum.  Numeric depth monotonicity then raises every entry to that
single depth.

The resulting package retains `CtxWF'` at the point where an extended source
context is consumed.  This is the honest interface needed by variable-leaf
construction: arbitrary `NLCtxIncl` targets need not themselves be well
formed.
-/

namespace GLang
namespace RawCertifiedPairStoreUniformization

open RawCertifiedPairCertificate
open RawCertifiedPairLookupResolver
open RawCertifiedConsistentPairStore

/-- One common exact-quad depth for every lookup in a finite evaluator.  The
depth is chosen before both the lookup and the future-world quantifiers. -/
structure CheckedPairFreshDepthQuadSelectedStoreAt
    (Psi : EvalCtx) (Gamma : NLCtx) (depth : Nat) : Prop where
  resolve : forall {x : VName} {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi (x, b) = some v ->
    forall {Psi' : EvalCtx} {Gamma' : NLCtx},
      CheckedFreshFuture Psi Psi' -> NLCtxIncl Gamma Gamma' ->
      V2.CtxWF' (∅ : LCtx) Gamma' ->
        CheckedPairDepthQuad Psi' depth Gamma' b

private noncomputable def CheckedPairFreshDepthQuadSelectedStore.depthAt
    {Psi : EvalCtx} {Gamma : NLCtx}
    (store : CheckedPairFreshDepthQuadSelectedStore Psi Gamma) :
    VName × Basis -> Nat
  | key =>
      if hmem : key ∈ Psi then
        let found := Finmap.mem_iff.mp hmem
        Classical.choose (store found.choose_spec)
      else 0

private theorem CheckedPairFreshDepthQuadSelectedStore.depthAt_spec
    {Psi : EvalCtx} {Gamma : NLCtx}
    (store : CheckedPairFreshDepthQuadSelectedStore Psi Gamma)
    {x : VName} {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v) :
    forall {Psi' : EvalCtx} {Gamma' : NLCtx},
        CheckedFreshFuture Psi Psi' -> NLCtxIncl Gamma Gamma' ->
      V2.CtxWF' (∅ : LCtx) Gamma' ->
        CheckedPairDepthQuad Psi'
          (CheckedPairFreshDepthQuadSelectedStore.depthAt store (x, b))
          Gamma' b := by
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  simp only [CheckedPairFreshDepthQuadSelectedStore.depthAt, dif_pos hmem]
  let found := Finmap.mem_iff.mp hmem
  intro Psi' Gamma' hfuture hGamma hwf
  exact Classical.choose_spec (store found.choose_spec)
    hfuture hGamma hwf

/-- Finiteness of `Psi` turns the pointwise-finite fresh store into a store
whose exact quads all have one common numeric depth. -/
theorem CheckedPairFreshDepthQuadSelectedStore.exists_atDepth
    {Psi : EvalCtx} {Gamma : NLCtx}
    (store : CheckedPairFreshDepthQuadSelectedStore Psi Gamma) :
    exists depth,
      CheckedPairFreshDepthQuadSelectedStoreAt Psi Gamma depth := by
  classical
  let depth := Psi.keys.sup
    (CheckedPairFreshDepthQuadSelectedStore.depthAt store)
  refine ⟨depth, ⟨?_⟩⟩
  intro x b v hlookup Psi' Gamma' hfuture hGamma hwf
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  have hle : CheckedPairFreshDepthQuadSelectedStore.depthAt store (x, b) ≤
      depth := Finset.le_sup hmem
  exact CheckedPairDepthQuad.monoDepth hle
    (CheckedPairFreshDepthQuadSelectedStore.depthAt_spec store
      hlookup hfuture hGamma hwf)

/-- Root-evaluator selected-to-standard projection at any well-formed
nonlinear-context extension.  This has the same useful conclusion as
`RootSelectedPairsAt`, but keeps the `CtxWF'` premise that its actual
variable-leaf consumers already possess. -/
theorem CheckedPairFreshDepthQuadSelectedStoreAt.toRootSelectedPair
    {Psi : EvalCtx} {Gamma : NLCtx} {depth : Nat}
    (store : CheckedPairFreshDepthQuadSelectedStoreAt Psi Gamma depth)
    {x : VName} {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    {Gamma' : NLCtx} (hGamma : NLCtxIncl Gamma Gamma')
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma') :
    CheckedPairBasisDepth Psi depth Gamma' b
      (Basis.std (Basis.tof b)) :=
  (store.resolve hlookup (CheckedFreshFuture.refl Psi) hGamma hwf).toStd

theorem CheckedPairFreshDepthQuadSelectedStoreAt.toRootSelectedPairsAt
    {Psi : EvalCtx} {Gamma : NLCtx} {depth : Nat}
    (store : CheckedPairFreshDepthQuadSelectedStoreAt Psi Gamma depth)
    (extensionsWF : forall {Gamma' : NLCtx},
      NLCtxIncl Gamma Gamma' -> V2.CtxWF' (∅ : LCtx) Gamma') :
    RootSelectedPairsAt Psi Gamma depth := by
  intro x b v hlookup Gamma' hGamma
  exact store.toRootSelectedPair hlookup hGamma (extensionsWF hGamma)

end RawCertifiedPairStoreUniformization
end GLang
