import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardCertificate
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairStoreUniformization

namespace GLang
namespace RawCertifiedPairFreeStandardStore

open OperationalStrengthening
open RawCertifiedConsistentPairStore
open RawCertifiedPairFreeStandardCertificate
open RawCertifiedPairStoreUniformization

/-- One basis quad, stable at a single chosen depth over arbitrary fresh
evaluator growth and well-formed nonlinear-context growth. -/
def CheckedFreeStdFreshDepthQuadFinite
    (Psi : EvalCtx) (Gamma : NLCtx) (b : Basis) : Prop :=
  exists depth, forall {Psi' : EvalCtx} {Gamma' : NLCtx},
    CheckedFreshFuture Psi Psi' -> NLCtxIncl Gamma Gamma' ->
    V2.CtxWF' (∅ : LCtx) Gamma' ->
      CheckedFreeStdPairDepthQuad Psi' depth Gamma' b

/-- Fixed-depth form of the fresh package. -/
def CheckedFreeStdFreshDepthQuadAt
    (Psi : EvalCtx) (Gamma : NLCtx) (depth : Nat) (b : Basis) : Prop :=
  forall {Psi' : EvalCtx} {Gamma' : NLCtx},
    CheckedFreshFuture Psi Psi' -> NLCtxIncl Gamma Gamma' ->
    V2.CtxWF' (∅ : LCtx) Gamma' ->
      CheckedFreeStdPairDepthQuad Psi' depth Gamma' b

/-- Rebase a fresh package by composing its two extension relations. -/
theorem CheckedFreeStdFreshDepthQuadFinite.rebase
    {Psi Psi' : EvalCtx} {Gamma Gamma' : NLCtx} {b : Basis}
    (p : CheckedFreeStdFreshDepthQuadFinite Psi Gamma b)
    (hfuture : CheckedFreshFuture Psi Psi')
    (hGamma : NLCtxIncl Gamma Gamma') :
    CheckedFreeStdFreshDepthQuadFinite Psi' Gamma' b := by
  obtain ⟨depth, p⟩ := p
  refine ⟨depth, ?_⟩
  intro Psi'' Gamma'' hfuture' hGamma' hwf
  exact p (hfuture.trans hfuture') (hGamma.trans hGamma') hwf

/-- Root projection of one fresh package. -/
theorem CheckedFreeStdFreshDepthQuadFinite.toRoot
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis}
    (p : CheckedFreeStdFreshDepthQuadFinite Psi Gamma b)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma) :
    exists depth, CheckedFreeStdPairDepthQuad Psi depth Gamma b := by
  obtain ⟨depth, p⟩ := p
  exact ⟨depth, p (CheckedFreshFuture.refl Psi)
    (NLCtxIncl.refl Gamma) hwf⟩

/-- Pointwise fresh store at independently chosen depths. -/
def CheckedFreeStdFreshDepthQuadSelectedStore
    (Psi : EvalCtx) (Gamma : NLCtx) : Prop :=
  forall {x : VName} {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi (x, b) = some v ->
      CheckedFreeStdFreshDepthQuadFinite Psi Gamma b

/-- Uniform fixed-depth fresh store over a finite evaluator. -/
def CheckedFreeStdFreshDepthQuadSelectedStoreAt
    (Psi : EvalCtx) (Gamma : NLCtx) (depth : Nat) : Prop :=
  forall {x : VName} {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi (x, b) = some v ->
      CheckedFreeStdFreshDepthQuadAt Psi Gamma depth b

/-- Existential uniform-depth package used by one creation-prefix layer. -/
def CheckedFreeStdFreshDepthQuadUniformStore
    (Psi : EvalCtx) (Gamma : NLCtx) : Prop :=
  exists depth,
    CheckedFreeStdFreshDepthQuadSelectedStoreAt Psi Gamma depth

/-- Raise every entry of a uniform store to a larger common depth. -/
theorem CheckedFreeStdFreshDepthQuadSelectedStoreAt.monoDepth
    {Psi : EvalCtx} {Gamma : NLCtx} {depth depth' : Nat}
    (store : CheckedFreeStdFreshDepthQuadSelectedStoreAt Psi Gamma depth)
    (hle : depth <= depth') :
    CheckedFreeStdFreshDepthQuadSelectedStoreAt Psi Gamma depth' := by
  intro x b v hlookup Psi' Gamma' hfuture hGamma hwf
  exact (store hlookup hfuture hGamma hwf).monoDepth hle

private noncomputable def selectedDepthAt
    {Psi : EvalCtx} {Gamma : NLCtx}
    (store : CheckedFreeStdFreshDepthQuadSelectedStore Psi Gamma) :
    VName × Basis -> Nat
  | (x, b) =>
      if hmem : (x, b) ∈ Psi then
        let found := Finmap.mem_iff.mp hmem
        Classical.choose (store found.choose_spec)
      else 0

private theorem selectedDepthAt_spec
    {Psi : EvalCtx} {Gamma : NLCtx}
    (store : CheckedFreeStdFreshDepthQuadSelectedStore Psi Gamma)
    {x : VName} {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v) :
    CheckedFreeStdFreshDepthQuadAt Psi Gamma
      (selectedDepthAt store (x, b)) b := by
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  simp only [selectedDepthAt, dif_pos hmem]
  let found := Finmap.mem_iff.mp hmem
  intro Psi' Gamma' hfuture hGamma hwf
  exact Classical.choose_spec (store found.choose_spec)
    hfuture hGamma hwf

/-- Finiteness of the evaluator uniformizes all pointwise depths. -/
theorem
    CheckedFreeStdFreshDepthQuadSelectedStore.exists_atDepth
    {Psi : EvalCtx} {Gamma : NLCtx}
    (store : CheckedFreeStdFreshDepthQuadSelectedStore Psi Gamma) :
    CheckedFreeStdFreshDepthQuadUniformStore Psi Gamma := by
  classical
  let depth := Psi.keys.sup (selectedDepthAt store)
  refine ⟨depth, ?_⟩
  intro x b v hlookup Psi' Gamma' hfuture hGamma hwf
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  have hle : selectedDepthAt store (x, b) <= depth :=
    Finset.le_sup hmem
  exact (selectedDepthAt_spec store hlookup hfuture hGamma hwf).monoDepth hle

end RawCertifiedPairFreeStandardStore
end GLang
