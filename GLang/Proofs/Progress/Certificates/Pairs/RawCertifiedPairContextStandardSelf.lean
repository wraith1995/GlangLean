import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairStoreUniformization

/-!
# Stable standard-self evidence for the current source context

Source-tree variable leaves need a standard self-pair only for a type that is
actually bound in the current linear or nonlinear context.  This module
records exactly those pairs.  Each field is stable under later *well-formed*
nonlinear extensions, matching the context evidence carried by the source
traversal; it does not quantify over arbitrary types at one fixed depth.

The elementary operations mirror source traversal: restrict the linear
context, or insert one fresh linear/nonlinear binder whose standard self-pair
is projected from a fresh-world exact quad.  Mutual source/basis recursion is
deliberately outside this module.
-/

namespace GLang
namespace RawCertifiedPairContextStandardSelf

open RawCertifiedPairCertificate
open RawCertifiedPairLookupResolver
open RawCertifiedConsistentPairStore

/-- Exact quad construction at a fixed depth, stable over fresh evaluator
growth and well-formed nonlinear-context growth.  This is the non-existential
body of `CheckedPairFreshDepthQuadFinite`. -/
def CheckedPairFreshDepthQuadAt
    (Psi : EvalCtx) (Gamma : NLCtx) (depth : Nat) (b : Basis) : Prop :=
  forall {Psi' : EvalCtx} {Gamma' : NLCtx},
    CheckedFreshFuture Psi Psi' -> NLCtxIncl Gamma Gamma' ->
    V2.CtxWF' (∅ : LCtx) Gamma' ->
      CheckedPairDepthQuad Psi' depth Gamma' b

/-- The existential package is exactly a choice of depth and a stable exact
quad at that depth. -/
theorem checkedPairFreshDepthQuadFinite_iff_exists_at
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis} :
    CheckedPairFreshDepthQuadFinite Psi Gamma b <->
      exists depth, CheckedPairFreshDepthQuadAt Psi Gamma depth b :=
  Iff.rfl

/-- Rebase a fixed-depth fresh quad while preserving its chosen depth. -/
theorem CheckedPairFreshDepthQuadAt.rebase
    {Psi Psi' : EvalCtx} {Gamma Gamma' : NLCtx}
    {depth : Nat} {b : Basis}
    (q : CheckedPairFreshDepthQuadAt Psi Gamma depth b)
    (hfuture : CheckedFreshFuture Psi Psi')
    (hGamma : NLCtxIncl Gamma Gamma') :
    CheckedPairFreshDepthQuadAt Psi' Gamma' depth b := by
  intro Psi'' Gamma'' hfuture' hGamma' hwf
  exact q (hfuture.trans hfuture') (hGamma.trans hGamma') hwf

/-- Raise the common numeric depth without changing either stability
quantifier. -/
theorem CheckedPairFreshDepthQuadAt.monoDepth
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis} {n m : Nat}
    (hnm : n ≤ m) (q : CheckedPairFreshDepthQuadAt Psi Gamma n b) :
    CheckedPairFreshDepthQuadAt Psi Gamma m b := by
  intro Psi' Gamma' hfuture hGamma hwf
  exact CheckedPairDepthQuad.monoDepth hnm (q hfuture hGamma hwf)

/-- A pointwise inclusion used only to forget linear bindings while keeping
the nonlinear root fixed. -/
def LinearCtxIncl (DeltaSmall DeltaBig : LCtx) : Prop :=
  forall x s, DeltaSmall.lookup x = some s ->
    DeltaBig.lookup x = some s

theorem LinearCtxIncl.refl (Delta : LCtx) : LinearCtxIncl Delta Delta :=
  fun _ _ h => h

theorem LinearCtxIncl.trans
    {Delta0 Delta1 Delta2 : LCtx}
    (h01 : LinearCtxIncl Delta0 Delta1)
    (h12 : LinearCtxIncl Delta1 Delta2) :
    LinearCtxIncl Delta0 Delta2 :=
  fun x s h => h12 x s (h01 x s h)

/-- Standard self-pairs for precisely the variables bound in `Delta` and
`Gamma`.  Each stored binding remains available in every fresh evaluator
future and every later well-formed nonlinear extension of `Gamma`. -/
structure CheckedContextStandardSelfAt
    (Psi : EvalCtx) (depth : Nat) (Delta : LCtx) (Gamma : NLCtx) : Prop where
  lin : forall {x : VName} {s : Space},
    Delta.lookup x = some s ->
    forall {Psi' : EvalCtx} {Gamma' : NLCtx},
      CheckedFreshFuture Psi Psi' -> NLCtxIncl Gamma Gamma' ->
      V2.CtxWF' (∅ : LCtx) Gamma' ->
        StandardSelfAt Psi' depth Gamma' (.space s)
  nlin : forall {x : VName} {tau : Ty},
    Gamma.lookup x = some tau ->
    forall {Psi' : EvalCtx} {Gamma' : NLCtx},
      CheckedFreshFuture Psi Psi' -> NLCtxIncl Gamma Gamma' ->
      V2.CtxWF' (∅ : LCtx) Gamma' ->
        StandardSelfAt Psi' depth Gamma' tau

/-- Initialize the dynamic context service from source/evaluator linkage and
the uniform fresh root store.  `TypingImplyEval` selects the root basis for
each actual source binding and identifies its `tof`; the quad's `stdSelf`
field supplies the requested pair.  The well-formedness used for a later
nonlinear context is taken from the service call itself, so no global
all-extensions-WF premise is introduced. -/
theorem CheckedContextStandardSelfAt.of_storeAt
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    (hlink : V2.TypingImplyEval Delta Gamma Psi)
    (store :
      RawCertifiedPairStoreUniformization.CheckedPairFreshDepthQuadSelectedStoreAt
        Psi Gamma depth) :
    CheckedContextStandardSelfAt Psi depth Delta Gamma where
  lin := by
    intro x s hlookup Psi' Gamma' hfuture hGamma hwf
    obtain ⟨b, hmem⟩ := (hlink.1 x).mp
      (Or.inl (Finmap.mem_iff.mpr ⟨s, hlookup⟩))
    obtain ⟨v, hlookupPsi⟩ := Finmap.mem_iff.mp hmem
    have htof : Basis.tof b = .space s :=
      hlink.2.1 x s b hlookup hmem
    simpa only [htof] using
      (store.resolve hlookupPsi hfuture hGamma hwf).stdSelf
  nlin := by
    intro x tau hlookup Psi' Gamma' hfuture hGamma hwf
    obtain ⟨b, hmem⟩ := (hlink.1 x).mp
      (Or.inr (Finmap.mem_iff.mpr ⟨tau, hlookup⟩))
    obtain ⟨v, hlookupPsi⟩ := Finmap.mem_iff.mp hmem
    have htof : Basis.tof b = tau :=
      hlink.2.2.1 x tau b hlookup hmem
    simpa only [htof] using
      (store.resolve hlookupPsi hfuture hGamma hwf).stdSelf

/-- Project a linear binding at the service's current nonlinear context. -/
theorem CheckedContextStandardSelfAt.linCurrent
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    (self : CheckedContextStandardSelfAt Psi depth Delta Gamma)
    {x : VName} {s : Space} (hlookup : Delta.lookup x = some s)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma) :
    StandardSelfAt Psi depth Gamma (.space s) :=
  self.lin hlookup (CheckedFreshFuture.refl Psi)
    (NLCtxIncl.refl Gamma) hwf

/-- Project a nonlinear binding at the service's current context. -/
theorem CheckedContextStandardSelfAt.nlinCurrent
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    (self : CheckedContextStandardSelfAt Psi depth Delta Gamma)
    {x : VName} {tau : Ty} (hlookup : Gamma.lookup x = some tau)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma) :
    StandardSelfAt Psi depth Gamma tau :=
  self.nlin hlookup (CheckedFreshFuture.refl Psi)
    (NLCtxIncl.refl Gamma) hwf

/-- Move the service's evaluator root forward.  All stored bindings are
replayed through the original service's fresh-world quantifier. -/
theorem CheckedContextStandardSelfAt.rebase
    {Psi Psi' : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    (self : CheckedContextStandardSelfAt Psi depth Delta Gamma)
    (hfuture : CheckedFreshFuture Psi Psi') :
    CheckedContextStandardSelfAt Psi' depth Delta Gamma where
  lin hlookup _ _ hfuture' hGamma hwf :=
    self.lin hlookup (hfuture.trans hfuture') hGamma hwf
  nlin hlookup _ _ hfuture' hGamma hwf :=
    self.nlin hlookup (hfuture.trans hfuture') hGamma hwf

/-- Forget linear bindings.  Pair evidence depends only on the nonlinear
target context, so no reconstruction of certificates is required. -/
theorem CheckedContextStandardSelfAt.restrictLinear
    {Psi : EvalCtx} {depth : Nat} {DeltaSmall DeltaBig : LCtx}
    {Gamma : NLCtx}
    (self : CheckedContextStandardSelfAt Psi depth DeltaBig Gamma)
    (hDelta : LinearCtxIncl DeltaSmall DeltaBig) :
    CheckedContextStandardSelfAt Psi depth DeltaSmall Gamma where
  lin hlookup := self.lin (hDelta _ _ hlookup)
  nlin hlookup := self.nlin hlookup

/-- Insert one fresh linear binding. -/
theorem CheckedContextStandardSelfAt.insertLinear
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    (self : CheckedContextStandardSelfAt Psi depth Delta Gamma)
    {y : Name} {s : Space} {b : Basis}
    (_hyDelta : y ∉ Delta) (_hyGamma : y ∉ Gamma)
    (htof : Basis.tof b = .space s)
    (quad : CheckedPairFreshDepthQuadAt Psi Gamma depth b) :
    CheckedContextStandardSelfAt Psi depth
      (Finmap.insert y s Delta) Gamma where
  lin := by
    intro x sx hlookup Psi' Gamma' hfuture hGamma hwf
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      simpa only [htof] using
        (quad hfuture hGamma hwf).stdSelf
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact self.lin hlookup hfuture hGamma hwf
  nlin hlookup := self.nlin hlookup

/-- Insert one fresh nonlinear binding. -/
theorem CheckedContextStandardSelfAt.insertNonlinear
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    (self : CheckedContextStandardSelfAt Psi depth Delta Gamma)
    {y : Name} {tau : Ty} {b : Basis}
    (_hyDelta : y ∉ Delta) (hyGamma : y ∉ Gamma)
    (htof : Basis.tof b = tau)
    (quad : CheckedPairFreshDepthQuadAt Psi Gamma depth b) :
    CheckedContextStandardSelfAt Psi depth Delta
      (Finmap.insert y tau Gamma) where
  lin := by
    intro x s hlookup Psi' Gamma' hfuture hGamma hwf
    exact self.lin hlookup hfuture
      ((NLCtxIncl.refl Gamma).insert_right hyGamma tau |>.trans hGamma)
      hwf
  nlin := by
    intro x tauX hlookup Psi' Gamma' hfuture hGamma hwf
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      have hbase : NLCtxIncl Gamma Gamma' :=
        ((NLCtxIncl.refl Gamma).insert_right hyGamma tau).trans hGamma
      simpa only [htof] using
        (quad hfuture hbase hwf).stdSelf
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact self.nlin hlookup hfuture
        ((NLCtxIncl.refl Gamma).insert_right hyGamma tau |>.trans hGamma)
        hwf

end RawCertifiedPairContextStandardSelf
end GLang
