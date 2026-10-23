import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairContextStandardSelf

/-!
# Stable selected-pair evidence for the current source context

A standard-self-only context service is insufficient below a dependent-frame
endpoint: the frame callback installs the literal endpoint basis, which may
be nonstandard.  A variable referring to that binder must therefore obtain
the selected-to-standard orientation of that exact basis.

This module records, for each actual source-context binding, both:

* a fresh-stable exact quad for every matching key already in the current
  evaluator root; and
* a fresh-stable exact quad for the corresponding standard basis, used when a
  source binder appears only in a standard future.

The interface remains finite and context-indexed.  It does not quantify over
unrelated valid types or bases.
-/

namespace GLang
namespace RawCertifiedPairContextSelected

open OperationalStrengthening
open RawCertifiedHereditaryStore
open RawCertifiedPairCertificate
open RawCertifiedConsistentPairStore
open RawCertifiedPairStoreUniformization
open RawCertifiedPairContextStandardSelf

/-- A valid selected basis together with its exact quad, stable at one fixed
depth over fresh evaluator and well-formed nonlinear-context growth. -/
structure CheckedFreshSelectedAt
    (Psi : EvalCtx) (Gamma : NLCtx) (depth : Nat) (b : Basis) : Prop where
  valid : Basis.BasisValid Gamma b
  quad : CheckedPairFreshDepthQuadAt Psi Gamma depth b

/-- Rebase a selected package without changing its chosen numeric depth. -/
theorem CheckedFreshSelectedAt.rebase
    {Psi Psi' : EvalCtx} {Gamma Gamma' : NLCtx} {depth : Nat} {b : Basis}
    (p : CheckedFreshSelectedAt Psi Gamma depth b)
    (hfuture : CheckedFreshFuture Psi Psi')
    (hGamma : NLCtxIncl Gamma Gamma') :
    CheckedFreshSelectedAt Psi' Gamma' depth b where
  valid := raw_basisValid_mono p.valid hGamma
  quad := CheckedPairFreshDepthQuadAt.rebase p.quad hfuture hGamma

/-- Raise a selected package to a larger common cross depth. -/
theorem CheckedFreshSelectedAt.monoDepth
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis} {n m : Nat}
    (hnm : n ≤ m) (p : CheckedFreshSelectedAt Psi Gamma n b) :
    CheckedFreshSelectedAt Psi Gamma m b where
  valid := p.valid
  quad := CheckedPairFreshDepthQuadAt.monoDepth hnm p.quad

/-- The standard orientation of a quad is itself a full quad: all four
orientations of `std (tof b)` are definitionally the original `stdSelf`
field. -/
theorem CheckedFreshSelectedAt.toStandard
    {Psi : EvalCtx} {Gamma : NLCtx} {depth : Nat} {b : Basis}
    (p : CheckedFreshSelectedAt Psi Gamma depth b) :
    CheckedFreshSelectedAt Psi Gamma depth (Basis.std (Basis.tof b)) := by
  obtain ⟨k, ⟨ht⟩⟩ := p.valid.tof_tvalid
  refine ⟨Basis.std_valid (Basis.tof b) ht, ?_⟩
  intro Psi' Gamma' hfuture hGamma hwf
  have q := p.quad hfuture hGamma hwf
  refine {
    self := ?_
    toStd := ?_
    fromStd := ?_
    stdSelf := ?_ }
  all_goals simpa only [Basis.tof_std] using q.stdSelf

/-- Pair service for one source binding of type `tau`.  `root` handles exact
keys installed at the service root; `standard` handles that binding when it
is introduced only in a standard future. -/
structure CheckedContextSelectedEntryAt
    (Psi : EvalCtx) (Gamma : NLCtx) (depth : Nat)
    (x : VName) (tau : Ty) : Prop where
  root : forall {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi (x, b) = some v -> Basis.tof b = tau ->
      CheckedFreshSelectedAt Psi Gamma depth b
  standard : CheckedFreshSelectedAt Psi Gamma depth (Basis.std tau)

/-- Selected-pair evidence for precisely the current linear and nonlinear
source bindings. -/
structure CheckedContextSelectedAt
    (Psi : EvalCtx) (depth : Nat) (Delta : LCtx) (Gamma : NLCtx) : Prop where
  lin : forall {x : VName} {s : Space}, Delta.lookup x = some s ->
    CheckedContextSelectedEntryAt Psi Gamma depth x (.space s)
  nlin : forall {x : VName} {tau : Ty}, Gamma.lookup x = some tau ->
    CheckedContextSelectedEntryAt Psi Gamma depth x tau

/-- Raise one context entry to a larger common cross depth. -/
theorem CheckedContextSelectedEntryAt.monoDepth
    {Psi : EvalCtx} {Gamma : NLCtx} {x : VName} {tau : Ty} {n m : Nat}
    (hnm : n ≤ m) (entry : CheckedContextSelectedEntryAt Psi Gamma n x tau) :
    CheckedContextSelectedEntryAt Psi Gamma m x tau where
  root hlookup htof := (entry.root hlookup htof).monoDepth hnm
  standard := entry.standard.monoDepth hnm

/-- Raise every current-context entry to a larger common cross depth. -/
theorem CheckedContextSelectedAt.monoDepth
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx} {n m : Nat}
    (hnm : n ≤ m) (self : CheckedContextSelectedAt Psi n Delta Gamma) :
    CheckedContextSelectedAt Psi m Delta Gamma where
  lin hlookup := (self.lin hlookup).monoDepth hnm
  nlin hlookup := (self.nlin hlookup).monoDepth hnm

/-- Initialize the selected service from the uniform creation-prefix store
and exact source/evaluator linkage. -/
theorem CheckedContextSelectedAt.of_storeAt
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx} {Gamma : NLCtx}
    (hlink : V2.TypingImplyEval Delta Gamma Psi)
    (store : CheckedPairFreshDepthQuadSelectedStoreAt Psi Gamma depth) :
    CheckedContextSelectedAt Psi depth Delta Gamma where
  lin := by
    intro x s hlookup
    have hx : x ∈ Delta := Finmap.mem_of_lookup_eq_some hlookup
    obtain ⟨b0, hmem0⟩ := (hlink.1 x).mp (Or.inl hx)
    obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp hmem0
    have htof0 : Basis.tof b0 = .space s :=
      hlink.2.1 x s b0 hlookup hmem0
    let p0 : CheckedFreshSelectedAt Psi Gamma depth b0 :=
      ⟨hlink.2.2.2 x b0 hmem0, store.resolve hlookup0⟩
    refine {
      root := ?_
      standard := ?_ }
    · intro b v hlookupB htof
      exact ⟨hlink.2.2.2 x b
          (Finmap.mem_of_lookup_eq_some hlookupB),
        store.resolve hlookupB⟩
    · simpa only [htof0] using p0.toStandard
  nlin := by
    intro x tau hlookup
    have hx : x ∈ Gamma := Finmap.mem_of_lookup_eq_some hlookup
    obtain ⟨b0, hmem0⟩ := (hlink.1 x).mp (Or.inr hx)
    obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp hmem0
    have htof0 : Basis.tof b0 = tau :=
      hlink.2.2.1 x tau b0 hlookup hmem0
    let p0 : CheckedFreshSelectedAt Psi Gamma depth b0 :=
      ⟨hlink.2.2.2 x b0 hmem0, store.resolve hlookup0⟩
    refine {
      root := ?_
      standard := ?_ }
    · intro b v hlookupB htof
      exact ⟨hlink.2.2.2 x b
          (Finmap.mem_of_lookup_eq_some hlookupB),
        store.resolve hlookupB⟩
    · simpa only [htof0] using p0.toStandard

/-- Re-root one entry through a standard-only evaluator future. -/
theorem CheckedContextSelectedEntryAt.rebaseStandard
    {Psi Psi' : EvalCtx} {Gamma : NLCtx} {depth : Nat}
    {x : VName} {tau : Ty}
    (entry : CheckedContextSelectedEntryAt Psi Gamma depth x tau)
    (hfuture : CheckedStdFuture Psi Psi') :
    CheckedContextSelectedEntryAt Psi' Gamma depth x tau where
  root := by
    intro b v hlookup htof
    rcases RawConsistentRank.CheckedStdFuture.lookup_root_or_standard
        hfuture hlookup with hroot | hextra
    · exact (entry.root hroot htof).rebase
        (RawCertifiedConsistentPairStore.CheckedStdFuture.toFresh hfuture)
        (NLCtxIncl.refl Gamma)
    · obtain ⟨_hnotRoot, hstd, _hfresh⟩ := hextra
      rw [hstd, htof]
      exact entry.standard.rebase
        (RawCertifiedConsistentPairStore.CheckedStdFuture.toFresh hfuture)
        (NLCtxIncl.refl Gamma)
  standard := entry.standard.rebase
    (RawCertifiedConsistentPairStore.CheckedStdFuture.toFresh hfuture)
    (NLCtxIncl.refl Gamma)

/-- Re-root the whole current-context service through a standard-only
future. -/
theorem CheckedContextSelectedAt.rebaseStandard
    {Psi Psi' : EvalCtx} {Gamma : NLCtx} {Delta : LCtx} {depth : Nat}
    (self : CheckedContextSelectedAt Psi depth Delta Gamma)
    (hfuture : CheckedStdFuture Psi Psi') :
    CheckedContextSelectedAt Psi' depth Delta Gamma where
  lin hlookup := (self.lin hlookup).rebaseStandard hfuture
  nlin hlookup := (self.nlin hlookup).rebaseStandard hfuture

/-- Restrict the linear half along an exact lookup inclusion. -/
theorem CheckedContextSelectedAt.restrictLinear
    {Psi : EvalCtx} {Gamma : NLCtx} {DeltaSmall DeltaBig : LCtx}
    {depth : Nat}
    (self : CheckedContextSelectedAt Psi depth DeltaBig Gamma)
    (hDelta : LinearCtxIncl DeltaSmall DeltaBig) :
    CheckedContextSelectedAt Psi depth DeltaSmall Gamma where
  lin hlookup := self.lin (hDelta _ _ hlookup)
  nlin hlookup := self.nlin hlookup

/-- Rebuild one entry after nonlinear-context growth while leaving its
evaluator root unchanged. -/
theorem CheckedContextSelectedEntryAt.rebaseContext
    {Psi : EvalCtx} {Gamma Gamma' : NLCtx} {depth : Nat}
    {x : VName} {tau : Ty}
    (entry : CheckedContextSelectedEntryAt Psi Gamma depth x tau)
    (hGamma : NLCtxIncl Gamma Gamma') :
    CheckedContextSelectedEntryAt Psi Gamma' depth x tau where
  root hlookup htof :=
    (entry.root hlookup htof).rebase (CheckedFreshFuture.refl Psi) hGamma
  standard := entry.standard.rebase (CheckedFreshFuture.refl Psi) hGamma

theorem CheckedContextSelectedEntryAt.rebaseFresh
    {Psi Psi' : EvalCtx} {Gamma Gamma' : NLCtx} {depth : Nat}
    {x : VName} {tau : Ty}
    (entry : CheckedContextSelectedEntryAt Psi Gamma depth x tau)
    (hfuture : CheckedFreshFuture Psi Psi')
    (hGamma : NLCtxIncl Gamma Gamma')
    (hx : x ∈ Psi.names) :
    CheckedContextSelectedEntryAt Psi' Gamma' depth x tau where
  root := by
    intro b v hlookup htof
    have hlookup0 := hfuture.lookup_root_of_root_name hx hlookup
    exact (entry.root hlookup0 htof).rebase hfuture hGamma
  standard := entry.standard.rebase hfuture hGamma

private theorem not_mem_names_of_context_absent
    {Psi : EvalCtx} {y : VName} (hy : y ∉ Psi.names)
    {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi (y, b) = some v) : False :=
  hy (EvalCtx.mem_names_of_lookup hlookup)

/-- Add a fresh linear source binder which is visible only in standard
futures of the unchanged evaluator root. -/
theorem CheckedContextSelectedAt.insertLinearFuture
    {Psi : EvalCtx} {Gamma : NLCtx} {Delta : LCtx} {depth : Nat}
    (self : CheckedContextSelectedAt Psi depth Delta Gamma)
    {y : VName} {s : Space}
    (hyPsi : y ∉ Psi.names) (hyDelta : y ∉ Delta)
    (domain : CheckedFreshSelectedAt Psi Gamma depth (Basis.stdSpace s)) :
    CheckedContextSelectedAt Psi depth (Finmap.insert y s Delta) Gamma where
  lin := by
    intro x sx hlookup
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      refine {
        root := ?_
        standard := ?_ }
      · intro b v hlookupRoot htof
        exact False.elim
          (not_mem_names_of_context_absent hyPsi hlookupRoot)
      · simpa only [Basis.std] using domain
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact self.lin hlookup
  nlin hlookup := self.nlin hlookup

/-- Add a fresh nonlinear source binder which is visible only in standard
futures. -/
theorem CheckedContextSelectedAt.insertNonlinearFuture
    {Psi : EvalCtx} {Gamma : NLCtx} {Delta : LCtx} {depth : Nat}
    (self : CheckedContextSelectedAt Psi depth Delta Gamma)
    {y : VName} {tau : Ty}
    (hyPsi : y ∉ Psi.names) (hyGamma : y ∉ Gamma)
    (domain : CheckedFreshSelectedAt Psi Gamma depth (Basis.std tau)) :
    CheckedContextSelectedAt Psi depth Delta
      (Finmap.insert y tau Gamma) := by
  let hbase : NLCtxIncl Gamma (Finmap.insert y tau Gamma) :=
    (NLCtxIncl.refl Gamma).insert_right hyGamma tau
  refine {
    lin := ?_
    nlin := ?_ }
  · intro x s hlookup
    exact (self.lin hlookup).rebaseContext hbase
  · intro x tauX hlookup
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      refine {
        root := ?_
        standard := ?_ }
      · intro b v hlookupRoot htof
        exact False.elim
          (not_mem_names_of_context_absent hyPsi hlookupRoot)
      · exact domain.rebase (CheckedFreshFuture.refl Psi) hbase
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact (self.nlin hlookup).rebaseContext hbase

/-- Simultaneously install a possibly nonstandard dependent-frame endpoint
in the evaluator root and nonlinear source context.  This operation retains
the literal selected basis, so a body occurrence of the bound variable gets
`bArg -> std (tof bArg)`, not merely a standard self-pair. -/
theorem CheckedContextSelectedAt.extendFrameNonlinear
    {Psi : EvalCtx} {Gamma : NLCtx} {Delta : LCtx} {depth : Nat}
    (self : CheckedContextSelectedAt Psi depth Delta Gamma)
    {y : VName} {tau : Ty} {bArg : Basis} {v : ValExpr}
    (hyPsi : y ∉ Psi.names) (hyDelta : y ∉ Delta) (hyGamma : y ∉ Gamma)
    (htof : Basis.tof bArg = tau)
    (domain : CheckedFreshSelectedAt Psi Gamma depth bArg) :
    CheckedContextSelectedAt (Psi.extend y bArg v) depth Delta
      (Finmap.insert y tau Gamma) := by
  let PsiX := Psi.extend y bArg v
  let GammaX := Finmap.insert y tau Gamma
  let hfuture : CheckedFreshFuture Psi PsiX :=
    (CheckedFreshFuture.refl Psi).extend hyPsi bArg v
  let hbase : NLCtxIncl Gamma GammaX :=
    (NLCtxIncl.refl Gamma).insert_right hyGamma tau
  refine {
    lin := ?_
    nlin := ?_ }
  · intro x s hlookup
    have hxy : x ≠ y := by
      intro heq
      subst x
      exact hyDelta (Finmap.mem_of_lookup_eq_some hlookup)
    have entry := self.lin hlookup
    refine {
      root := ?_
      standard := entry.standard.rebase hfuture hbase }
    intro b vX hlookupX htofX
    have hkey : (x, b) ≠ (y, bArg) := by
      intro heq
      exact hxy (Prod.mk.inj heq).1
    have hlookup0 : EvalCtx.lookup Psi (x, b) = some vX := by
      simpa only [PsiX, EvalCtx.lookup, EvalCtx.extend,
        Finmap.lookup_insert_of_ne _ hkey] using hlookupX
    exact (entry.root hlookup0 htofX).rebase hfuture hbase
  · intro x tauX hlookup
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      refine {
        root := ?_
        standard := ?_ }
      · intro b vX hlookupX htofX
        by_cases hbb : b = bArg
        · subst b
          exact domain.rebase hfuture hbase
        · have hkey : (y, b) ≠ (y, bArg) := by
            intro heq
            exact hbb (Prod.mk.inj heq).2
          have hlookup0 : EvalCtx.lookup Psi (y, b) = some vX := by
            simpa only [PsiX, EvalCtx.lookup, EvalCtx.extend,
              Finmap.lookup_insert_of_ne _ hkey] using hlookupX
          exact False.elim
            (not_mem_names_of_context_absent hyPsi hlookup0)
      · simpa only [htof] using domain.toStandard.rebase hfuture hbase
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      have entry := self.nlin hlookup
      refine {
        root := ?_
        standard := entry.standard.rebase hfuture hbase }
      intro b vX hlookupX htofX
      have hkey : (x, b) ≠ (y, bArg) := by
        intro heq
        exact hxy (Prod.mk.inj heq).1
      have hlookup0 : EvalCtx.lookup Psi (x, b) = some vX := by
        simpa only [PsiX, EvalCtx.lookup, EvalCtx.extend,
          Finmap.lookup_insert_of_ne _ hkey] using hlookupX
      exact (entry.root hlookup0 htofX).rebase hfuture hbase

/-! ## Controlled-source / target-context form

Fresh pair packages are rebuilt in arbitrary well-formed target contexts,
but source syntax must continue to traverse the original controlled typing
context.  The following form deliberately indexes those two roles
separately: it contains entries only for `DeltaCtrl,GammaCtrl`, while every
pair is already formed in `GammaTarget`. -/

structure CheckedControlledContextSelectedAt
    (Psi : EvalCtx) (depth : Nat) (DeltaCtrl : LCtx)
    (GammaCtrl GammaTarget : NLCtx) : Prop where
  lin : forall {x : VName} {s : Space},
    DeltaCtrl.lookup x = some s ->
      CheckedContextSelectedEntryAt Psi GammaTarget depth x (.space s)
  nlin : forall {x : VName} {tau : Ty},
    GammaCtrl.lookup x = some tau ->
      CheckedContextSelectedEntryAt Psi GammaTarget depth x tau

/-- Separate the controlled and target contexts by rebuilding only the
packages attached to controlled entries.  No entry is asserted for an
unrelated key newly present in `GammaTarget`. -/
theorem CheckedContextSelectedAt.toControlledTarget
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx}
    {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedContextSelectedAt Psi depth Delta GammaCtrl)
    (hGamma : NLCtxIncl GammaCtrl GammaTarget) :
    CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget where
  lin hlookup := (self.lin hlookup).rebaseContext hGamma
  nlin hlookup := (self.nlin hlookup).rebaseContext hGamma

/-- Initialize the controlled/target service directly from a creation-prefix
store and a chosen well-formed target-context inclusion. -/
theorem CheckedControlledContextSelectedAt.of_storeAt
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx}
    {GammaCtrl GammaTarget : NLCtx}
    (hlink : V2.TypingImplyEval Delta GammaCtrl Psi)
    (store : CheckedPairFreshDepthQuadSelectedStoreAt Psi GammaCtrl depth)
    (hGamma : NLCtxIncl GammaCtrl GammaTarget) :
    CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget :=
  (CheckedContextSelectedAt.of_storeAt hlink store).toControlledTarget hGamma

/-- Initialize directly at an arbitrary fresh evaluator and nonlinear target
extension of a creation prefix. -/
theorem CheckedControlledContextSelectedAt.of_storeAtFresh
    {Psi0 Psi : EvalCtx} {depth : Nat} {Delta : LCtx}
    {Gamma0 Gamma : NLCtx}
    (hlink : V2.TypingImplyEval Delta Gamma0 Psi0)
    (store : CheckedPairFreshDepthQuadSelectedStoreAt Psi0 Gamma0 depth)
    (hfuture : CheckedFreshFuture Psi0 Psi)
    (hGamma : NLCtxIncl Gamma0 Gamma) :
    CheckedControlledContextSelectedAt Psi depth Delta Gamma0 Gamma := by
  let root := CheckedContextSelectedAt.of_storeAt hlink store
  refine {
    lin := ?_
    nlin := ?_ }
  · intro x s hlookup
    have hxDelta : x ∈ Delta := Finmap.mem_of_lookup_eq_some hlookup
    have hxRoot : x ∈ Psi0.names := by
      obtain ⟨b, hmem⟩ := (hlink.1 x).mp (Or.inl hxDelta)
      exact EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hmem⟩
    exact (root.lin hlookup).rebaseFresh hfuture hGamma hxRoot
  · intro x tau hlookup
    have hxGamma : x ∈ Gamma0 := Finmap.mem_of_lookup_eq_some hlookup
    have hxRoot : x ∈ Psi0.names := by
      obtain ⟨b, hmem⟩ := (hlink.1 x).mp (Or.inr hxGamma)
      exact EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hmem⟩
    exact (root.nlin hlookup).rebaseFresh hfuture hGamma hxRoot

/-- Move only the target context.  The controlled source domain, and hence
the set of variable leaves the traversal may consume, is unchanged. -/
theorem CheckedControlledContextSelectedAt.rebaseTarget
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx}
    {GammaCtrl GammaTarget GammaTarget' : NLCtx}
    (self : CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget)
    (hGamma : NLCtxIncl GammaTarget GammaTarget') :
    CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget' where
  lin hlookup := (self.lin hlookup).rebaseContext hGamma
  nlin hlookup := (self.nlin hlookup).rebaseContext hGamma

/-- Re-root controlled entries through standard-only evaluator growth. -/
theorem CheckedControlledContextSelectedAt.rebaseStandard
    {Psi Psi' : EvalCtx} {depth : Nat} {Delta : LCtx}
    {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget)
    (hfuture : CheckedStdFuture Psi Psi') :
    CheckedControlledContextSelectedAt Psi' depth Delta
      GammaCtrl GammaTarget where
  lin hlookup := (self.lin hlookup).rebaseStandard hfuture
  nlin hlookup := (self.nlin hlookup).rebaseStandard hfuture

/-- Restrict only the controlled linear source domain. -/
theorem CheckedControlledContextSelectedAt.restrictLinear
    {Psi : EvalCtx} {depth : Nat} {DeltaSmall DeltaBig : LCtx}
    {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedControlledContextSelectedAt Psi depth DeltaBig
      GammaCtrl GammaTarget)
    (hDelta : LinearCtxIncl DeltaSmall DeltaBig) :
    CheckedControlledContextSelectedAt Psi depth DeltaSmall
      GammaCtrl GammaTarget where
  lin hlookup := self.lin (hDelta _ _ hlookup)
  nlin hlookup := self.nlin hlookup

/-- Numeric depth raising for the controlled/target service. -/
theorem CheckedControlledContextSelectedAt.monoDepth
    {Psi : EvalCtx} {Delta : LCtx} {GammaCtrl GammaTarget : NLCtx}
    {n m : Nat} (hnm : n ≤ m)
    (self : CheckedControlledContextSelectedAt Psi n Delta
      GammaCtrl GammaTarget) :
    CheckedControlledContextSelectedAt Psi m Delta
      GammaCtrl GammaTarget where
  lin hlookup := (self.lin hlookup).monoDepth hnm
  nlin hlookup := (self.nlin hlookup).monoDepth hnm

/-- Add a fresh controlled linear binder.  The target nonlinear context does
not change; the supplied domain package is already formed there. -/
theorem CheckedControlledContextSelectedAt.insertLinearFuture
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx}
    {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget)
    {y : VName} {s : Space}
    (hyPsi : y ∉ Psi.names) (_hyDelta : y ∉ Delta)
    (domain : CheckedFreshSelectedAt Psi GammaTarget depth
      (Basis.stdSpace s)) :
    CheckedControlledContextSelectedAt Psi depth
      (Finmap.insert y s Delta) GammaCtrl GammaTarget where
  lin := by
    intro x sx hlookup
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      refine {
        root := ?_
        standard := ?_ }
      · intro b v hlookupRoot htof
        exact False.elim
          (not_mem_names_of_context_absent hyPsi hlookupRoot)
      · simpa only [Basis.std] using domain
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact self.lin hlookup
  nlin hlookup := self.nlin hlookup

/-- Add a fresh nonlinear source binder to the controlled and target
contexts in lockstep.  The service remains silent about any unrelated target
bindings. -/
theorem CheckedControlledContextSelectedAt.insertNonlinearFuture
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx}
    {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget)
    {y : VName} {tau : Ty}
    (hyPsi : y ∉ Psi.names) (hyCtrl : y ∉ GammaCtrl)
    (hyTarget : y ∉ GammaTarget)
    (domain : CheckedFreshSelectedAt Psi GammaTarget depth
      (Basis.std tau)) :
    CheckedControlledContextSelectedAt Psi depth Delta
      (Finmap.insert y tau GammaCtrl)
      (Finmap.insert y tau GammaTarget) := by
  let hTarget : NLCtxIncl GammaTarget (Finmap.insert y tau GammaTarget) :=
    (NLCtxIncl.refl GammaTarget).insert_right hyTarget tau
  refine {
    lin := ?_
    nlin := ?_ }
  · intro x s hlookup
    exact (self.lin hlookup).rebaseContext hTarget
  · intro x tauX hlookup
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      refine {
        root := ?_
        standard := ?_ }
      · intro b v hlookupRoot htof
        exact False.elim
          (not_mem_names_of_context_absent hyPsi hlookupRoot)
      · exact domain.rebase (CheckedFreshFuture.refl Psi) hTarget
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact (self.nlin hlookup).rebaseContext hTarget

/-- Install a dependent-frame endpoint in the evaluator and extend the
controlled and target nonlinear contexts in lockstep.  The new controlled
entry keeps the literal endpoint basis as its selected orientation. -/
theorem CheckedControlledContextSelectedAt.extendFrameNonlinear
    {Psi : EvalCtx} {depth : Nat} {Delta : LCtx}
    {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget)
    {y : VName} {tau : Ty} {bArg : Basis} {v : ValExpr}
    (hyPsi : y ∉ Psi.names) (hyDelta : y ∉ Delta)
    (hyCtrl : y ∉ GammaCtrl) (hyTarget : y ∉ GammaTarget)
    (htof : Basis.tof bArg = tau)
    (domain : CheckedFreshSelectedAt Psi GammaTarget depth bArg) :
    CheckedControlledContextSelectedAt (Psi.extend y bArg v) depth Delta
      (Finmap.insert y tau GammaCtrl)
      (Finmap.insert y tau GammaTarget) := by
  let PsiX := Psi.extend y bArg v
  let GammaTargetX := Finmap.insert y tau GammaTarget
  let hfuture : CheckedFreshFuture Psi PsiX :=
    (CheckedFreshFuture.refl Psi).extend hyPsi bArg v
  let hTarget : NLCtxIncl GammaTarget GammaTargetX :=
    (NLCtxIncl.refl GammaTarget).insert_right hyTarget tau
  refine {
    lin := ?_
    nlin := ?_ }
  · intro x s hlookup
    have hxy : x ≠ y := by
      intro heq
      subst x
      exact hyDelta (Finmap.mem_of_lookup_eq_some hlookup)
    have entry := self.lin hlookup
    refine {
      root := ?_
      standard := entry.standard.rebase hfuture hTarget }
    intro b vX hlookupX htofX
    have hkey : (x, b) ≠ (y, bArg) := by
      intro heq
      exact hxy (Prod.mk.inj heq).1
    have hlookup0 : EvalCtx.lookup Psi (x, b) = some vX := by
      simpa only [PsiX, EvalCtx.lookup, EvalCtx.extend,
        Finmap.lookup_insert_of_ne _ hkey] using hlookupX
    exact (entry.root hlookup0 htofX).rebase hfuture hTarget
  · intro x tauX hlookup
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      refine {
        root := ?_
        standard := ?_ }
      · intro b vX hlookupX htofX
        by_cases hbb : b = bArg
        · subst b
          exact domain.rebase hfuture hTarget
        · have hkey : (y, b) ≠ (y, bArg) := by
            intro heq
            exact hbb (Prod.mk.inj heq).2
          have hlookup0 : EvalCtx.lookup Psi (y, b) = some vX := by
            simpa only [PsiX, EvalCtx.lookup, EvalCtx.extend,
              Finmap.lookup_insert_of_ne _ hkey] using hlookupX
          exact False.elim
            (not_mem_names_of_context_absent hyPsi hlookup0)
      · simpa only [htof] using
          domain.toStandard.rebase hfuture hTarget
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      have entry := self.nlin hlookup
      refine {
        root := ?_
        standard := entry.standard.rebase hfuture hTarget }
      intro b vX hlookupX htofX
      have hkey : (x, b) ≠ (y, bArg) := by
        intro heq
        exact hxy (Prod.mk.inj heq).1
      have hlookup0 : EvalCtx.lookup Psi (x, b) = some vX := by
        simpa only [PsiX, EvalCtx.lookup, EvalCtx.extend,
          Finmap.lookup_insert_of_ne _ hkey] using hlookupX
      exact (entry.root hlookup0 htofX).rebase hfuture hTarget

end RawCertifiedPairContextSelected
end GLang
