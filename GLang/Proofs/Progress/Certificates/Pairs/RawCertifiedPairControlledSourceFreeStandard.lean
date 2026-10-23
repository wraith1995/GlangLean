import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairControlledSourceBuilder
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairHybridFuture
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedContextMono
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardCertificate
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardStore

/-!
# Controlled source traversal with free standard binder keys

The original fixed-depth pair certificate asks every variable lookup for a
recursive selected-to-standard pair.  That is appropriate for evaluator
history keys and literal dependent-frame endpoints, but too strong for an
ordinary source binder: its key is definitionally standard, and its hidden
dependent type need not fit any syntax-height bound of the enclosing term.

This module is an internal, parallel construction surface.  It leaves the
pair-only certificate untouched.  Its selected policy accepts either the
literal standard equality or the original recursive pair.  Equality is not
inferred merely because an arbitrary root key happens to look standard;
entries carry persistent provenance distinguishing pair-backed evaluator
keys from ordinary standard-binder slots.
-/

namespace GLang
namespace RawCertifiedPairControlledSourceFreeStandard

open OperationalStrengthening
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate
open RawCertifiedConsistentPairStore
open RawCertifiedPairStoreUniformization
open RawCertifiedPairContextStandardSelf
open RawCertifiedPairContextSelected
open RawCertifiedPairHybridFuture
open RawCertifiedPairControlledSourceBuilder
open RawCertifiedPairFreeStandardCertificate
open RawCertifiedPairFreeStandardStore

/-- The relaxed internal selected-basis policy. -/
abbrev CheckedPairOrStandardSelectedAt := CheckedFreeStdSelectedAt

/-- A free-standard quad stable under hybrid evaluator growth and
well-formed nonlinear-context growth. -/
structure CheckedFreeStdHybridSelectedAt
    (Psi : EvalCtx) (Gamma reserved : NLCtx)
    (depth : Nat) (b : Basis) : Prop where
  valid : Basis.BasisValid Gamma b
  quad : forall {Psi' : EvalCtx} {Gamma' : NLCtx},
    CheckedHybridFuture Psi Psi' reserved ->
    NLCtxIncl Gamma Gamma' ->
    V2.CtxWF' (∅ : LCtx) Gamma' ->
      CheckedFreeStdPairDepthQuad Psi' depth Gamma' b

/-- Re-root one free-standard package through an admissible hybrid future. -/
theorem CheckedFreeStdHybridSelectedAt.rebase
    {Psi Psi' : EvalCtx} {Gamma Gamma' reserved : NLCtx}
    {depth : Nat} {b : Basis}
    (p : CheckedFreeStdHybridSelectedAt Psi Gamma reserved depth b)
    (hfuture : CheckedHybridFuture Psi Psi' reserved)
    (hGamma : NLCtxIncl Gamma Gamma') :
    CheckedFreeStdHybridSelectedAt Psi' Gamma' reserved depth b where
  valid := raw_basisValid_mono p.valid hGamma
  quad hfuture' hGamma' hwf :=
    p.quad (hfuture.trans hfuture') (hGamma.trans hGamma') hwf

/-- Raise a free-standard package to a larger common depth. -/
theorem CheckedFreeStdHybridSelectedAt.monoDepth
    {Psi : EvalCtx} {Gamma reserved : NLCtx} {depth depth' : Nat}
    {b : Basis} (hle : depth <= depth')
    (p : CheckedFreeStdHybridSelectedAt Psi Gamma reserved depth b) :
    CheckedFreeStdHybridSelectedAt Psi Gamma reserved depth' b where
  valid := p.valid
  quad hfuture hGamma hwf := (p.quad hfuture hGamma hwf).monoDepth hle

/-- Strengthen the set of standard-only source slots. -/
theorem CheckedFreeStdHybridSelectedAt.strengthenReserved
    {Psi : EvalCtx} {Gamma reserved reserved' : NLCtx}
    {depth : Nat} {b : Basis}
    (hReserved : NLCtxIncl reserved reserved')
    (p : CheckedFreeStdHybridSelectedAt Psi Gamma reserved depth b) :
    CheckedFreeStdHybridSelectedAt Psi Gamma reserved' depth b where
  valid := p.valid
  quad hfuture hGamma hwf :=
    p.quad (hfuture.of_reserved_incl hReserved) hGamma hwf

/-- Standard-future source-side aliases consumed by the free-standard pair
certificate.  The controlled service is hybrid-stable so these leaves can
embed `CheckedStdFuture` through `CheckedHybridFuture.ofStandard`. -/
abbrev CheckedPairOrStandardLocalSideS
    (Psi : EvalCtx) (depth : Nat)
    {Gamma : NLCtx} {s : Space} (h : SValid Gamma s) : Type :=
  CheckedLocalSideSWith (CheckedPairOrStandardSelectedAt Psi depth) Psi h

abbrev CheckedPairOrStandardLocalSideT
    (Psi : EvalCtx) (depth : Nat)
    {Gamma : NLCtx} {tau : Ty} {k : Kind} (h : TValid Gamma tau k) : Type :=
  CheckedLocalSideTWith (CheckedPairOrStandardSelectedAt Psi depth) Psi h

abbrev CheckedPairOrStandardLocalSideSub
    (Psi : EvalCtx) (depth : Nat)
    {Gamma : NLCtx} {s0 s1 : Space} (h : SubType Gamma s0 s1) : Type :=
  CheckedLocalSideSubWith (CheckedPairOrStandardSelectedAt Psi depth) Psi h

abbrev CheckedPairOrStandardLocalSideBases
    (Psi : EvalCtx) (depth : Nat)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) : Type :=
  CheckedLocalSideBasesWith (CheckedPairOrStandardSelectedAt Psi depth) Psi h

/-- Persistent provenance of one controlled variable.

`paired` is used only for an actual evaluator/history key or a literal frame
endpoint and therefore keeps a recursive pair package.  `standard` is used
only for an ordinary source-binder slot.  Its equality remains available if
that standard key is materialized and later inherited into a re-rooted frame
body. -/
inductive CheckedRelaxedEntryProvenance
    (Psi : EvalCtx) (GammaTarget reserved : NLCtx) (depth : Nat)
    (x : VName) (tau : Ty) : Prop
  | paired
      (owned : x ∈ Psi.names)
      (selected : exists b : Basis, exists v : ValExpr,
        EvalCtx.lookup Psi (x, b) = some v /\ Basis.tof b = tau /\
          CheckedFreeStdHybridSelectedAt Psi GammaTarget reserved depth b)
      (lookupValid : forall {b : Basis} {v : ValExpr},
        EvalCtx.lookup Psi (x, b) = some v -> Basis.tof b = tau ->
          Basis.BasisValid GammaTarget b) :
      CheckedRelaxedEntryProvenance Psi GammaTarget reserved depth x tau
  | standard
      (reservedLookup : reserved.lookup x = some tau)
      (standardValid : Basis.BasisValid GammaTarget (Basis.std tau))
      (rootStandard : forall {b : Basis} {v : ValExpr},
        EvalCtx.lookup Psi (x, b) = some v -> Basis.tof b = tau ->
          b = Basis.std tau) :
      CheckedRelaxedEntryProvenance Psi GammaTarget reserved depth x tau

/-- One controlled source binding with persistent pair-vs-standard
provenance. -/
structure CheckedRelaxedContextSelectedEntryAt
    (Psi : EvalCtx) (GammaTarget reserved : NLCtx) (depth : Nat)
    (x : VName) (tau : Ty) : Prop where
  provenance : CheckedRelaxedEntryProvenance Psi GammaTarget reserved
    depth x tau

/-- Controlled linear/nonlinear entries, with pairs formed in the separate
target context. -/
structure CheckedRelaxedControlledContextSelectedAt
    (Psi : EvalCtx) (reserved : NLCtx) (depth : Nat)
    (DeltaCtrl : LCtx) (GammaCtrl GammaTarget : NLCtx) : Prop where
  lin : forall {x : VName} {s : Space},
    DeltaCtrl.lookup x = some s ->
      CheckedRelaxedContextSelectedEntryAt Psi GammaTarget reserved depth
        x (.space s)
  nlin : forall {x : VName} {tau : Ty},
    GammaCtrl.lookup x = some tau ->
      CheckedRelaxedContextSelectedEntryAt Psi GammaTarget reserved depth
        x tau

/-- Choose the persistent primary representation of a paired source entry.
For an ordinary standard-provenance binder, use the representation supplied
by coverage and discharge it by literal standard equality.  Thus a later
representation of an already-owned source name never changes the recursive
certificate selected by a variable leaf. -/
theorem CheckedRelaxedContextSelectedEntryAt.resolveSelected
    {Psi Psi' : EvalCtx} {GammaTarget reserved : NLCtx} {depth : Nat}
    {x : VName} {tau : Ty}
    (entry : CheckedRelaxedContextSelectedEntryAt Psi GammaTarget reserved
      depth x tau)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hfuture : CheckedHybridFuture Psi Psi' reserved)
    (available : exists b : Basis, exists v : ValExpr,
      EvalCtx.lookup Psi' (x, b) = some v /\ Basis.tof b = tau) :
    exists b : Basis, exists v : ValExpr,
      EvalCtx.lookup Psi' (x, b) = some v /\ Basis.tof b = tau /\
      exists hb : Basis.BasisValid GammaTarget b,
        CheckedPairOrStandardSelectedAt Psi depth hb := by
  cases entry.provenance with
  | paired hxRoot selected lookupValid =>
      obtain ⟨b, v, hlookup, htof, p⟩ := selected
      refine ⟨b, v, hfuture.fresh.subctx (x, b) v hlookup, htof,
        p.valid, Or.inr ?_⟩
      exact (p.quad (CheckedHybridFuture.refl Psi reserved)
        (NLCtxIncl.refl GammaTarget) hwf).toStd
  | standard hreserved hvalid hrootStd =>
      obtain ⟨b, v, hlookup, htof⟩ := available
      have hstd : b = Basis.std tau := by
        by_cases hxRoot : x ∈ Psi.names
        · exact hrootStd
            (hfuture.fresh.lookup_root_of_root_name hxRoot hlookup) htof
        · exact hfuture.reserved_standard hreserved hxRoot hlookup htof
      subst b
      refine ⟨Basis.std tau, v, hlookup, by simpa only [Basis.tof_std] using htof,
        hvalid, ?_⟩
      exact Or.inl (by simp only [Basis.tof_std])

/-- Every matching lookup remains valid, independently of which one is the
primary recursive representation.  This is the separate shallow-side fact
needed by conversion and is deliberately weaker than certifying every
representation. -/
theorem CheckedRelaxedContextSelectedEntryAt.lookupValid
    {Psi Psi' : EvalCtx} {GammaTarget reserved : NLCtx} {depth : Nat}
    {x : VName} {tau : Ty}
    (entry : CheckedRelaxedContextSelectedEntryAt Psi GammaTarget reserved
      depth x tau)
    (hfuture : CheckedHybridFuture Psi Psi' reserved)
    {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi' (x, b) = some v)
    (htof : Basis.tof b = tau) :
    Basis.BasisValid GammaTarget b := by
  cases entry.provenance with
  | paired hxRoot _selected lookupValid =>
      exact lookupValid
        (hfuture.fresh.lookup_root_of_root_name hxRoot hlookup) htof
  | standard hreserved hvalid hrootStd =>
      have hstd : b = Basis.std tau := by
        by_cases hxRoot : x ∈ Psi.names
        · exact hrootStd
            (hfuture.fresh.lookup_root_of_root_name hxRoot hlookup) htof
        · exact hfuture.reserved_standard hreserved hxRoot hlookup htof
      subst b
      exact hvalid

/-! ## Provenance-preserving transport -/

/-- Raise a relaxed entry to a common larger pair depth. -/
theorem CheckedRelaxedContextSelectedEntryAt.monoDepth
    {Psi : EvalCtx} {GammaTarget reserved : NLCtx}
    {depth depth' : Nat} {x : VName} {tau : Ty}
    (hle : depth <= depth')
    (entry : CheckedRelaxedContextSelectedEntryAt Psi GammaTarget reserved
      depth x tau) :
    CheckedRelaxedContextSelectedEntryAt Psi GammaTarget reserved
      depth' x tau := by
  cases entry.provenance with
  | paired howned selected lookupValid =>
      obtain ⟨b, v, hlookup, htof, package⟩ := selected
      exact ⟨.paired howned
        ⟨b, v, hlookup, htof, package.monoDepth hle⟩ lookupValid⟩
  | standard hreserved hvalid hroot =>
      exact ⟨.standard hreserved hvalid hroot⟩

/-- Move the target nonlinear context without changing evaluator or
provenance. -/
theorem CheckedRelaxedContextSelectedEntryAt.rebaseContext
    {Psi : EvalCtx} {GammaTarget GammaTarget' reserved : NLCtx}
    {depth : Nat} {x : VName} {tau : Ty}
    (entry : CheckedRelaxedContextSelectedEntryAt Psi GammaTarget reserved
      depth x tau)
    (hGamma : NLCtxIncl GammaTarget GammaTarget') :
    CheckedRelaxedContextSelectedEntryAt Psi GammaTarget' reserved
      depth x tau := by
  cases entry.provenance with
  | paired howned selected lookupValid =>
      obtain ⟨b, v, hlookup, htof, package⟩ := selected
      exact ⟨.paired howned
        ⟨b, v, hlookup, htof, package.rebase
          (CheckedHybridFuture.refl Psi reserved) hGamma⟩
        (fun hlookup htof => raw_basisValid_mono
          (lookupValid hlookup htof) hGamma)⟩
  | standard hreserved hvalid hroot =>
      exact ⟨.standard hreserved (raw_basisValid_mono hvalid hGamma) hroot⟩

/-- Add standard-only reservations.  Pair-backed entries restrict their
future quantifier; standard entries retain their explicit provenance. -/
theorem CheckedRelaxedContextSelectedEntryAt.strengthenReserved
    {Psi : EvalCtx} {GammaTarget reserved reserved' : NLCtx}
    {depth : Nat} {x : VName} {tau : Ty}
    (hReserved : NLCtxIncl reserved reserved')
    (entry : CheckedRelaxedContextSelectedEntryAt Psi GammaTarget reserved
      depth x tau) :
    CheckedRelaxedContextSelectedEntryAt Psi GammaTarget reserved'
      depth x tau := by
  cases entry.provenance with
  | paired howned selected lookupValid =>
      obtain ⟨b, v, hlookup, htof, package⟩ := selected
      exact ⟨.paired howned
        ⟨b, v, hlookup, htof, package.strengthenReserved hReserved⟩
        lookupValid⟩
  | standard hreserved hvalid hroot =>
      exact ⟨.standard (hReserved _ _ hreserved) hvalid hroot⟩

/-- Re-root an entry through hybrid growth.  The provenance tag is
persistent: a standard binder which has become physically present in the
new root stays in the `standard` arm. -/
theorem CheckedRelaxedContextSelectedEntryAt.rebase
    {Psi Psi' : EvalCtx} {GammaTarget GammaTarget' reserved : NLCtx}
    {depth : Nat} {x : VName} {tau : Ty}
    (entry : CheckedRelaxedContextSelectedEntryAt Psi GammaTarget reserved
      depth x tau)
    (hfuture : CheckedHybridFuture Psi Psi' reserved)
    (hGamma : NLCtxIncl GammaTarget GammaTarget') :
    CheckedRelaxedContextSelectedEntryAt Psi' GammaTarget' reserved
      depth x tau := by
  cases entry.provenance with
  | paired howned selected lookupValid =>
      have howned' : x ∈ Psi'.names :=
        EvalCtx.Subctx.names_subset hfuture.fresh.subctx howned
      obtain ⟨b, v, hlookup, htof, package⟩ := selected
      refine ⟨.paired howned'
        ⟨b, v, hfuture.fresh.subctx (x, b) v hlookup, htof,
          package.rebase hfuture hGamma⟩ ?_⟩
      intro b v hlookup htof
      exact raw_basisValid_mono
        (lookupValid
          (hfuture.fresh.lookup_root_of_root_name howned hlookup) htof)
        hGamma
  | standard hreserved hvalid hroot =>
      refine ⟨.standard hreserved (raw_basisValid_mono hvalid hGamma) ?_⟩
      intro b v hlookup htof
      by_cases hxRoot : x ∈ Psi.names
      · exact hroot
          (hfuture.fresh.lookup_root_of_root_name hxRoot hlookup) htof
      · exact hfuture.reserved_standard hreserved hxRoot hlookup htof

/-- Raise every entry of the relaxed controlled service. -/
theorem CheckedRelaxedControlledContextSelectedAt.monoDepth
    {Psi : EvalCtx} {reserved : NLCtx} {depth depth' : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (hle : depth <= depth')
    (self : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget) :
    CheckedRelaxedControlledContextSelectedAt Psi reserved depth'
      DeltaCtrl GammaCtrl GammaTarget where
  lin hlookup := (self.lin hlookup).monoDepth hle
  nlin hlookup := (self.nlin hlookup).monoDepth hle

/-- Restrict only the controlled linear context. -/
theorem CheckedRelaxedControlledContextSelectedAt.restrictLinear
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaSmall DeltaBig : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      DeltaBig GammaCtrl GammaTarget)
    (hDelta : LinearCtxIncl DeltaSmall DeltaBig) :
    CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      DeltaSmall GammaCtrl GammaTarget where
  lin hlookup := self.lin (hDelta _ _ hlookup)
  nlin hlookup := self.nlin hlookup

/-- Move only the target nonlinear context. -/
theorem CheckedRelaxedControlledContextSelectedAt.rebaseTarget
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget GammaTarget' : NLCtx}
    (self : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget)
    (hGamma : NLCtxIncl GammaTarget GammaTarget') :
    CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget' where
  lin hlookup := (self.lin hlookup).rebaseContext hGamma
  nlin hlookup := (self.nlin hlookup).rebaseContext hGamma

/-- Re-root all controlled entries through one hybrid future. -/
theorem CheckedRelaxedControlledContextSelectedAt.rebase
    {Psi Psi' : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget GammaTarget' : NLCtx}
    (self : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget)
    (hfuture : CheckedHybridFuture Psi Psi' reserved)
    (hGamma : NLCtxIncl GammaTarget GammaTarget') :
    CheckedRelaxedControlledContextSelectedAt Psi' reserved depth
      DeltaCtrl GammaCtrl GammaTarget' where
  lin hlookup := (self.lin hlookup).rebase hfuture hGamma
  nlin hlookup := (self.nlin hlookup).rebase hfuture hGamma

/-- Initialize all creation-prefix bindings as genuinely pair-backed. -/
theorem CheckedRelaxedControlledContextSelectedAt.of_storeAtFresh
    {Psi0 Psi : EvalCtx} {depth : Nat} {DeltaCtrl : LCtx}
    {GammaCtrl GammaTarget : NLCtx}
    (hlink : V2.TypingImplyEval DeltaCtrl GammaCtrl Psi0)
    (store : CheckedFreeStdFreshDepthQuadSelectedStoreAt
      Psi0 GammaCtrl depth)
    (hfuture : CheckedFreshFuture Psi0 Psi)
    (hGamma : NLCtxIncl GammaCtrl GammaTarget) :
    CheckedRelaxedControlledContextSelectedAt Psi (∅ : NLCtx) depth
      DeltaCtrl GammaCtrl GammaTarget := by
  refine {
    lin := ?_
    nlin := ?_ }
  · intro x s hlookup
    have hxCtrl : x ∈ DeltaCtrl := Finmap.mem_of_lookup_eq_some hlookup
    obtain ⟨b, hmem⟩ := (hlink.1 x).mp (Or.inl hxCtrl)
    obtain ⟨v, hlookup0⟩ := Finmap.mem_iff.mp hmem
    have htof : Basis.tof b = .space s :=
      hlink.2.1 x s b hlookup hmem
    have hx0 : x ∈ Psi0.names :=
      EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hmem⟩
    have hx : x ∈ Psi.names :=
      EvalCtx.Subctx.names_subset hfuture.subctx hx0
    refine ⟨.paired hx ⟨b, v, hfuture.subctx (x, b) v hlookup0, htof, {
      valid := raw_basisValid_mono
        (hlink.2.2.2 x b hmem) hGamma
      quad := ?_ }
      ⟩ ?_⟩
    intro Psi' Gamma' hhybrid hGamma' hwf
    exact store hlookup0 (hfuture.trans hhybrid.fresh)
      (hGamma.trans hGamma') hwf
    · intro b' v' hlookupPsi _htof
      have hlookupRoot := hfuture.lookup_root_of_root_name hx0 hlookupPsi
      exact raw_basisValid_mono
        (hlink.2.2.2 x b'
          (Finmap.mem_of_lookup_eq_some hlookupRoot)) hGamma
  · intro x tau hlookup
    have hxCtrl : x ∈ GammaCtrl := Finmap.mem_of_lookup_eq_some hlookup
    obtain ⟨b, hmem⟩ := (hlink.1 x).mp (Or.inr hxCtrl)
    obtain ⟨v, hlookup0⟩ := Finmap.mem_iff.mp hmem
    have htof : Basis.tof b = tau :=
      hlink.2.2.1 x tau b hlookup hmem
    have hx0 : x ∈ Psi0.names :=
      EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hmem⟩
    have hx : x ∈ Psi.names :=
      EvalCtx.Subctx.names_subset hfuture.subctx hx0
    refine ⟨.paired hx ⟨b, v, hfuture.subctx (x, b) v hlookup0, htof, {
      valid := raw_basisValid_mono
        (hlink.2.2.2 x b hmem) hGamma
      quad := ?_ }
      ⟩ ?_⟩
    intro Psi' Gamma' hhybrid hGamma' hwf
    exact store hlookup0 (hfuture.trans hhybrid.fresh)
      (hGamma.trans hGamma') hwf
    · intro b' v' hlookupPsi _htof
      have hlookupRoot := hfuture.lookup_root_of_root_name hx0 hlookupPsi
      exact raw_basisValid_mono
        (hlink.2.2.2 x b'
          (Finmap.mem_of_lookup_eq_some hlookupRoot)) hGamma

private theorem no_lookup_at_fresh_name
    {Psi : EvalCtx} {y : VName} (hy : y ∉ Psi.names)
    {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi (y, b) = some v) : False :=
  hy (EvalCtx.mem_names_of_lookup hlookup)

/-- Add an ordinary linear binder as a standard-provenance reservation.  No
recursive pair for the binder's standard basis is requested. -/
theorem CheckedRelaxedControlledContextSelectedAt.insertLinearStandard
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget)
    {y : VName} {s : Space}
    (hyPsi : y ∉ Psi.names) (hyReserved : y ∉ reserved)
    (_hyDelta : y ∉ DeltaCtrl)
    (hvalid : Basis.BasisValid GammaTarget (Basis.stdSpace s)) :
    CheckedRelaxedControlledContextSelectedAt Psi
      (Finmap.insert y (.space s) reserved) depth
      (Finmap.insert y s DeltaCtrl) GammaCtrl GammaTarget := by
  let reserved' := Finmap.insert y (.space s) reserved
  let hReserved : NLCtxIncl reserved reserved' :=
    (NLCtxIncl.refl reserved).insert_right hyReserved (.space s)
  refine {
    lin := ?_
    nlin := ?_ }
  · intro x sx hlookup
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      exact ⟨.standard (by simp only [Finmap.lookup_insert]) hvalid
        (fun hlookup _ => False.elim
          (no_lookup_at_fresh_name hyPsi hlookup))⟩
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact (self.lin hlookup).strengthenReserved hReserved
  · intro x tau hlookup
    exact (self.nlin hlookup).strengthenReserved hReserved

/-- Add an ordinary nonlinear binder as a standard-provenance reservation
and extend the controlled/target nonlinear contexts in lockstep. -/
theorem CheckedRelaxedControlledContextSelectedAt.insertNonlinearStandard
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget)
    {y : VName} {tau : Ty}
    (hyPsi : y ∉ Psi.names) (hyReserved : y ∉ reserved)
    (_hyCtrl : y ∉ GammaCtrl) (hyTarget : y ∉ GammaTarget)
    (hvalid : Basis.BasisValid GammaTarget (Basis.std tau)) :
    CheckedRelaxedControlledContextSelectedAt Psi
      (Finmap.insert y tau reserved) depth DeltaCtrl
      (Finmap.insert y tau GammaCtrl)
      (Finmap.insert y tau GammaTarget) := by
  let reserved' := Finmap.insert y tau reserved
  let hReserved : NLCtxIncl reserved reserved' :=
    (NLCtxIncl.refl reserved).insert_right hyReserved tau
  let target' := Finmap.insert y tau GammaTarget
  let hTarget : NLCtxIncl GammaTarget target' :=
    (NLCtxIncl.refl GammaTarget).insert_right hyTarget tau
  refine {
    lin := ?_
    nlin := ?_ }
  · intro x s hlookup
    exact ((self.lin hlookup).rebaseContext hTarget).strengthenReserved
      hReserved
  · intro x tauX hlookup
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      exact ⟨.standard (by simp only [Finmap.lookup_insert])
        (raw_basisValid_mono hvalid hTarget)
        (fun hlookup _ => False.elim
          (no_lookup_at_fresh_name hyPsi hlookup))⟩
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact ((self.nlin hlookup).rebaseContext hTarget).strengthenReserved
        hReserved

/-- Install a literal dependent-frame endpoint as a pair-backed entry. -/
theorem CheckedRelaxedControlledContextSelectedAt.extendFrameNonlinear
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget)
    {y : VName} {tau : Ty} {bArg : Basis} {v : ValExpr}
    (hyPsi : y ∉ Psi.names) (hyReserved : y ∉ reserved)
    (_hyDelta : y ∉ DeltaCtrl) (_hyCtrl : y ∉ GammaCtrl)
    (hyTarget : y ∉ GammaTarget)
    (_htof : Basis.tof bArg = tau)
    (domain : CheckedFreeStdHybridSelectedAt Psi GammaTarget reserved
      depth bArg) :
    CheckedRelaxedControlledContextSelectedAt (Psi.extend y bArg v)
      reserved depth DeltaCtrl (Finmap.insert y tau GammaCtrl)
      (Finmap.insert y tau GammaTarget) := by
  let Psi' := Psi.extend y bArg v
  let target' := Finmap.insert y tau GammaTarget
  let hfuture : CheckedHybridFuture Psi Psi' reserved :=
    (CheckedHybridFuture.refl Psi reserved).extend
      hyPsi hyReserved bArg v
  let hTarget : NLCtxIncl GammaTarget target' :=
    (NLCtxIncl.refl GammaTarget).insert_right hyTarget tau
  refine {
    lin := ?_
    nlin := ?_ }
  · intro x s hlookup
    exact (self.lin hlookup).rebase hfuture hTarget
  · intro x tauX hlookup
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hlookup
      obtain rfl := Option.some.inj hlookup
      have hyOwned : y ∈ Psi'.names := by
        apply EvalCtx.mem_names_of_lookup (b := bArg) (v := v)
        simp only [Psi', EvalCtx.lookup, EvalCtx.extend,
          Finmap.lookup_insert]
      have insertedLookup : EvalCtx.lookup Psi' (y, bArg) = some v := by
        simp only [Psi', EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert]
      let package := domain.rebase hfuture hTarget
      refine ⟨.paired hyOwned
        ⟨bArg, v, insertedLookup, _htof, package⟩ ?_⟩
      intro b vX hlookupX htofX
      have hb : b = bArg := by
        apply hfuture.fresh.extra_name_unique y b bArg
        · exact Finmap.mem_of_lookup_eq_some hlookupX
        · intro hmem
          exact hyPsi (EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hmem⟩)
        · exact Finmap.mem_insert.mpr (Or.inl rfl)
      subst b
      exact package.valid
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact (self.nlin hlookup).rebase hfuture hTarget

mutual

def RelaxedBinderInputsS (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {GammaCtrl : NLCtx} -> {s : Space} -> SValid GammaCtrl s -> Prop
  | _, _, .empty => True
  | _, _, .real => True
  | _, _, .dual hs => RelaxedBinderInputsS Psi depth GammaTarget hs
  | _, _, .dsum hs0 hs1 =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1
  | _, _, .tprod hs0 hs1 =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1
  | _, _, .ker hs0 hs1 ht =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget ht
  | _, _, .coker hs0 hs1 ht =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget ht
  | _, _, .img hs0 hs1 ht =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget ht
  | _, _, .coimg hs0 hs1 ht =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget ht

def RelaxedBinderInputsT (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {GammaCtrl : NLCtx} -> {tau : Ty} -> {k : Kind} ->
      TValid GammaCtrl tau k -> Prop
  | _, _, _, .space hs => RelaxedBinderInputsS Psi depth GammaTarget hs
  | _, _, _, @TValid.piTy _ tau0 _ _ _ _ ht0 hbody =>
      RelaxedBinderInputsT Psi depth GammaTarget ht0 /\
      True /\
      forall y hy, RelaxedBinderInputsT Psi depth
        (Finmap.insert y tau0 GammaTarget) (hbody y hy)

def RelaxedBinderInputsSub (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {GammaCtrl : NLCtx} -> {s0 s1 : Space} ->
      SubType GammaCtrl s0 s1 -> Prop
  | _, _, _, .sub_ker hs0 hs1 ht =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget ht
  | _, _, _, .sub_coker hs0 hs1 ht =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget ht
  | _, _, _, .sub_img hs0 hs1 ht =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget ht
  | _, _, _, .sub_coimg hs0 hs1 ht =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget ht

def RelaxedBinderInputsH (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {Delta : LCtx} -> {GammaCtrl : NLCtx} -> {e : Term} -> {tau : Ty} ->
      HasType Delta GammaCtrl e tau -> Prop
  | _, _, _, _, .zero hs => RelaxedBinderInputsS Psi depth GammaTarget hs
  | _, _, _, _, .smul hs _ h0 h1 =>
      RelaxedBinderInputsS Psi depth GammaTarget hs /\
      RelaxedBinderInputsH Psi depth GammaTarget h0 /\
      RelaxedBinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .add hs h0 h1 =>
      RelaxedBinderInputsS Psi depth GammaTarget hs /\
      RelaxedBinderInputsH Psi depth GammaTarget h0 /\
      RelaxedBinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .inner hs => RelaxedBinderInputsS Psi depth GammaTarget hs
  | _, _, _, _, .real_lit _ => True
  | _, _, _, _, .app_linear hs0 hs1 _ h0 h1 =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget h0 /\
      RelaxedBinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .app_inner hs _ h0 h1 =>
      RelaxedBinderInputsS Psi depth GammaTarget hs /\
      RelaxedBinderInputsH Psi depth GammaTarget h0 /\
      RelaxedBinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .app_nonlinear h0 h1 =>
      RelaxedBinderInputsH Psi depth GammaTarget h0 /\
      RelaxedBinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .var_lin => True
  | _, _, _, _, .var_nlin _ => True
  | _, _, _, _, .pinv_tensor hs0 hs1 ht =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget ht
  | _, _, _, _, .pinv_dual hs ht =>
      RelaxedBinderInputsS Psi depth GammaTarget hs /\
      RelaxedBinderInputsH Psi depth GammaTarget ht
  | _, _, _, _, .promote _ _ _ _ ht =>
      RelaxedBinderInputsH Psi depth GammaTarget ht
  | _, _, _, _, .dsumE hs0 hs1 h0 h1 =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget h0 /\
      RelaxedBinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .tprodE hs0 hs1 _ h0 h1 =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs1 /\
      RelaxedBinderInputsH Psi depth GammaTarget h0 /\
      RelaxedBinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, @HasType.llam_real _ _ s _ _ hs hbody =>
      RelaxedBinderInputsS Psi depth GammaTarget hs /\
      True /\
      forall y hy, RelaxedBinderInputsH Psi depth GammaTarget (hbody y hy)
  | _, _, _, _, @HasType.llam_tensor _ _ s0 _ _ _ _ hs0 hs hbody =>
      RelaxedBinderInputsS Psi depth GammaTarget hs0 /\
      RelaxedBinderInputsS Psi depth GammaTarget hs /\
      True /\
      forall y hy, RelaxedBinderInputsH Psi depth GammaTarget (hbody y hy)
  | _, _, _, _, .embed hsub => RelaxedBinderInputsSub Psi depth GammaTarget hsub
  | _, _, _, _, @HasType.nllam _ tau0 _ _ _ _ _ ht hbody =>
      RelaxedBinderInputsT Psi depth GammaTarget ht /\
      True /\
      forall y hy, RelaxedBinderInputsH Psi depth
        (Finmap.insert y tau0 GammaTarget) (hbody y hy)

end

/-! The bookkeeping predicates carry no external evidence. -/

mutual

noncomputable def relaxedBinderInputsS_all
    (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {GammaCtrl : NLCtx} -> {s : Space} ->
      (h : SValid GammaCtrl s) ->
      RelaxedBinderInputsS Psi depth GammaTarget h
  | _, _, .empty => True.intro
  | _, _, .real => True.intro
  | _, _, .dual hs => relaxedBinderInputsS_all Psi depth GammaTarget hs
  | _, _, .dsum hs0 hs1 =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1⟩
  | _, _, .tprod hs0 hs1 =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1⟩
  | _, _, .ker hs0 hs1 ht =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget ht⟩
  | _, _, .coker hs0 hs1 ht =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget ht⟩
  | _, _, .img hs0 hs1 ht =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget ht⟩
  | _, _, .coimg hs0 hs1 ht =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget ht⟩

noncomputable def relaxedBinderInputsT_all
    (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {GammaCtrl : NLCtx} -> {tau : Ty} -> {k : Kind} ->
      (h : TValid GammaCtrl tau k) ->
      RelaxedBinderInputsT Psi depth GammaTarget h
  | _, _, _, .space hs =>
      relaxedBinderInputsS_all Psi depth GammaTarget hs
  | _, _, _, @TValid.piTy _ tau0 _ _ _ _ ht0 hbody =>
      ⟨relaxedBinderInputsT_all Psi depth GammaTarget ht0,
        True.intro,
        fun y hy => relaxedBinderInputsT_all Psi depth
          (Finmap.insert y tau0 GammaTarget) (hbody y hy)⟩

noncomputable def relaxedBinderInputsSub_all
    (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {GammaCtrl : NLCtx} -> {s0 s1 : Space} ->
      (h : SubType GammaCtrl s0 s1) ->
      RelaxedBinderInputsSub Psi depth GammaTarget h
  | _, _, _, .sub_ker hs0 hs1 ht =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget ht⟩
  | _, _, _, .sub_coker hs0 hs1 ht =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget ht⟩
  | _, _, _, .sub_img hs0 hs1 ht =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget ht⟩
  | _, _, _, .sub_coimg hs0 hs1 ht =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget ht⟩

noncomputable def relaxedBinderInputsH_all
    (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {Delta : LCtx} -> {GammaCtrl : NLCtx} -> {e : Term} -> {tau : Ty} ->
      (h : HasType Delta GammaCtrl e tau) ->
      RelaxedBinderInputsH Psi depth GammaTarget h
  | _, _, _, _, .zero hs =>
      relaxedBinderInputsS_all Psi depth GammaTarget hs
  | _, _, _, _, .smul hs _ h0 h1 =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs,
        relaxedBinderInputsH_all Psi depth GammaTarget h0,
        relaxedBinderInputsH_all Psi depth GammaTarget h1⟩
  | _, _, _, _, .add hs h0 h1 =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs,
        relaxedBinderInputsH_all Psi depth GammaTarget h0,
        relaxedBinderInputsH_all Psi depth GammaTarget h1⟩
  | _, _, _, _, .inner hs =>
      relaxedBinderInputsS_all Psi depth GammaTarget hs
  | _, _, _, _, .real_lit _ => True.intro
  | _, _, _, _, .app_linear hs0 hs1 _ h0 h1 =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget h0,
        relaxedBinderInputsH_all Psi depth GammaTarget h1⟩
  | _, _, _, _, .app_inner hs _ h0 h1 =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs,
        relaxedBinderInputsH_all Psi depth GammaTarget h0,
        relaxedBinderInputsH_all Psi depth GammaTarget h1⟩
  | _, _, _, _, .app_nonlinear h0 h1 =>
      ⟨relaxedBinderInputsH_all Psi depth GammaTarget h0,
        relaxedBinderInputsH_all Psi depth GammaTarget h1⟩
  | _, _, _, _, .var_lin => True.intro
  | _, _, _, _, .var_nlin _ => True.intro
  | _, _, _, _, .pinv_tensor hs0 hs1 ht =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget ht⟩
  | _, _, _, _, .pinv_dual hs ht =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs,
        relaxedBinderInputsH_all Psi depth GammaTarget ht⟩
  | _, _, _, _, .promote _ _ _ _ ht =>
      relaxedBinderInputsH_all Psi depth GammaTarget ht
  | _, _, _, _, .dsumE hs0 hs1 h0 h1 =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget h0,
        relaxedBinderInputsH_all Psi depth GammaTarget h1⟩
  | _, _, _, _, .tprodE hs0 hs1 _ h0 h1 =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs1,
        relaxedBinderInputsH_all Psi depth GammaTarget h0,
        relaxedBinderInputsH_all Psi depth GammaTarget h1⟩
  | _, _, _, _, @HasType.llam_real _ _ _ _ _ hs hbody =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs, True.intro,
        fun y hy => relaxedBinderInputsH_all Psi depth GammaTarget
          (hbody y hy)⟩
  | _, _, _, _, @HasType.llam_tensor _ _ _ _ _ _ _ hs0 hs hbody =>
      ⟨relaxedBinderInputsS_all Psi depth GammaTarget hs0,
        relaxedBinderInputsS_all Psi depth GammaTarget hs, True.intro,
        fun y hy => relaxedBinderInputsH_all Psi depth GammaTarget
          (hbody y hy)⟩
  | _, _, _, _, .embed hsub =>
      relaxedBinderInputsSub_all Psi depth GammaTarget hsub
  | _, _, _, _, @HasType.nllam _ tau0 _ _ _ _ _ ht hbody =>
      ⟨relaxedBinderInputsT_all Psi depth GammaTarget ht, True.intro,
        fun y hy => relaxedBinderInputsH_all Psi depth
          (Finmap.insert y tau0 GammaTarget) (hbody y hy)⟩

end

/-! ## Simultaneous target derivation and local-side results -/

structure RelaxedResultS (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx)
    {GammaCtrl : NLCtx} {s : Space} (_h : SValid GammaCtrl s) : Type where
  target : SValid GammaTarget s
  promotionFree : Graded.SPromotionFree target
  side : CheckedPairOrStandardLocalSideS Psi depth target

structure RelaxedResultT (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx)
    {GammaCtrl : NLCtx} {tau : Ty} {k : Kind}
    (_h : TValid GammaCtrl tau k) : Type where
  target : TValid GammaTarget tau k
  promotionFree : Graded.TPromotionFree target
  side : CheckedPairOrStandardLocalSideT Psi depth target

structure RelaxedResultSub (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx)
    {GammaCtrl : NLCtx} {s0 s1 : Space}
    (_h : SubType GammaCtrl s0 s1) : Type where
  target : SubType GammaTarget s0 s1
  promotionFree : Graded.SubPromotionFree target
  side : CheckedPairOrStandardLocalSideSub Psi depth target

structure RelaxedResultH (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx)
    {Delta : LCtx} {GammaCtrl : NLCtx} {e : Term} {tau : Ty}
    (_h : HasType Delta GammaCtrl e tau) : Type where
  target : HasType Delta GammaTarget e tau
  promotionFree : Graded.PromotionFree target
  side : CheckedPairOrStandardLocalSideBases Psi depth target

/-! ## Controlled variable seam -/

private theorem resolveRelaxedEntryAtRoot
    {Psi : EvalCtx} {Gamma reserved : NLCtx} {depth : Nat}
    {x : VName} {tau : Ty}
    (entry : CheckedRelaxedContextSelectedEntryAt Psi Gamma reserved
      depth x tau)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (Psi' : EvalCtx) (hfuture : CheckedStdFuture Psi Psi')
    (available : exists b : Basis, exists v : ValExpr,
      EvalCtx.lookup Psi' (x, b) = some v /\ Basis.tof b = tau) :
    exists b : Basis, exists v : ValExpr,
      EvalCtx.lookup Psi' (x, b) = some v /\ Basis.tof b = tau /\
      exists hb : Basis.BasisValid Gamma b,
        CheckedFreeStdSelectedAt Psi depth hb :=
  entry.resolveSelected hwf (CheckedHybridFuture.ofStandard hfuture) available

private theorem relaxedLeafLinDeep
    {Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {reserved : NLCtx} {Delta : LCtx} {depth : Nat}
    {x : VName} {s : Space}
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth Delta
      GammaCtrl GammaTarget)
    (hlookupCtrl : Delta.lookup x = some s)
    (hwf : V2.CtxWF' (Finmap.singleton x s) GammaTarget) :
    CheckedLocalTermSideBasisWith (CheckedFreeStdSelectedAt Psi depth) Psi
      (HasType.var_lin :
        HasType (Finmap.singleton x s) GammaTarget (.var x) (.space s)) := by
  intro Psi' hfuture
  refine ⟨?_, ?_⟩
  · intro hcov
    obtain ⟨b, hmem, htof⟩ :=
      hcov.1 x s Finmap.lookup_singleton_eq
    obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp hmem
    obtain ⟨b, v, hlookup, htof, hb, hselected⟩ := resolveRelaxedEntryAtRoot
      (selected.lin hlookupCtrl)
      (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
      Psi' hfuture ⟨b, v, hlookup, htof⟩
    exact ⟨b, v, hlookup, htof, hb, hselected⟩
  · intro b v hlookup htof
    exact (selected.lin hlookupCtrl).lookupValid
      (CheckedHybridFuture.ofStandard hfuture) hlookup htof

private theorem relaxedLeafLinShallow
    {Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {reserved : NLCtx} {Delta : LCtx} {depth : Nat}
    {x : VName} {s : Space}
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth Delta
      GammaCtrl GammaTarget)
    (hlookupCtrl : Delta.lookup x = some s)
    (hwf : V2.CtxWF' (Finmap.singleton x s) GammaTarget) :
    CheckedLocalTermSideBasis Psi
      (HasType.var_lin :
        HasType (Finmap.singleton x s) GammaTarget (.var x) (.space s)) := by
  intro b v hlookup htof
  exact (selected.lin hlookupCtrl).lookupValid
    (CheckedHybridFuture.refl Psi reserved) hlookup htof

private theorem relaxedLeafNlinDeep
    {Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {reserved : NLCtx} {Delta : LCtx} {depth : Nat}
    {x : VName} {tau : Ty}
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth Delta
      GammaCtrl GammaTarget)
    (hlookupCtrl : GammaCtrl.lookup x = some tau)
    (hlookupTarget : GammaTarget.lookup x = some tau)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget) :
    CheckedLocalTermSideBasisWith (CheckedFreeStdSelectedAt Psi depth) Psi
      (HasType.var_nlin hlookupTarget) := by
  intro Psi' hfuture
  refine ⟨?_, ?_⟩
  · intro hcov
    obtain ⟨b, hmem, htof⟩ := hcov.2 x tau hlookupTarget
    obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp hmem
    obtain ⟨b, v, hlookup, htof, hb, hselected⟩ :=
      resolveRelaxedEntryAtRoot (selected.nlin hlookupCtrl) hwf Psi' hfuture
        ⟨b, v, hlookup, htof⟩
    exact ⟨b, v, hlookup, htof, hb, hselected⟩
  · intro b v hlookup htof
    exact (selected.nlin hlookupCtrl).lookupValid
      (CheckedHybridFuture.ofStandard hfuture) hlookup htof

private theorem relaxedLeafNlinShallow
    {Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {reserved : NLCtx} {Delta : LCtx} {depth : Nat}
    {x : VName} {tau : Ty}
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth Delta
      GammaCtrl GammaTarget)
    (hlookupCtrl : GammaCtrl.lookup x = some tau)
    (hlookupTarget : GammaTarget.lookup x = some tau)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget) :
    CheckedLocalTermSideBasis Psi (HasType.var_nlin hlookupTarget) := by
  intro b v hlookup htof
  exact (selected.nlin hlookupCtrl).lookupValid
    (CheckedHybridFuture.refl Psi reserved) hlookup htof

private theorem linearIncl_union_left
    (Delta0 Delta1 : LCtx) :
    LinearCtxIncl Delta0 (Delta0 ∪ Delta1) := by
  intro x s hlookup
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hlookup)]
  exact hlookup

private theorem linearIncl_empty (Delta : LCtx) :
    LinearCtxIncl (∅ : LCtx) Delta := by
  intro x s hlookup
  cases hlookup

private theorem linearIncl_union_right
    {Delta0 Delta1 : LCtx} (hdisj : Finmap.Disjoint Delta0 Delta1) :
    LinearCtxIncl Delta1 (Delta0 ∪ Delta1) := by
  intro x s hlookup
  have hx1 : x ∈ Delta1 := Finmap.mem_of_lookup_eq_some hlookup
  have hx0 : x ∉ Delta0 := fun hx => hdisj x hx hx1
  rw [Finmap.lookup_union_right hx0]
  exact hlookup

/-- A target derivation may choose a larger cofinite set than the controlled
source proof.  Reserving every live namespace here supplies all freshness
facts required to replay an ordinary binder and to add its standard-only
provenance slot. -/
private noncomputable def traversalBinderAvoid
    (L : Finset Name) (Psi : EvalCtx) (reserved : NLCtx)
    (Delta : LCtx) (GammaCtrl GammaTarget : NLCtx) : Finset Name :=
  L ∪ (Psi.names ∪ (reserved.keys ∪
    (Delta.keys ∪ (GammaCtrl.keys ∪ GammaTarget.keys))))

private structure TraversalBinderFresh
    (L : Finset Name) (Psi : EvalCtx) (reserved : NLCtx)
    (Delta : LCtx) (GammaCtrl GammaTarget : NLCtx)
    (y : Name) : Prop where
  source : y ∉ L
  eval : y ∉ Psi.names
  reserved : y ∉ reserved
  linear : y ∉ Delta
  controlled : y ∉ GammaCtrl
  target : y ∉ GammaTarget

private theorem traversalBinderFresh_of_not_mem
    {L : Finset Name} {Psi : EvalCtx} {reserved : NLCtx}
    {Delta : LCtx} {GammaCtrl GammaTarget : NLCtx} {y : Name}
    (hy : y ∉ traversalBinderAvoid L Psi reserved Delta
      GammaCtrl GammaTarget) :
    TraversalBinderFresh L Psi reserved Delta GammaCtrl GammaTarget y := by
  have parts : y ∉ L /\ y ∉ Psi.names /\ y ∉ reserved.keys /\
      y ∉ Delta.keys /\ y ∉ GammaCtrl.keys /\ y ∉ GammaTarget.keys := by
    simpa only [traversalBinderAvoid, Finset.mem_union, not_or] using hy
  exact {
    source := parts.1
    eval := parts.2.1
    reserved := fun hm => parts.2.2.1 (Finmap.mem_keys.mpr hm)
    linear := fun hm => parts.2.2.2.1 (Finmap.mem_keys.mpr hm)
    controlled := fun hm => parts.2.2.2.2.1 (Finmap.mem_keys.mpr hm)
    target := fun hm => parts.2.2.2.2.2 (Finmap.mem_keys.mpr hm) }

private def relaxed_tvalid_pi_domain
    {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind}
    (h : TValid Gamma (.piTy tau0 tau1) (.arrow k0 k1)) :
    TValid Gamma tau0 k0 := by
  cases h with
  | piTy _ ht0 _ => exact ht0

/-! ## Simultaneous structural traversal -/

mutual

/-- Replay a controlled space-validity derivation in the target context and
build its fixed-depth local-side tree in the same recursion. -/
noncomputable def ofSCore
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat} {A : Finset Name}
    {GammaCtrl GammaTarget : NLCtx} {s : Space}
    (h : SValid GammaCtrl s)
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth (∅ : LCtx)
      GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hPsi : True)
    (hcover : True)
    (hinputs : RelaxedBinderInputsS Psi depth GammaTarget h)
    (hfree : Graded.SPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.SBinderHygiene A h) :
    RelaxedResultS Psi depth GammaTarget h :=
  match h with
  | .empty =>
      let ht : SValid GammaTarget .empty := .empty
      ⟨ht, True.intro, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, PUnit.unit⟩ ⟨True.intro, PUnit.unit⟩⟩
  | .real =>
      let ht : SValid GammaTarget .real := .real
      ⟨ht, True.intro, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, PUnit.unit⟩ ⟨True.intro, PUnit.unit⟩⟩
  | .dual hs =>
      let r := ofSCore hs selected hinc hwf hPsi hcover hinputs hfree hhyg
      let ht : SValid GammaTarget (.dual _) := .dual r.target
      ⟨ht, r.promotionFree, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, r.side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, r.side.deep⟩⟩⟩
  | .dsum hs0 hs1 =>
      let r0 := ofSCore hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofSCore hs1 selected hinc hwf hPsi hcover hinputs.2
        hfree.2 hhyg.2
      let ht : SValid GammaTarget (.dsum _ _) := .dsum r0.target r1.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree⟩,
        CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨True.intro, r1.side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨True.intro, r1.side.deep⟩⟩⟩⟩
  | .tprod hs0 hs1 =>
      let r0 := ofSCore hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofSCore hs1 selected hinc hwf hPsi hcover hinputs.2
        hfree.2 hhyg.2
      let ht : SValid GammaTarget (.tprod _ _) := .tprod r0.target r1.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree⟩,
        CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨True.intro, r1.side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨True.intro, r1.side.deep⟩⟩⟩⟩
  | .ker hs0 hs1 he =>
      let r0 := ofSCore hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofSCore hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofHCore he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SValid GammaTarget (.ker _ _ _) :=
        .ker r0.target r1.target re.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree, re.promotionFree⟩,
        CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .coker hs0 hs1 he =>
      let r0 := ofSCore hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofSCore hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofHCore he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SValid GammaTarget (.coker _ _ _) :=
        .coker r0.target r1.target re.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree, re.promotionFree⟩,
        CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .img hs0 hs1 he =>
      let r0 := ofSCore hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofSCore hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofHCore he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SValid GammaTarget (.img _ _ _) :=
        .img r0.target r1.target re.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree, re.promotionFree⟩,
        CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .coimg hs0 hs1 he =>
      let r0 := ofSCore hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofSCore hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofHCore he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SValid GammaTarget (.coimg _ _ _) :=
        .coimg r0.target r1.target re.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree, re.promotionFree⟩,
        CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩

/-- Replay a controlled type-validity derivation in the target context. -/
noncomputable def ofTCore
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat} {A : Finset Name}
    {GammaCtrl GammaTarget : NLCtx} {tau : Ty} {k : Kind}
    (h : TValid GammaCtrl tau k)
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth (∅ : LCtx)
      GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hPsi : True)
    (hcover : True)
    (hinputs : RelaxedBinderInputsT Psi depth GammaTarget h)
    (hfree : Graded.TPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.TBinderHygiene A h) :
    RelaxedResultT Psi depth GammaTarget h :=
  match h with
  | .space hs =>
      let r := ofSCore hs selected hinc hwf hPsi hcover hinputs hfree hhyg
      let ht : TValid GammaTarget (.space _) .base := .space r.target
      ⟨ht, r.promotionFree, CheckedLocalSideTWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, r.side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, r.side.deep⟩⟩⟩
  | @TValid.piTy GammaCtrl tau0 tau1 k0 k1 L ht0 hbody =>
      let r0 := ofTCore ht0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.2.2.1
      let LTarget := traversalBinderAvoid L Psi reserved (∅ : LCtx)
        GammaCtrl GammaTarget
      let bodyResult := fun y (hyTargetAvoid : y ∉ LTarget) =>
        let fresh := traversalBinderFresh_of_not_mem hyTargetAvoid
        let hy := fresh.source
        let hincY : NLCtxIncl (Finmap.insert y tau0 GammaCtrl)
            (Finmap.insert y tau0 GammaTarget) :=
          RawCertifiedOperational.NLCtxIncl.insert_same hinc y tau0
        let domainValid : Basis.BasisValid GammaTarget
            (Basis.std tau0) := Basis.std_valid tau0 r0.target
        let hwfY : V2.CtxWF' (∅ : LCtx)
            (Finmap.insert y tau0 GammaTarget) := by
          simpa only [Basis.tof_std] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
              (b := Basis.std tau0) hwf Finmap.notMem_empty fresh.target
              domainValid
        let selectedY := selected.insertNonlinearStandard
          fresh.eval fresh.reserved fresh.controlled fresh.target domainValid
        ofTCore (hbody y hy) selectedY hincY hwfY hPsi
          True.intro (hinputs.2.2 y hy)
          (hfree.2 y hy) (hhyg.2.2.2 y hy)
      let ht : TValid GammaTarget (.piTy tau0 tau1) (.arrow k0 k1) :=
        .piTy LTarget r0.target (fun y hy => (bodyResult y hy).target)
      ⟨ht, ⟨r0.promotionFree,
          fun y hy => (bodyResult y hy).promotionFree⟩,
        CheckedLocalSideTWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          fun y hy => ⟨True.intro,
            (bodyResult y hy).side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          fun y hy => ⟨True.intro, (bodyResult y hy).side.deep⟩⟩⟩⟩

/-- Replay a controlled subtyping derivation in the target context. -/
noncomputable def ofSubCore
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat} {A : Finset Name}
    {GammaCtrl GammaTarget : NLCtx} {s0 s1 : Space}
    (h : SubType GammaCtrl s0 s1)
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth (∅ : LCtx)
      GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hPsi : True)
    (hcover : True)
    (hinputs : RelaxedBinderInputsSub Psi depth GammaTarget h)
    (hfree : Graded.SubPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.SubBinderHygiene A h) :
    RelaxedResultSub Psi depth GammaTarget h :=
  match h with
  | .sub_ker hs0 hs1 he =>
      let r0 := ofSCore hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofSCore hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofHCore he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SubType GammaTarget (.ker _ _ _) _ :=
        .sub_ker r0.target r1.target re.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree, re.promotionFree⟩,
        CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .sub_coker hs0 hs1 he =>
      let r0 := ofSCore hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofSCore hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofHCore he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SubType GammaTarget (.coker _ _ _) _ :=
        .sub_coker r0.target r1.target re.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree, re.promotionFree⟩,
        CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .sub_img hs0 hs1 he =>
      let r0 := ofSCore hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofSCore hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofHCore he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SubType GammaTarget (.img _ _ _) _ :=
        .sub_img r0.target r1.target re.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree, re.promotionFree⟩,
        CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .sub_coimg hs0 hs1 he =>
      let r0 := ofSCore hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofSCore hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofHCore he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SubType GammaTarget (.coimg _ _ _) _ :=
        .sub_coimg r0.target r1.target re.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree, re.promotionFree⟩,
        CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩

/-- Replay a controlled promotion-free typing derivation in the target
context while constructing its proof-indexed fixed-depth local-side tree. -/
noncomputable def ofHCore
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat} {A : Finset Name}
    {Delta : LCtx} {GammaCtrl GammaTarget : NLCtx}
    {e : Term} {tau : Ty}
    (h : HasType Delta GammaCtrl e tau)
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth Delta
      GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' Delta GammaTarget)
    (hPsi : True)
    (hcover : True)
    (hinputs : RelaxedBinderInputsH Psi depth GammaTarget h)
    (hfree : Graded.PromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.BinderHygiene A h) :
    RelaxedResultH Psi depth GammaTarget h :=
  match h with
  | .zero hs =>
      let selected0 := selected.restrictLinear (linearIncl_empty Delta)
      let rs := ofSCore hs selected0 hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs hfree hhyg
      let ht : HasType Delta GammaTarget (.zero _) (.space _) := .zero rs.target
      ⟨ht, rs.promotionFree, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, rs.side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, rs.side.deep⟩⟩⟩
  | @HasType.smul Delta0 Delta1 GammaCtrl e0 e1 s
      hs hdisj h0 h1 =>
      let selectedEmpty := selected.restrictLinear
        (linearIncl_empty (Delta0 ∪ Delta1))
      let selected0 := selected.restrictLinear
        (linearIncl_union_left Delta0 Delta1)
      let selected1 := selected.restrictLinear
        (linearIncl_union_right hdisj)
      let rs := ofSCore hs selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let r0 := ofHCore h0 selected0 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_left hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.1
      let r1 := ofHCore h1 selected1 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf)
        hPsi hcover hinputs.2.2 hfree.2.2 hhyg.2.2
      let ht : HasType (Delta0 ∪ Delta1) GammaTarget (.smul _ _) (.space _) :=
        .smul rs.target hdisj r0.target r1.target
      ⟨ht, ⟨rs.promotionFree, r0.promotionFree, r1.promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs.side.shallow.descendants⟩,
          ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
            ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs.side.deep⟩,
          ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
            ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩⟩
  | .add hs h0 h1 =>
      let selectedEmpty := selected.restrictLinear (linearIncl_empty Delta)
      let rs := ofSCore hs selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let r0 := ofHCore h0 selected hinc hwf hPsi hcover
        hinputs.2.1 hfree.2.1 hhyg.2.1
      let r1 := ofHCore h1 selected hinc hwf hPsi hcover
        hinputs.2.2 hfree.2.2 hhyg.2.2
      let ht : HasType Delta GammaTarget (.add _ _) (.space _) :=
        .add rs.target r0.target r1.target
      ⟨ht, ⟨rs.promotionFree, r0.promotionFree, r1.promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs.side.shallow.descendants⟩,
          ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
            ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs.side.deep⟩,
          ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
            ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩⟩
  | .inner hs =>
      let rs := ofSCore hs selected hinc hwf hPsi hcover hinputs hfree hhyg
      let ht : HasType (∅ : LCtx) GammaTarget (.inner _) _ := .inner rs.target
      ⟨ht, rs.promotionFree, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, rs.side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, rs.side.deep⟩⟩⟩
  | .real_lit r =>
      let ht : HasType (∅ : LCtx) GammaTarget (.real r) (.space .real) :=
        .real_lit r
      ⟨ht, True.intro, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, PUnit.unit⟩ ⟨True.intro, PUnit.unit⟩⟩
  | @HasType.app_linear Delta0 Delta1 GammaCtrl e0 e1 s0 s1
      hs0 hs1 hdisj h0 h1 =>
      let selectedEmpty := selected.restrictLinear
        (linearIncl_empty (Delta0 ∪ Delta1))
      let selected0 := selected.restrictLinear
        (linearIncl_union_left Delta0 Delta1)
      let selected1 := selected.restrictLinear
        (linearIncl_union_right hdisj)
      let hwf0 := RawCertifiedWorldProgressArms.ctxWF_union_left hwf
      let hwf1 := RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf
      let rs0 := ofSCore hs0 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let rs1 := ofSCore hs1 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.1
      let r0 := ofHCore h0 selected0 hinc hwf0 hPsi hcover
        hinputs.2.2.1 hfree.2.2.1 hhyg.2.2.1
      let r1 := ofHCore h1 selected1 hinc hwf1 hPsi hcover
        hinputs.2.2.2 hfree.2.2.2 hhyg.2.2.2
      let ht : HasType (Delta0 ∪ Delta1) GammaTarget (.appL _ _ _ _) _ :=
        .app_linear rs0.target rs1.target hdisj r0.target r1.target
      ⟨ht, ⟨rs0.promotionFree, rs1.promotionFree,
          r0.promotionFree, r1.promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs0.side.shallow.descendants⟩,
          ⟨⟨True.intro, rs1.side.shallow.descendants⟩,
            ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
              ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs0.side.deep⟩,
          ⟨⟨True.intro, rs1.side.deep⟩,
            ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
              ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩⟩⟩
  | @HasType.app_inner Delta0 Delta1 GammaCtrl e0 e1 s
      hs hdisj h0 h1 =>
      let selectedEmpty := selected.restrictLinear
        (linearIncl_empty (Delta0 ∪ Delta1))
      let selected0 := selected.restrictLinear
        (linearIncl_union_left Delta0 Delta1)
      let selected1 := selected.restrictLinear
        (linearIncl_union_right hdisj)
      let rs := ofSCore hs selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let r0 := ofHCore h0 selected0 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_left hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.1
      let r1 := ofHCore h1 selected1 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf)
        hPsi hcover hinputs.2.2 hfree.2.2 hhyg.2.2
      let ht : HasType (Delta0 ∪ Delta1) GammaTarget (.appI _ _ _) _ :=
        .app_inner rs.target hdisj r0.target r1.target
      ⟨ht, ⟨rs.promotionFree, r0.promotionFree, r1.promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs.side.shallow.descendants⟩,
          ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
            ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs.side.deep⟩,
          ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
            ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩⟩
  | .app_nonlinear h0 h1 =>
      let r0 := ofHCore h0 selected hinc hwf hPsi hcover
        hinputs.1 hfree.1 hhyg.1
      let r1 := ofHCore h1 selected hinc hwf hPsi hcover
        hinputs.2 hfree.2 hhyg.2
      let ht : HasType (∅ : LCtx) GammaTarget (.appN _ _) _ :=
        .app_nonlinear r0.target r1.target
      ⟨ht, ⟨r0.promotionFree, r1.promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
          ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
          ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩
  | @HasType.var_lin GammaCtrl x s =>
      let ht : HasType (Finmap.singleton x s) GammaTarget (.var x) (.space s) :=
        .var_lin
      ⟨ht, True.intro, CheckedLocalSideBasesWith.ofBelowPair
        ⟨relaxedLeafLinShallow selected Finmap.lookup_singleton_eq hwf, PUnit.unit⟩
        ⟨relaxedLeafLinDeep selected Finmap.lookup_singleton_eq hwf, PUnit.unit⟩⟩
  | @HasType.var_nlin GammaCtrl x tau hlookupCtrl =>
      let hlookupTarget := hinc x tau hlookupCtrl
      let ht : HasType (∅ : LCtx) GammaTarget (.var x) tau :=
        .var_nlin hlookupTarget
      ⟨ht, True.intro, CheckedLocalSideBasesWith.ofBelowPair
        ⟨relaxedLeafNlinShallow selected hlookupCtrl hlookupTarget hwf, PUnit.unit⟩
        ⟨relaxedLeafNlinDeep selected hlookupCtrl hlookupTarget hwf, PUnit.unit⟩⟩
  | .pinv_tensor hs0 hs1 he =>
      let rs0 := ofSCore hs0 selected hinc hwf hPsi hcover
        hinputs.1 hfree.1 hhyg.1
      let rs1 := ofSCore hs1 selected hinc hwf hPsi hcover
        hinputs.2.1 hfree.2.1 hhyg.2.1
      let re := ofHCore he selected hinc hwf hPsi hcover
        hinputs.2.2 hfree.2.2 hhyg.2.2
      let ht : HasType (∅ : LCtx) GammaTarget (.pinvT _ _ _) _ :=
        .pinv_tensor rs0.target rs1.target re.target
      ⟨ht, ⟨rs0.promotionFree, rs1.promotionFree, re.promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs0.side.shallow.descendants⟩,
          ⟨⟨True.intro, rs1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs0.side.deep⟩,
          ⟨⟨True.intro, rs1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .pinv_dual hs he =>
      let rs := ofSCore hs selected hinc hwf hPsi hcover
        hinputs.1 hfree.1 hhyg.1
      let re := ofHCore he selected hinc hwf hPsi hcover
        hinputs.2 hfree.2 hhyg.2
      let ht : HasType (∅ : LCtx) GammaTarget (.pinvD _ _) _ :=
        .pinv_dual rs.target re.target
      ⟨ht, ⟨rs.promotionFree, re.promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs.side.shallow.descendants⟩,
          ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs.side.deep⟩,
          ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩
  | .promote _ _ _ _ _ => False.elim hfree
  | .dsumE hs0 hs1 h0 h1 =>
      let selectedEmpty := selected.restrictLinear (linearIncl_empty Delta)
      let rs0 := ofSCore hs0 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let rs1 := ofSCore hs1 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.1
      let r0 := ofHCore h0 selected hinc hwf hPsi hcover
        hinputs.2.2.1 hfree.2.2.1 hhyg.2.2.1
      let r1 := ofHCore h1 selected hinc hwf hPsi hcover
        hinputs.2.2.2 hfree.2.2.2 hhyg.2.2.2
      let ht : HasType Delta GammaTarget (.dsumE _ _) _ :=
        .dsumE rs0.target rs1.target r0.target r1.target
      ⟨ht, ⟨rs0.promotionFree, rs1.promotionFree,
          r0.promotionFree, r1.promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs0.side.shallow.descendants⟩,
          ⟨⟨True.intro, rs1.side.shallow.descendants⟩,
            ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
              ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs0.side.deep⟩,
          ⟨⟨True.intro, rs1.side.deep⟩,
            ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
              ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩⟩⟩
  | @HasType.tprodE Delta0 Delta1 GammaCtrl e0 e1 s0 s1
      hs0 hs1 hdisj h0 h1 =>
      let selectedEmpty := selected.restrictLinear
        (linearIncl_empty (Delta0 ∪ Delta1))
      let selected0 := selected.restrictLinear
        (linearIncl_union_left Delta0 Delta1)
      let selected1 := selected.restrictLinear
        (linearIncl_union_right hdisj)
      let rs0 := ofSCore hs0 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let rs1 := ofSCore hs1 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.1
      let r0 := ofHCore h0 selected0 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_left hwf)
        hPsi hcover hinputs.2.2.1 hfree.2.2.1 hhyg.2.2.1
      let r1 := ofHCore h1 selected1 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf)
        hPsi hcover hinputs.2.2.2 hfree.2.2.2 hhyg.2.2.2
      let ht : HasType (Delta0 ∪ Delta1) GammaTarget (.tprodE _ _) _ :=
        .tprodE rs0.target rs1.target hdisj r0.target r1.target
      ⟨ht, ⟨rs0.promotionFree, rs1.promotionFree,
          r0.promotionFree, r1.promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs0.side.shallow.descendants⟩,
          ⟨⟨True.intro, rs1.side.shallow.descendants⟩,
            ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
              ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs0.side.deep⟩,
          ⟨⟨True.intro, rs1.side.deep⟩,
            ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
              ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩⟩⟩
  | @HasType.llam_real Delta GammaCtrl s e L hs hbody =>
      let selectedEmpty := selected.restrictLinear (linearIncl_empty Delta)
      let rs := ofSCore hs selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.2.2.2.1
      let LTarget := traversalBinderAvoid L Psi reserved Delta
        GammaCtrl GammaTarget
      let bodyResult := fun y (hyTargetAvoid : y ∉ LTarget) =>
        let fresh := traversalBinderFresh_of_not_mem hyTargetAvoid
        let hy := fresh.source
        let domainValid : Basis.BasisValid GammaTarget
            (Basis.stdSpace s) := Basis.stdSpace_valid s rs.target
        let hwfY : V2.CtxWF' (Finmap.insert y s Delta) GammaTarget := by
          simpa only [Basis.sof_stdSpace] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
              (b := Basis.stdSpace s) hwf fresh.linear fresh.target
              domainValid
        let selectedY := selected.insertLinearStandard fresh.eval
          fresh.reserved fresh.linear domainValid
        ofHCore (hbody y hy) selectedY hinc hwfY hPsi hcover
          (hinputs.2.2 y hy) (hfree.2 y hy) (hhyg.2.2.2.2 y hy)
      let ht : HasType Delta GammaTarget (.llam s .real e) (.space (.dual s)) :=
        .llam_real LTarget rs.target (fun y hy => (bodyResult y hy).target)
      ⟨ht, ⟨rs.promotionFree,
          fun y hy => (bodyResult y hy).promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs.side.shallow.descendants⟩,
          fun y hy => ⟨(bodyResult y hy).side.shallow.here,
            (bodyResult y hy).side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs.side.deep⟩,
          fun y hy => ⟨(bodyResult y hy).side.deepHere,
            (bodyResult y hy).side.deepDescendants⟩⟩⟩⟩
  | @HasType.llam_tensor Delta GammaCtrl s0 s e L hne hs0 hs hbody =>
      let selectedEmpty := selected.restrictLinear (linearIncl_empty Delta)
      let rs0 := ofSCore hs0 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.2.2.2.1
      let rs := ofSCore hs selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.2.2.2.1
      let LTarget := traversalBinderAvoid L Psi reserved Delta
        GammaCtrl GammaTarget
      let bodyResult := fun y (hyTargetAvoid : y ∉ LTarget) =>
        let fresh := traversalBinderFresh_of_not_mem hyTargetAvoid
        let hy := fresh.source
        let domainValid : Basis.BasisValid GammaTarget
            (Basis.stdSpace s0) := Basis.stdSpace_valid s0 rs0.target
        let hwfY : V2.CtxWF' (Finmap.insert y s0 Delta) GammaTarget := by
          simpa only [Basis.sof_stdSpace] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
              (b := Basis.stdSpace s0) hwf fresh.linear fresh.target
              domainValid
        let selectedY := selected.insertLinearStandard fresh.eval
          fresh.reserved fresh.linear domainValid
        ofHCore (hbody y hy) selectedY hinc hwfY hPsi hcover
          (hinputs.2.2.2 y hy) (hfree.2.2 y hy)
          (hhyg.2.2.2.2.2 y hy)
      let ht : HasType Delta GammaTarget (.llam s0 s e) _ :=
        .llam_tensor LTarget hne rs0.target rs.target
          (fun y hy => (bodyResult y hy).target)
      ⟨ht, ⟨rs0.promotionFree, rs.promotionFree,
          fun y hy => (bodyResult y hy).promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs0.side.shallow.descendants⟩,
          ⟨⟨True.intro, rs.side.shallow.descendants⟩,
            fun y hy => ⟨(bodyResult y hy).side.shallow.here,
              (bodyResult y hy).side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs0.side.deep⟩,
          ⟨⟨True.intro, rs.side.deep⟩,
            fun y hy => ⟨(bodyResult y hy).side.deepHere,
              (bodyResult y hy).side.deepDescendants⟩⟩⟩⟩⟩
  | .embed hsub =>
      let r := ofSubCore hsub selected hinc hwf hPsi hcover
        hinputs hfree hhyg
      let ht : HasType (∅ : LCtx) GammaTarget (.embed _) _ := .embed r.target
      ⟨ht, r.promotionFree, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, r.side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, r.side.deep⟩⟩⟩
  | @HasType.nllam GammaCtrl tau0 tau1 k0 k1 e L ht hbody =>
      let rt := ofTCore ht selected hinc hwf hPsi hcover
        hinputs.1 hfree.1 hhyg.2.2.1
      let LTarget := traversalBinderAvoid L Psi reserved (∅ : LCtx)
        GammaCtrl GammaTarget
      let bodyResult := fun y (hyTargetAvoid : y ∉ LTarget) =>
        let fresh := traversalBinderFresh_of_not_mem hyTargetAvoid
        let hy := fresh.source
        let hincY : NLCtxIncl (Finmap.insert y tau0 GammaCtrl)
            (Finmap.insert y tau0 GammaTarget) :=
          RawCertifiedOperational.NLCtxIncl.insert_same hinc y tau0
        let domainValid : Basis.BasisValid GammaTarget
            (Basis.std tau0) :=
          Basis.std_valid tau0 (relaxed_tvalid_pi_domain rt.target)
        let hwfY : V2.CtxWF' (∅ : LCtx)
            (Finmap.insert y tau0 GammaTarget) := by
          simpa only [Basis.tof_std] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
              (b := Basis.std tau0) hwf Finmap.notMem_empty fresh.target
              domainValid
        let selectedY := selected.insertNonlinearStandard
          fresh.eval fresh.reserved fresh.controlled fresh.target domainValid
        ofHCore (hbody y hy) selectedY hincY hwfY hPsi
          True.intro (hinputs.2.2 y hy)
          (hfree.2 y hy) (hhyg.2.2.2 y hy)
      let hout : HasType (∅ : LCtx) GammaTarget (.nllam tau0 e)
          (.piTy tau0 tau1) :=
        .nllam LTarget rt.target (fun y hy => (bodyResult y hy).target)
      ⟨hout, ⟨rt.promotionFree,
          fun y hy => (bodyResult y hy).promotionFree⟩,
        CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rt.side.shallow.descendants⟩,
          fun y hy => ⟨(bodyResult y hy).side.shallow.here,
            (bodyResult y hy).side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rt.side.deep⟩,
          fun y hy => ⟨(bodyResult y hy).side.deepHere,
            (bodyResult y hy).side.deepDescendants⟩⟩⟩⟩

end

/-! ## Clean traversal surface

The core mutual block retains an internal proof-indexed routing value, but
that value is constructed structurally and exposes no premise.  These are
the interfaces consumed by creation-prefix construction. -/

/-- Replay space validity in the target context and construct its complete
free-standard source side. -/
noncomputable def ofS
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat} {A : Finset Name}
    {GammaCtrl GammaTarget : NLCtx} {s : Space}
    (h : SValid GammaCtrl s)
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      (∅ : LCtx) GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hfree : Graded.SPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.SBinderHygiene A h) :
    RelaxedResultS Psi depth GammaTarget h :=
  ofSCore h selected hinc hwf True.intro True.intro
    (relaxedBinderInputsS_all Psi depth GammaTarget h) hfree hhyg

/-- Replay type validity in the target context and construct its complete
free-standard source side. -/
noncomputable def ofT
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat} {A : Finset Name}
    {GammaCtrl GammaTarget : NLCtx} {tau : Ty} {k : Kind}
    (h : TValid GammaCtrl tau k)
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      (∅ : LCtx) GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hfree : Graded.TPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.TBinderHygiene A h) :
    RelaxedResultT Psi depth GammaTarget h :=
  ofTCore h selected hinc hwf True.intro True.intro
    (relaxedBinderInputsT_all Psi depth GammaTarget h) hfree hhyg

/-- Replay subtyping in the target context and construct its complete
free-standard source side. -/
noncomputable def ofSub
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat} {A : Finset Name}
    {GammaCtrl GammaTarget : NLCtx} {s0 s1 : Space}
    (h : SubType GammaCtrl s0 s1)
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      (∅ : LCtx) GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hfree : Graded.SubPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.SubBinderHygiene A h) :
    RelaxedResultSub Psi depth GammaTarget h :=
  ofSubCore h selected hinc hwf True.intro True.intro
    (relaxedBinderInputsSub_all Psi depth GammaTarget h) hfree hhyg

/-- Replay a promotion-free typing derivation in the target context and
construct its complete free-standard source side. -/
noncomputable def ofH
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat} {A : Finset Name}
    {Delta : LCtx} {GammaCtrl GammaTarget : NLCtx}
    {e : Term} {tau : Ty}
    (h : HasType Delta GammaCtrl e tau)
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      Delta GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' Delta GammaTarget)
    (hfree : Graded.PromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.BinderHygiene A h) :
    RelaxedResultH Psi depth GammaTarget h :=
  ofHCore h selected hinc hwf True.intro True.intro
    (relaxedBinderInputsH_all Psi depth GammaTarget h) hfree hhyg

end RawCertifiedPairControlledSourceFreeStandard
end GLang
