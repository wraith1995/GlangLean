import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardNatProgress
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedCtxTele
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairCreationPrefixStore

/-!
# Checked progress from the operational context telescope

The public progress premises are only the semantic-free joint creation
history, source typing, and validity of the requested basis.  This module
constructs exact lookup anchors, finite syntax certificates, numeric depths,
and the final standard-to-requested transport internally.
-/

namespace GLang
namespace RawCertifiedCtxTeleProgress

open OperationalStrengthening
open RawCertifiedHereditaryStore
open RawCertifiedConsistentPairStore
open RawCertifiedPairFreeStandardStore
open RawCertifiedPairFreeStandardCreationPrefixStore
open RawCertifiedPairFreeStandardCreationPrefixLayer
open RawCertifiedPairFreeStandardCertificate
open RawCertifiedPairCertificate
open RawCertifiedPairFreeStandardNatProgress
open RawCertifiedExactAnchorStore
open RawCertifiedOperational
open RawCertifiedPairControlledSourceFreeStandard
open RawCertifiedPairFreeStandardCreationPrefixLayer
open RawCertifiedPairCreationDepth

theorem ctxWFPrime : forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx},
    V2.CtxTele Delta Gamma Psi -> V2.CtxWF' Delta Gamma := by
  intro Delta Gamma Psi h
  induction h with
  | empty =>
      exact {
        disjoint := fun _ hm => absurd hm Finmap.notMem_empty
        lin_fv := fun _ _ hm => absurd
          (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
        nl_fv := fun _ _ hm => absurd
          (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
        lin_valid := fun _ _ hm => absurd
          (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
        nl_valid := fun _ _ hm => absurd
          (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty }
  | extend_nlin hprefix hsource _hcreation hb ih =>
      exact RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
        ih hsource.freshLinear hsource.freshNonlinear hb
  | extend_lin hprefix hsource _hcreation hb htof ih =>
      have hwf := RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
        ih hsource.freshLinear hsource.freshNonlinear hb
      simpa only [Basis.sof_eq_of_tof_eq_space htof] using hwf
  | extend_rep hprefix hlink hkey _hcreation hb ih =>
      exact ih

theorem typingImplyEval : forall
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx},
    V2.CtxTele Delta Gamma Psi -> V2.TypingImplyEval Delta Gamma Psi := by
  intro Delta Gamma Psi h
  induction h with
  | empty =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x
        constructor
        · rintro (hx | hx) <;> exact absurd hx Finmap.notMem_empty
        · rintro ⟨b, hmem⟩
          exact absurd hmem Finmap.notMem_empty
      · intro x s b hlookup
        exact absurd (Finmap.mem_of_lookup_eq_some hlookup)
          Finmap.notMem_empty
      · intro x tau b hlookup
        exact absurd (Finmap.mem_of_lookup_eq_some hlookup)
          Finmap.notMem_empty
      · intro x b hmem
        exact absurd hmem Finmap.notMem_empty
  | @extend_nlin Delta Gamma Psi x b v hprefix hsource _hcreation hb ih =>
      exact RawLocalCtxWFInsertionScratch.typingImplyEval_insert_nl
        (v := v) ih hsource.freshLinear hsource.freshNonlinear
          (hprefix.freshEvalName hsource) hb
  | @extend_lin Delta Gamma Psi x b v s hprefix hsource hcreation hb htof ih =>
      have htypingLink := RawLocalCtxWFInsertionScratch.typingImplyEval_insert_lin
        (v := v) ih hsource.freshLinear hsource.freshNonlinear
          (hprefix.freshEvalName hsource) hb
          (by simpa only [Basis.sof_eq_of_tof_eq_space htof] using htof)
      simpa only [Basis.sof_eq_of_tof_eq_space htof] using htypingLink
  | @extend_rep Delta Gamma Psi x b v hprefix hsource hkey hcreation hb ih =>
      exact ih.extend_rep (ctxWFPrime hprefix) hsource hkey hb

/-! Multiple representations make a left-to-right rebase of already-built
certificates too strong: adding `(x,b₂)` must not retroactively turn it into
a dependency of the certificate that selected `(x,b₁)`.  The construction
below instead fixes the final evaluator root first and inducts over creation
prefixes inside that root.  Each source variable records one primary prefix
representation; all other representations contribute only their ordinary
`BasisValid` fact.  Binder worlds still use the original name-fresh
`CheckedFreshFuture`. -/

private def CheckedFreeStdPrefixStoreAt
    (Psi0 root : EvalCtx) (Gamma : NLCtx) (depth : Nat) : Prop :=
  forall {x : VName} {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi0 (x, b) = some v ->
      CheckedFreeStdFreshDepthQuadAt root Gamma depth b

private theorem CheckedFreeStdPrefixStoreAt.monoDepth
    {Psi0 root : EvalCtx} {Gamma : NLCtx} {depth depth' : Nat}
    (store : CheckedFreeStdPrefixStoreAt Psi0 root Gamma depth)
    (hle : depth <= depth') :
    CheckedFreeStdPrefixStoreAt Psi0 root Gamma depth' := by
  intro x b v hlookup Psi' Gamma' hfuture hGamma hwf
  exact (store hlookup hfuture hGamma hwf).monoDepth hle

/-- Turn a store for an exact creation prefix into the selected source
service used by one structural basis layer.  Selection comes from the prefix
link, while arbitrary root lookups are used only for validity. -/
private theorem selectedFamily_of_prefixStore
    {Delta : LCtx} {Gamma GammaRoot GammaTarget : NLCtx}
    {Psi0 root Psi : EvalCtx} {baseDepth : Nat}
    (hlink : V2.TypingImplyEval Delta Gamma Psi0)
    (store : CheckedFreeStdPrefixStoreAt Psi0 root GammaRoot baseDepth)
    (hsub : Psi0.Subctx root)
    (hfuture : CheckedFreshFuture root Psi)
    (hGamma : NLCtxIncl GammaRoot GammaTarget)
    (rootValid : forall {x : VName} {b : Basis}, (x, b) ∈ root ->
      Basis.BasisValid GammaRoot b) :
    CheckedRelaxedControlledSelectedFamily Psi (∅ : NLCtx) baseDepth
      Delta Gamma GammaTarget := by
  intro depth hle
  have store' : CheckedFreeStdPrefixStoreAt Psi0 root GammaRoot depth :=
    CheckedFreeStdPrefixStoreAt.monoDepth store hle
  refine { lin := ?_, nlin := ?_ }
  · intro x s hlookupDelta
    have hxDelta : x ∈ Delta := Finmap.mem_of_lookup_eq_some hlookupDelta
    obtain ⟨b, hmem⟩ := (hlink.1 x).mp (Or.inl hxDelta)
    obtain ⟨v, hlookupPrefix⟩ := Finmap.mem_iff.mp hmem
    have htof : Basis.tof b = .space s :=
      hlink.2.1 x s b hlookupDelta hmem
    have hlookupRoot : EvalCtx.lookup root (x, b) = some v :=
      hsub (x, b) v hlookupPrefix
    have hxRoot : x ∈ root.names := EvalCtx.mem_names_of_lookup hlookupRoot
    have hlookupPsi : EvalCtx.lookup Psi (x, b) = some v :=
      hfuture.subctx (x, b) v hlookupRoot
    refine ⟨.paired (EvalCtx.mem_names_of_lookup hlookupPsi)
      ⟨b, v, hlookupPsi, htof, {
        valid := raw_basisValid_mono
          (rootValid (Finmap.mem_of_lookup_eq_some hlookupRoot)) hGamma
        quad := ?_ }
      ⟩ ?_⟩
    · intro Psi' Gamma' hhybrid hGamma' hwf
      exact store' hlookupPrefix (hfuture.trans hhybrid.fresh)
        (hGamma.trans hGamma') hwf
    · intro b' v' hlookup' _htof
      have hlookupRoot' :=
        hfuture.lookup_root_of_root_name hxRoot hlookup'
      exact raw_basisValid_mono
        (rootValid (Finmap.mem_of_lookup_eq_some hlookupRoot')) hGamma
  · intro x tau hlookupGamma
    have hxGamma : x ∈ Gamma := Finmap.mem_of_lookup_eq_some hlookupGamma
    obtain ⟨b, hmem⟩ := (hlink.1 x).mp (Or.inr hxGamma)
    obtain ⟨v, hlookupPrefix⟩ := Finmap.mem_iff.mp hmem
    have htof : Basis.tof b = tau :=
      hlink.2.2.1 x tau b hlookupGamma hmem
    have hlookupRoot : EvalCtx.lookup root (x, b) = some v :=
      hsub (x, b) v hlookupPrefix
    have hxRoot : x ∈ root.names := EvalCtx.mem_names_of_lookup hlookupRoot
    have hlookupPsi : EvalCtx.lookup Psi (x, b) = some v :=
      hfuture.subctx (x, b) v hlookupRoot
    refine ⟨.paired (EvalCtx.mem_names_of_lookup hlookupPsi)
      ⟨b, v, hlookupPsi, htof, {
        valid := raw_basisValid_mono
          (rootValid (Finmap.mem_of_lookup_eq_some hlookupRoot)) hGamma
        quad := ?_ }
      ⟩ ?_⟩
    · intro Psi' Gamma' hhybrid hGamma' hwf
      exact store' hlookupPrefix (hfuture.trans hhybrid.fresh)
        (hGamma.trans hGamma') hwf
    · intro b' v' hlookup' _htof
      have hlookupRoot' :=
        hfuture.lookup_root_of_root_name hxRoot hlookup'
      exact raw_basisValid_mono
        (rootValid (Finmap.mem_of_lookup_eq_some hlookupRoot')) hGamma

/-- Build certificates for a creation prefix directly at a fixed final root. -/
private theorem checkedFreeStdPrefixStoreAtFinal : forall
    {Delta : LCtx} {Gamma : NLCtx} {Psi0 : EvalCtx},
    (htele : V2.CtxTele Delta Gamma Psi0) ->
    forall {root : EvalCtx} {GammaRoot : NLCtx},
      Psi0.Subctx root -> NLCtxIncl Gamma GammaRoot ->
      V2.CtxWF' (∅ : LCtx) GammaRoot ->
      (forall {x : VName} {b : Basis}, (x, b) ∈ root ->
        Basis.BasisValid GammaRoot b) ->
      exists depth, CheckedFreeStdPrefixStoreAt
        Psi0 root GammaRoot depth := by
  intro Delta Gamma Psi0 htele
  induction htele with
  | empty =>
      intro root GammaRoot hsub hGamma hwf rootValid
      refine ⟨0, ?_⟩
      intro x b v hlookup
      exact absurd (Finmap.mem_of_lookup_eq_some hlookup)
        Finmap.notMem_empty
  | @extend_nlin Delta Gamma Psi0 x b v htele hsource hcreation hb ih =>
      intro root GammaRoot hsub hGammaRoot hwfRoot rootValid
      have hstep : Psi0.Subctx (Psi0.extend x b v) :=
        EvalCtx.Subctx.extend_right_of_key_fresh
          (htele.freshEvalName hsource b) v
      have hsubPrefix : Psi0.Subctx root := hstep.trans hsub
      have hGammaStep : NLCtxIncl Gamma
          (Finmap.insert x (Basis.tof b) Gamma) :=
        (NLCtxIncl.refl Gamma).insert_right hsource.freshNonlinear _
      have hGammaPrefix : NLCtxIncl Gamma GammaRoot :=
        hGammaStep.trans hGammaRoot
      obtain ⟨baseDepth, prefixStore⟩ :=
        ih hsubPrefix hGammaPrefix hwfRoot rootValid
      let outDepth := baseDepth + basisHeight b
      have hnew : CheckedFreeStdFreshDepthQuadAt
          root GammaRoot outDepth b := by
        intro Psi' Gamma' hfuture hGamma' hwf'
        let familyAll := selectedFamily_of_prefixStore
          (typingImplyEval htele) prefixStore hsubPrefix hfuture hGamma'
          rootValid
        let family := familyAll.restrictLinearEmpty
        exact checkedFreeStdPairDepthQuad_of_family family
          (hGammaPrefix.trans hGamma') hwf' hb le_rfl
      refine ⟨outDepth, ?_⟩
      intro z bZ vZ hlookup
      by_cases hkey : (z, bZ) = (x, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
        exact hnew
      · have hlookup0 : EvalCtx.lookup Psi0 (z, bZ) = some vZ := by
          simpa only [EvalCtx.lookup, EvalCtx.extend,
            Finmap.lookup_insert_of_ne _ hkey] using hlookup
        exact prefixStore.monoDepth
          (Nat.le_add_right baseDepth (basisHeight b)) hlookup0
  | @extend_lin Delta Gamma Psi0 x b v s htele hsource hcreation hb htof ih =>
      intro root GammaRoot hsub hGammaRoot hwfRoot rootValid
      have hstep : Psi0.Subctx (Psi0.extend x b v) :=
        EvalCtx.Subctx.extend_right_of_key_fresh
          (htele.freshEvalName hsource b) v
      have hsubPrefix : Psi0.Subctx root := hstep.trans hsub
      obtain ⟨baseDepth, prefixStore⟩ :=
        ih hsubPrefix hGammaRoot hwfRoot rootValid
      let outDepth := baseDepth + basisHeight b
      have hnew : CheckedFreeStdFreshDepthQuadAt
          root GammaRoot outDepth b := by
        intro Psi' Gamma' hfuture hGamma' hwf'
        let familyAll := selectedFamily_of_prefixStore
          (typingImplyEval htele) prefixStore hsubPrefix hfuture hGamma'
          rootValid
        let family := familyAll.restrictLinearEmpty
        exact checkedFreeStdPairDepthQuad_of_family family
          (hGammaRoot.trans hGamma') hwf' hb le_rfl
      refine ⟨outDepth, ?_⟩
      intro z bZ vZ hlookup
      by_cases hkey : (z, bZ) = (x, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
        exact hnew
      · have hlookup0 : EvalCtx.lookup Psi0 (z, bZ) = some vZ := by
          simpa only [EvalCtx.lookup, EvalCtx.extend,
            Finmap.lookup_insert_of_ne _ hkey] using hlookup
        exact prefixStore.monoDepth
          (Nat.le_add_right baseDepth (basisHeight b)) hlookup0
  | @extend_rep Delta Gamma Psi0 x b v htele hsource hpair hcreation hb ih =>
      intro root GammaRoot hsub hGammaRoot hwfRoot rootValid
      have hstep : Psi0.Subctx (Psi0.extend x b v) :=
        EvalCtx.Subctx.extend_right_of_key_fresh hpair v
      have hsubPrefix : Psi0.Subctx root := hstep.trans hsub
      obtain ⟨baseDepth, prefixStore⟩ :=
        ih hsubPrefix hGammaRoot hwfRoot rootValid
      let outDepth := baseDepth + basisHeight b
      have hnew : CheckedFreeStdFreshDepthQuadAt
          root GammaRoot outDepth b := by
        intro Psi' Gamma' hfuture hGamma' hwf'
        let familyAll := selectedFamily_of_prefixStore
          (typingImplyEval htele) prefixStore hsubPrefix hfuture hGamma'
          rootValid
        let family := familyAll.restrictLinearEmpty
        exact checkedFreeStdPairDepthQuad_of_family family
          (hGammaRoot.trans hGamma') hwf' hb le_rfl
      refine ⟨outDepth, ?_⟩
      intro z bZ vZ hlookup
      by_cases hkey : (z, bZ) = (x, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
        exact hnew
      · have hlookup0 : EvalCtx.lookup Psi0 (z, bZ) = some vZ := by
          simpa only [EvalCtx.lookup, EvalCtx.extend,
            Finmap.lookup_insert_of_ne _ hkey] using hlookup
        exact prefixStore.monoDepth
          (Nat.le_add_right baseDepth (basisHeight b)) hlookup0

theorem checkedFreeStdFreshDepthQuadSelectedStore
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi) :
    CheckedFreeStdFreshDepthQuadSelectedStore Psi Gamma := by
  obtain ⟨depth, store⟩ := checkedFreeStdPrefixStoreAtFinal htele
    (EvalCtx.Subctx.refl Psi) (NLCtxIncl.refl Gamma)
    (RawCertifiedWorldBinderProgress.ctxWF_dropLin (ctxWFPrime htele))
    (fun {x b} hmem => (typingImplyEval htele).2.2.2 x b hmem)
  intro x b v hlookup
  exact ⟨depth, store hlookup⟩

private theorem prefixExact
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi)
    (anchors : CheckedExactLookupStore Gamma Psi)
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
  obtain ⟨kind, ⟨hty⟩⟩ := hb.tof_tvalid
  have hstd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
    Basis.std_valid _ hty
  exact services.targetExact Psi htele.storedWF Gamma Psi
    (Basis.std (Basis.tof b)) b quad.fromStd hstd hb
    (CheckedStdFuture.refl Psi) anchors
    (htele.pCarrier V2.pi_entry_transport) htele.varsCovered.drop_lin
    htele.storedWF Delta (ctxWFPrime htele)
    (Basis.isTyBasis_std _) hb.isTyBasis (Basis.tof_std _).symm

theorem checkedExactLookupStore : forall
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx},
    V2.CtxTele Delta Gamma Psi -> CheckedExactLookupStore Gamma Psi := by
  intro Delta Gamma Psi htele
  induction htele with
  | empty =>
      intro x b v hlookup
      exact absurd (Finmap.mem_of_lookup_eq_some hlookup)
        Finmap.notMem_empty
  | @extend_nlin Delta Gamma Psi x b v htele hsource hcreation hb ih =>
      obtain ⟨tauV, hnew⟩ := prefixExact htele ih hb
      have hkey : (x, b) ∉ Psi := htele.freshEvalName hsource b
      have extended : CheckedExactLookupStore Gamma (Psi.extend x b v) :=
        ih.extendValue hkey hnew
      intro z bZ vZ hlookup
      exact CheckedExactLookupStore.nlMono extended
        ((NLCtxIncl.refl Gamma).insert_right hsource.freshNonlinear
          (Basis.tof b)) hlookup
  | @extend_lin Delta Gamma Psi x b v s htele hsource hcreation hb htof ih =>
      obtain ⟨tauV, hnew⟩ := prefixExact htele ih hb
      have hkey : (x, b) ∉ Psi := htele.freshEvalName hsource b
      intro z bZ vZ hlookup
      exact ih.extendValue hkey hnew hlookup
  | @extend_rep Delta Gamma Psi x b v htele hsource hkey hcreation hb ih =>
      obtain ⟨tauV, hnew⟩ := prefixExact htele ih hb
      exact ih.extendValue hkey hnew

theorem checkedRootBasisBoundary
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi)
    {requested : Basis}
    (hrequested : Basis.BasisValid Gamma requested) :
    CheckedRootBasisBoundary Gamma Psi requested := by
  obtain ⟨storeDepth, store⟩ :=
    CheckedFreeStdFreshDepthQuadSelectedStore.exists_atDepth
      (checkedFreeStdFreshDepthQuadSelectedStore htele)
  have package : CheckedFreeStdFreshDepthQuadFinite Psi Gamma requested :=
    checkedFreeStdCreationPrefixLayerBuilder (ctxWFPrime htele)
      (typingImplyEval htele) ⟨storeDepth, store⟩ hrequested
  obtain ⟨depth, quad⟩ := package.toRoot
    (RawCertifiedWorldBinderProgress.ctxWF_dropLin (ctxWFPrime htele))
  let services := checkedFreeStdDepthServices_all
    RawCertifiedOperational.RenameProof.checkedRenameLaws
    RawCertifiedOperational.checkedTyAtAppCut depth
  obtain ⟨kind, ⟨hty⟩⟩ := hrequested.tof_tvalid
  have hstd : Basis.BasisValid Gamma
      (Basis.std (Basis.tof requested)) := Basis.std_valid _ hty
  refine ⟨hrequested, ?_⟩
  intro Delta' e v tauV hwf hterm
  exact services.transport Psi htele.storedWF Delta' Gamma Psi e
    (Basis.std (Basis.tof requested)) requested v tauV
    quad.fromStd hstd hrequested (CheckedStdFuture.refl Psi)
    (checkedExactLookupStore htele)
    (htele.pCarrier V2.pi_entry_transport) htele.varsCovered.drop_lin
    htele.storedWF hwf (Basis.isTyBasis_std _)
    hrequested.isTyBasis (Basis.tof_std _).symm hterm

private theorem checkedFreeStdJudgmentTermSideFinite
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi)
    {e : Term} {tau : Ty} (ht : HasType Delta Gamma e tau) :
    CheckedFreeStdJudgmentTermSideFinite Psi ht := by
  obtain ⟨depth, store⟩ :=
    CheckedFreeStdFreshDepthQuadSelectedStore.exists_atDepth
      (checkedFreeStdFreshDepthQuadSelectedStore htele)
  let normalized := normalizedTypingAvoidingFreeHygienic Psi.names
    (ctxWFPrime htele).disjoint ht
  let selected := CheckedRelaxedControlledContextSelectedAt.of_storeAtFresh
    (typingImplyEval htele) store (CheckedFreshFuture.refl Psi)
      (NLCtxIncl.refl Gamma)
  let result := RawCertifiedPairControlledSourceFreeStandard.ofH
    normalized.typing selected (NLCtxIncl.refl Gamma)
      (ctxWFPrime htele) normalized.promotionFree
      normalized.binderHygiene
  exact ⟨result.target, result.promotionFree, depth, ⟨result.side⟩⟩

theorem checkedProgressStandard
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi)
    {e : Term} {tau : Ty} (ht : HasType Delta Gamma e tau) :
    exists v tauV, C.Term Delta Gamma Psi e (Basis.std tau) v tauV := by
  obtain ⟨ht', hfree, depth, ⟨side⟩⟩ :=
    checkedFreeStdJudgmentTermSideFinite htele ht
  let services := checkedFreeStdDepthServices_all
    RawCertifiedOperational.RenameProof.checkedRenameLaws
    RawCertifiedOperational.checkedTyAtAppCut depth
  exact services.termProgress Psi htele.storedWF ht' hfree side
    (CheckedStdFuture.refl Psi) (htele.pCarrier V2.pi_entry_transport)
    htele.varsCovered htele.storedWF (ctxWFPrime htele)
    (checkedExactLookupStore htele)

theorem checkedProgress
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (htele : V2.CtxTele Delta Gamma Psi)
    {e : Term} {requested : Basis}
    (ht : HasType Delta Gamma e (Basis.tof requested))
    (hrequested : Basis.BasisValid Gamma requested) :
    exists v tauV, C.Term Delta Gamma Psi e requested v tauV := by
  obtain ⟨v, tauV, hstd⟩ := checkedProgressStandard htele ht
  exact (checkedRootBasisBoundary htele hrequested).reanchor
    (ctxWFPrime htele) hstd

end RawCertifiedCtxTeleProgress
end GLang
