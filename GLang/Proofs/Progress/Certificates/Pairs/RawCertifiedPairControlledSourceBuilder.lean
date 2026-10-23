import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairContextSelected
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairHybridFuture
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedContextMono
import GLang.Proofs.Progress.ContextExtension
import GLang.Proofs.Progress.Certificates.RawCertifiedWorldProgressArms

namespace GLang
namespace RawCertifiedPairControlledSourceBuilder

open OperationalStrengthening
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate
open RawCertifiedConsistentPairStore
open RawCertifiedPairStoreUniformization
open RawCertifiedPairContextStandardSelf
open RawCertifiedPairContextSelected
open RawCertifiedPairHybridFuture
open RawCertifiedOperational

/-- Every target binding is either ambient (already present before the
controlled traversal) or belongs to the controlled source context.  This
invariant survives lockstep nonlinear binder insertion. -/
def TargetKeysCovered (A : Finset Name)
    (GammaCtrl GammaTarget : NLCtx) : Prop :=
  forall x, x ∈ GammaTarget -> x ∈ A \/ x ∈ GammaCtrl

theorem TargetKeysCovered.insertSame
    {A : Finset Name} {GammaCtrl GammaTarget : NLCtx}
    (h : TargetKeysCovered A GammaCtrl GammaTarget)
    (y : Name) (tau : Ty) :
    TargetKeysCovered A (Finmap.insert y tau GammaCtrl)
      (Finmap.insert y tau GammaTarget) := by
  intro x hx
  rcases Finmap.mem_insert.mp hx with rfl | hx
  · exact Or.inr (Finmap.mem_insert.mpr (Or.inl rfl))
  · rcases h x hx with hxA | hxCtrl
    · exact Or.inl hxA
    · exact Or.inr (Finmap.mem_insert.mpr (Or.inr hxCtrl))

private theorem not_mem_context_of_keys_subset
    {Gamma : NLCtx} {L : Finset Name} {y : Name}
    (hkeys : Gamma.keys ⊆ L) (hy : y ∉ L) : y ∉ Gamma := by
  intro hyGamma
  exact hy (hkeys (Finmap.mem_keys.mpr hyGamma))

private theorem not_mem_lctx_of_keys_subset
    {Delta : LCtx} {L : Finset Name} {y : Name}
    (hkeys : Delta.keys ⊆ L) (hy : y ∉ L) : y ∉ Delta := by
  intro hyDelta
  exact hy (hkeys (Finmap.mem_keys.mpr hyDelta))

private theorem not_mem_target_of_covered
    {A L : Finset Name} {GammaCtrl GammaTarget : NLCtx} {y : Name}
    (hcover : TargetKeysCovered A GammaCtrl GammaTarget)
    (hA : A ⊆ L) (hCtrl : GammaCtrl.keys ⊆ L) (hy : y ∉ L) :
    y ∉ GammaTarget := by
  intro hyTarget
  rcases hcover y hyTarget with hyA | hyCtrl
  · exact hy (hA hyA)
  · exact hy (hCtrl (Finmap.mem_keys.mpr hyCtrl))

private theorem not_mem_eval_of_ambient
    {A L : Finset Name} {Psi : EvalCtx} {y : Name}
    (hPsi : Psi.names ⊆ A) (hA : A ⊆ L) (hy : y ∉ L) :
    y ∉ Psi.names :=
  fun hyPsi => hy (hA (hPsi hyPsi))

private def tvalid_pi_domain
    {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind}
    (h : TValid Gamma (.piTy tau0 tau1) (.arrow k0 k1)) :
    TValid Gamma tau0 k0 := by
  cases h with
  | piTy _ ht0 _ => exact ht0

/-! ## Hybrid controlled-context service

Ordinary source binders reserve a name without immediately installing an
evaluator key.  Literal frame binders instead install a possibly nonstandard
key.  The strong `CheckedControlledContextSelectedAt` service cannot express
that mixture: its packages must survive *arbitrary* fresh growth, including
an inadmissible nonstandard key at an ordinary source-binder name.

The parallel service below uses `CheckedHybridFuture`.  Each entry records
why its source name is selectable: it is either already owned by the current
evaluator root or it is one of the standard-only reserved slots.  This small
ownership fact is exactly what makes arbitrary later frame extensions safe.
-/

/-- One controlled source binding, stable under hybrid evaluator growth. -/
structure CheckedHybridContextSelectedEntryAt
    (Psi : EvalCtx) (GammaTarget reserved : NLCtx) (depth : Nat)
    (x : VName) (tau : Ty) : Prop where
  owned : x ∈ Psi.names \/ reserved.lookup x = some tau
  root : forall {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi (x, b) = some v -> Basis.tof b = tau ->
      CheckedHybridSelectedAt Psi GammaTarget reserved depth b
  standard : CheckedHybridSelectedAt Psi GammaTarget reserved depth
    (Basis.std tau)

/-- Selected-pair evidence for the controlled source contexts, with all
pairs already formed in `GammaTarget` and stable under `reserved`. -/
structure CheckedHybridControlledContextSelectedAt
    (Psi : EvalCtx) (reserved : NLCtx) (depth : Nat)
    (DeltaCtrl : LCtx) (GammaCtrl GammaTarget : NLCtx) : Prop where
  lin : forall {x : VName} {s : Space},
    DeltaCtrl.lookup x = some s ->
      CheckedHybridContextSelectedEntryAt Psi GammaTarget reserved depth
        x (.space s)
  nlin : forall {x : VName} {tau : Ty},
    GammaCtrl.lookup x = some tau ->
      CheckedHybridContextSelectedEntryAt Psi GammaTarget reserved depth
        x tau

/-- Raise one hybrid entry to a common larger pair depth. -/
theorem CheckedHybridContextSelectedEntryAt.monoDepth
    {Psi : EvalCtx} {GammaTarget reserved : NLCtx}
    {depth depth' : Nat} {x : VName} {tau : Ty}
    (hle : depth <= depth')
    (entry : CheckedHybridContextSelectedEntryAt Psi GammaTarget reserved
      depth x tau) :
    CheckedHybridContextSelectedEntryAt Psi GammaTarget reserved
      depth' x tau where
  owned := entry.owned
  root hlookup htof := (entry.root hlookup htof).monoDepth hle
  standard := entry.standard.monoDepth hle

/-- Raise every entry of a hybrid controlled-context service. -/
theorem CheckedHybridControlledContextSelectedAt.monoDepth
    {Psi : EvalCtx} {reserved : NLCtx} {depth depth' : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (hle : depth <= depth')
    (self : CheckedHybridControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget) :
    CheckedHybridControlledContextSelectedAt Psi reserved depth'
      DeltaCtrl GammaCtrl GammaTarget where
  lin hlookup := (self.lin hlookup).monoDepth hle
  nlin hlookup := (self.nlin hlookup).monoDepth hle

/-- Rebuild an entry in a larger nonlinear target context. -/
theorem CheckedHybridContextSelectedEntryAt.rebaseContext
    {Psi : EvalCtx} {GammaTarget GammaTarget' reserved : NLCtx}
    {depth : Nat} {x : VName} {tau : Ty}
    (entry : CheckedHybridContextSelectedEntryAt Psi GammaTarget reserved
      depth x tau)
    (hGamma : NLCtxIncl GammaTarget GammaTarget') :
    CheckedHybridContextSelectedEntryAt Psi GammaTarget' reserved
      depth x tau where
  owned := entry.owned
  root hlookup htof :=
    (entry.root hlookup htof).rebase
      (CheckedHybridFuture.refl Psi reserved) hGamma
  standard := entry.standard.rebase
    (CheckedHybridFuture.refl Psi reserved) hGamma

/-- Strengthen the standard-only reservation policy of one entry. -/
theorem CheckedHybridContextSelectedEntryAt.strengthenReserved
    {Psi : EvalCtx} {GammaTarget reserved reserved' : NLCtx}
    {depth : Nat} {x : VName} {tau : Ty}
    (hReserved : NLCtxIncl reserved reserved')
    (entry : CheckedHybridContextSelectedEntryAt Psi GammaTarget reserved
      depth x tau) :
    CheckedHybridContextSelectedEntryAt Psi GammaTarget reserved'
      depth x tau where
  owned := entry.owned.elim Or.inl (fun hlookup =>
    Or.inr (hReserved _ _ hlookup))
  root hlookup htof :=
    (entry.root hlookup htof).strengthenReserved hReserved
  standard := entry.standard.strengthenReserved hReserved

/-- Re-root an entry through admissible hybrid growth and move its target
context at the same time.  A future-only lookup at a reserved source name is
forced to the recorded standard basis. -/
theorem CheckedHybridContextSelectedEntryAt.rebase
    {Psi Psi' : EvalCtx} {GammaTarget GammaTarget' reserved : NLCtx}
    {depth : Nat} {x : VName} {tau : Ty}
    (entry : CheckedHybridContextSelectedEntryAt Psi GammaTarget reserved
      depth x tau)
    (hfuture : CheckedHybridFuture Psi Psi' reserved)
    (hGamma : NLCtxIncl GammaTarget GammaTarget') :
    CheckedHybridContextSelectedEntryAt Psi' GammaTarget' reserved
      depth x tau where
  owned := by
    rcases entry.owned with hxRoot | hxReserved
    · exact Or.inl (EvalCtx.Subctx.names_subset hfuture.fresh.subctx hxRoot)
    · exact Or.inr hxReserved
  root := by
    intro b v hlookup htof
    by_cases hxRoot : x ∈ Psi.names
    · have hlookup0 := hfuture.fresh.lookup_root_of_root_name hxRoot hlookup
      exact (entry.root hlookup0 htof).rebase hfuture hGamma
    · rcases entry.owned with hxOwned | hxReserved
      · exact False.elim (hxRoot hxOwned)
      · have hstd : b = Basis.std tau :=
          hfuture.reserved_standard hxReserved hxRoot hlookup htof
        subst b
        exact entry.standard.rebase hfuture hGamma
  standard := entry.standard.rebase hfuture hGamma

/-- Restrict only the controlled linear source context. -/
theorem CheckedHybridControlledContextSelectedAt.restrictLinear
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaSmall DeltaBig : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedHybridControlledContextSelectedAt Psi reserved depth
      DeltaBig GammaCtrl GammaTarget)
    (hDelta : LinearCtxIncl DeltaSmall DeltaBig) :
    CheckedHybridControlledContextSelectedAt Psi reserved depth
      DeltaSmall GammaCtrl GammaTarget where
  lin hlookup := self.lin (hDelta _ _ hlookup)
  nlin hlookup := self.nlin hlookup

/-- Move only the target nonlinear context. -/
theorem CheckedHybridControlledContextSelectedAt.rebaseTarget
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget GammaTarget' : NLCtx}
    (self : CheckedHybridControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget)
    (hGamma : NLCtxIncl GammaTarget GammaTarget') :
    CheckedHybridControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget' where
  lin hlookup := (self.lin hlookup).rebaseContext hGamma
  nlin hlookup := (self.nlin hlookup).rebaseContext hGamma

/-- Re-root the service through admissible hybrid evaluator growth. -/
theorem CheckedHybridControlledContextSelectedAt.rebase
    {Psi Psi' : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget GammaTarget' : NLCtx}
    (self : CheckedHybridControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget)
    (hfuture : CheckedHybridFuture Psi Psi' reserved)
    (hGamma : NLCtxIncl GammaTarget GammaTarget') :
    CheckedHybridControlledContextSelectedAt Psi' reserved depth
      DeltaCtrl GammaCtrl GammaTarget' where
  lin hlookup := (self.lin hlookup).rebase hfuture hGamma
  nlin hlookup := (self.nlin hlookup).rebase hfuture hGamma

/-- Initialize the hybrid service with no reserved source slots.  The
creation-prefix linkage proves that every controlled key is already owned by
the (possibly freshly extended) evaluator root. -/
theorem CheckedHybridControlledContextSelectedAt.of_storeAtFresh
    {Psi0 Psi : EvalCtx} {depth : Nat} {DeltaCtrl : LCtx}
    {GammaCtrl GammaTarget : NLCtx}
    (hlink : V2.TypingImplyEval DeltaCtrl GammaCtrl Psi0)
    (store : CheckedPairFreshDepthQuadSelectedStoreAt Psi0 GammaCtrl depth)
    (hfuture : CheckedFreshFuture Psi0 Psi)
    (hGamma : NLCtxIncl GammaCtrl GammaTarget) :
    CheckedHybridControlledContextSelectedAt Psi (∅ : NLCtx) depth
      DeltaCtrl GammaCtrl GammaTarget := by
  let strong := CheckedControlledContextSelectedAt.of_storeAtFresh
    hlink store hfuture hGamma
  refine {
    lin := ?_
    nlin := ?_ }
  · intro x s hlookup
    have hxCtrl : x ∈ DeltaCtrl := Finmap.mem_of_lookup_eq_some hlookup
    have hx0 : x ∈ Psi0.names := by
      obtain ⟨b, hmem⟩ := (hlink.1 x).mp (Or.inl hxCtrl)
      exact EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hmem⟩
    have hx : x ∈ Psi.names :=
      EvalCtx.Subctx.names_subset hfuture.subctx hx0
    let entry := strong.lin hlookup
    exact {
      owned := Or.inl hx
      root := fun hlookup htof =>
        RawCertifiedPairHybridFuture.CheckedFreshSelectedAt.toHybrid
          (entry.root hlookup htof)
      standard :=
        RawCertifiedPairHybridFuture.CheckedFreshSelectedAt.toHybrid
          entry.standard }
  · intro x tau hlookup
    have hxCtrl : x ∈ GammaCtrl := Finmap.mem_of_lookup_eq_some hlookup
    have hx0 : x ∈ Psi0.names := by
      obtain ⟨b, hmem⟩ := (hlink.1 x).mp (Or.inr hxCtrl)
      exact EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hmem⟩
    have hx : x ∈ Psi.names :=
      EvalCtx.Subctx.names_subset hfuture.subctx hx0
    let entry := strong.nlin hlookup
    exact {
      owned := Or.inl hx
      root := fun hlookup htof =>
        RawCertifiedPairHybridFuture.CheckedFreshSelectedAt.toHybrid
          (entry.root hlookup htof)
      standard :=
        RawCertifiedPairHybridFuture.CheckedFreshSelectedAt.toHybrid
          entry.standard }

/-- Reserve one fresh ordinary linear source binder.  The evaluator is not
changed; the binder can subsequently appear only at its standard basis. -/
theorem CheckedHybridControlledContextSelectedAt.insertLinearReserved
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedHybridControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget)
    {y : VName} {s : Space}
    (hyPsi : y ∉ Psi.names) (hyReserved : y ∉ reserved)
    (_hyDelta : y ∉ DeltaCtrl)
    (domain : CheckedHybridSelectedAt Psi GammaTarget reserved depth
      (Basis.stdSpace s)) :
    CheckedHybridControlledContextSelectedAt Psi
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
      exact {
        owned := Or.inr (by simp only [Finmap.lookup_insert])
        root := by
          intro b v hlookupRoot htof
          exact False.elim
            (hyPsi (EvalCtx.mem_names_of_lookup hlookupRoot))
        standard := by
          simpa only [Basis.std] using
            domain.strengthenReserved hReserved }
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact (self.lin hlookup).strengthenReserved hReserved
  · intro x tau hlookup
    exact (self.nlin hlookup).strengthenReserved hReserved

/-- Reserve one fresh ordinary nonlinear source binder and insert its type in
the controlled and target nonlinear contexts in lockstep. -/
theorem CheckedHybridControlledContextSelectedAt.insertNonlinearReserved
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedHybridControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget)
    {y : VName} {tau : Ty}
    (hyPsi : y ∉ Psi.names) (hyReserved : y ∉ reserved)
    (_hyCtrl : y ∉ GammaCtrl) (hyTarget : y ∉ GammaTarget)
    (domain : CheckedHybridSelectedAt Psi GammaTarget reserved depth
      (Basis.std tau)) :
    CheckedHybridControlledContextSelectedAt Psi
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
      exact {
        owned := Or.inr (by simp only [Finmap.lookup_insert])
        root := by
          intro b v hlookupRoot htof
          exact False.elim
            (hyPsi (EvalCtx.mem_names_of_lookup hlookupRoot))
        standard :=
          (domain.rebase (CheckedHybridFuture.refl Psi reserved) hTarget).strengthenReserved
            hReserved }
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact ((self.nlin hlookup).rebaseContext hTarget).strengthenReserved
        hReserved

/-- Install one literal, possibly nonstandard frame endpoint. -/
theorem CheckedHybridControlledContextSelectedAt.extendFrameNonlinear
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (self : CheckedHybridControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget)
    {y : VName} {tau : Ty} {bArg : Basis} {v : ValExpr}
    (hyPsi : y ∉ Psi.names) (hyReserved : y ∉ reserved)
    (_hyDelta : y ∉ DeltaCtrl) (_hyCtrl : y ∉ GammaCtrl)
    (hyTarget : y ∉ GammaTarget)
    (htof : Basis.tof bArg = tau)
    (domain : CheckedFreshSelectedAt Psi GammaTarget depth bArg) :
    CheckedHybridControlledContextSelectedAt (Psi.extend y bArg v)
      reserved depth DeltaCtrl (Finmap.insert y tau GammaCtrl)
      (Finmap.insert y tau GammaTarget) := by
  let Psi' := Psi.extend y bArg v
  let target' := Finmap.insert y tau GammaTarget
  let hfuture : CheckedHybridFuture Psi Psi' reserved :=
    (CheckedHybridFuture.refl Psi reserved).extend
      hyPsi hyReserved bArg v
  let hTarget : NLCtxIncl GammaTarget target' :=
    (NLCtxIncl.refl GammaTarget).insert_right hyTarget tau
  let domainHybrid : CheckedHybridSelectedAt Psi GammaTarget reserved
      depth bArg :=
    RawCertifiedPairHybridFuture.CheckedFreshSelectedAt.toHybrid domain
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
      refine {
        owned := Or.inl ?_
        root := ?_
        standard := ?_ }
      · apply EvalCtx.mem_names_of_lookup (b := bArg) (v := v)
        simp only [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert]
      · intro b vX hlookupX htofX
        have hb : b = bArg := by
          apply hfuture.fresh.extra_name_unique y b bArg
          · exact Finmap.mem_of_lookup_eq_some hlookupX
          · intro hmem
            exact hyPsi (EvalCtx.mem_keyNames_iff_exists_basis.mpr
              ⟨b, hmem⟩)
          · exact Finmap.mem_insert.mpr (Or.inl rfl)
        subst b
        exact domainHybrid.rebase hfuture hTarget
      · simpa only [htof] using
          domainHybrid.toStandard.rebase hfuture hTarget
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hlookup
      exact (self.nlin hlookup).rebase hfuture hTarget

/-! ## Structural binder inputs

These predicates carry only the recursive basis evidence introduced by
source binders.  Their target-context index changes exactly when the
simultaneous source traversal inserts a nonlinear binder.
-/

mutual

def BinderInputsS (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {GammaCtrl : NLCtx} -> {s : Space} -> SValid GammaCtrl s -> Prop
  | _, _, .empty => True
  | _, _, .real => True
  | _, _, .dual hs => BinderInputsS Psi depth GammaTarget hs
  | _, _, .dsum hs0 hs1 =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1
  | _, _, .tprod hs0 hs1 =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1
  | _, _, .ker hs0 hs1 ht =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget ht
  | _, _, .coker hs0 hs1 ht =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget ht
  | _, _, .img hs0 hs1 ht =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget ht
  | _, _, .coimg hs0 hs1 ht =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget ht

def BinderInputsT (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {GammaCtrl : NLCtx} -> {tau : Ty} -> {k : Kind} ->
      TValid GammaCtrl tau k -> Prop
  | _, _, _, .space hs => BinderInputsS Psi depth GammaTarget hs
  | _, _, _, @TValid.piTy _ tau0 _ _ _ _ ht0 hbody =>
      BinderInputsT Psi depth GammaTarget ht0 /\
      CheckedFreshSelectedAt Psi GammaTarget depth (Basis.std tau0) /\
      forall y hy, BinderInputsT Psi depth
        (Finmap.insert y tau0 GammaTarget) (hbody y hy)

def BinderInputsSub (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {GammaCtrl : NLCtx} -> {s0 s1 : Space} ->
      SubType GammaCtrl s0 s1 -> Prop
  | _, _, _, .sub_ker hs0 hs1 ht =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget ht
  | _, _, _, .sub_coker hs0 hs1 ht =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget ht
  | _, _, _, .sub_img hs0 hs1 ht =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget ht
  | _, _, _, .sub_coimg hs0 hs1 ht =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget ht

def BinderInputsH (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    {Delta : LCtx} -> {GammaCtrl : NLCtx} -> {e : Term} -> {tau : Ty} ->
      HasType Delta GammaCtrl e tau -> Prop
  | _, _, _, _, .zero hs => BinderInputsS Psi depth GammaTarget hs
  | _, _, _, _, .smul hs _ h0 h1 =>
      BinderInputsS Psi depth GammaTarget hs /\
      BinderInputsH Psi depth GammaTarget h0 /\
      BinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .add hs h0 h1 =>
      BinderInputsS Psi depth GammaTarget hs /\
      BinderInputsH Psi depth GammaTarget h0 /\
      BinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .inner hs => BinderInputsS Psi depth GammaTarget hs
  | _, _, _, _, .real_lit _ => True
  | _, _, _, _, .app_linear hs0 hs1 _ h0 h1 =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget h0 /\
      BinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .app_inner hs _ h0 h1 =>
      BinderInputsS Psi depth GammaTarget hs /\
      BinderInputsH Psi depth GammaTarget h0 /\
      BinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .app_nonlinear h0 h1 =>
      BinderInputsH Psi depth GammaTarget h0 /\
      BinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .var_lin => True
  | _, _, _, _, .var_nlin _ => True
  | _, _, _, _, .pinv_tensor hs0 hs1 ht =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget ht
  | _, _, _, _, .pinv_dual hs ht =>
      BinderInputsS Psi depth GammaTarget hs /\
      BinderInputsH Psi depth GammaTarget ht
  | _, _, _, _, .promote _ _ _ _ ht =>
      BinderInputsH Psi depth GammaTarget ht
  | _, _, _, _, .dsumE hs0 hs1 h0 h1 =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget h0 /\
      BinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, .tprodE hs0 hs1 _ h0 h1 =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs1 /\
      BinderInputsH Psi depth GammaTarget h0 /\
      BinderInputsH Psi depth GammaTarget h1
  | _, _, _, _, @HasType.llam_real _ _ s _ _ hs hbody =>
      BinderInputsS Psi depth GammaTarget hs /\
      CheckedFreshSelectedAt Psi GammaTarget depth (Basis.stdSpace s) /\
      forall y hy, BinderInputsH Psi depth GammaTarget (hbody y hy)
  | _, _, _, _, @HasType.llam_tensor _ _ s0 _ _ _ _ hs0 hs hbody =>
      BinderInputsS Psi depth GammaTarget hs0 /\
      BinderInputsS Psi depth GammaTarget hs /\
      CheckedFreshSelectedAt Psi GammaTarget depth (Basis.stdSpace s0) /\
      forall y hy, BinderInputsH Psi depth GammaTarget (hbody y hy)
  | _, _, _, _, .embed hsub => BinderInputsSub Psi depth GammaTarget hsub
  | _, _, _, _, @HasType.nllam _ tau0 _ _ _ _ _ ht hbody =>
      BinderInputsT Psi depth GammaTarget ht /\
      CheckedFreshSelectedAt Psi GammaTarget depth (Basis.std tau0) /\
      forall y hy, BinderInputsH Psi depth
        (Finmap.insert y tau0 GammaTarget) (hbody y hy)

end

/-! ## Simultaneous target derivation and local-side results -/

structure ResultS (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx)
    {GammaCtrl : NLCtx} {s : Space} (_h : SValid GammaCtrl s) : Type where
  target : SValid GammaTarget s
  side : CheckedPairLocalSideS Psi depth target

structure ResultT (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx)
    {GammaCtrl : NLCtx} {tau : Ty} {k : Kind}
    (_h : TValid GammaCtrl tau k) : Type where
  target : TValid GammaTarget tau k
  side : CheckedPairLocalSideT Psi depth target

structure ResultSub (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx)
    {GammaCtrl : NLCtx} {s0 s1 : Space}
    (_h : SubType GammaCtrl s0 s1) : Type where
  target : SubType GammaTarget s0 s1
  side : CheckedPairLocalSideSub Psi depth target

structure ResultH (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx)
    {Delta : LCtx} {GammaCtrl : NLCtx} {e : Term} {tau : Ty}
    (_h : HasType Delta GammaCtrl e tau) : Type where
  target : HasType Delta GammaTarget e tau
  side : CheckedPairLocalSideBases Psi depth target

/-! ## Controlled variable seam -/

private theorem resolveEntryAtRoot
    {Psi : EvalCtx} {Gamma : NLCtx} {depth : Nat}
    {x : VName} {tau : Ty}
    (entry : CheckedContextSelectedEntryAt Psi Gamma depth x tau)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (Psi' : EvalCtx) (hfuture : CheckedStdFuture Psi Psi')
    (b : Basis) (v : ValExpr)
    (hlookup : EvalCtx.lookup Psi' (x, b) = some v)
    (htof : Basis.tof b = tau) :
    exists _hb : Basis.BasisValid Gamma b,
      CheckedPairBasisDepth Psi depth Gamma b
        (Basis.std (Basis.tof b)) := by
  rcases RawConsistentRank.CheckedStdFuture.lookup_root_or_standard
      hfuture hlookup with hroot | hextra
  · let p := entry.root hroot htof
    exact ⟨p.valid,
      (p.quad (CheckedFreshFuture.refl Psi)
        (NLCtxIncl.refl Gamma) hwf).toStd⟩
  · obtain ⟨_hnotRoot, hstd, _hfresh⟩ := hextra
    have p := entry.standard
    have hb : Basis.BasisValid Gamma b := by
      rw [hstd, htof]
      exact p.valid
    refine ⟨hb, ?_⟩
    have pair :=
      (p.quad (CheckedFreshFuture.refl Psi)
        (NLCtxIncl.refl Gamma) hwf).toStd
    exact Eq.mpr
      (congrArg
        (fun source => CheckedPairBasisDepth Psi depth Gamma source
          (Basis.std (Basis.tof b))) hstd)
      (by simpa only [htof, Basis.tof_std] using pair)

private theorem leafLinDeep
    {Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {Delta : LCtx} {depth : Nat} {x : VName} {s : Space}
    (selected : CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget)
    (hlookupCtrl : Delta.lookup x = some s)
    (hwf : V2.CtxWF' (Finmap.singleton x s) GammaTarget) :
    CheckedLocalTermSideBasisWith (CheckedPairSelectedAt Psi depth) Psi
      (HasType.var_lin :
        HasType (Finmap.singleton x s) GammaTarget (.var x) (.space s)) := by
  intro Psi' hfuture
  refine ⟨?_, ?_⟩
  · intro hcov
    obtain ⟨b, hmem, htof⟩ :=
      hcov.1 x s Finmap.lookup_singleton_eq
    obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp hmem
    obtain ⟨hb, hselected⟩ := resolveEntryAtRoot
      (selected.lin hlookupCtrl)
      (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
      Psi' hfuture b v hlookup htof
    exact ⟨b, v, hlookup, htof, hb, hselected⟩
  · intro b v hlookup htof
    exact (resolveEntryAtRoot (selected.lin hlookupCtrl)
      (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
      Psi' hfuture b v hlookup htof).choose

private theorem leafLinShallow
    {Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {Delta : LCtx} {depth : Nat} {x : VName} {s : Space}
    (selected : CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget)
    (hlookupCtrl : Delta.lookup x = some s)
    (hwf : V2.CtxWF' (Finmap.singleton x s) GammaTarget) :
    CheckedLocalTermSideBasis Psi
      (HasType.var_lin :
        HasType (Finmap.singleton x s) GammaTarget (.var x) (.space s)) := by
  intro b v hlookup htof
  exact (resolveEntryAtRoot (selected.lin hlookupCtrl)
    (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
    Psi (CheckedStdFuture.refl Psi) b v hlookup htof).choose

private theorem leafNlinDeep
    {Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {Delta : LCtx} {depth : Nat} {x : VName} {tau : Ty}
    (selected : CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget)
    (hlookupCtrl : GammaCtrl.lookup x = some tau)
    (hlookupTarget : GammaTarget.lookup x = some tau)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget) :
    CheckedLocalTermSideBasisWith (CheckedPairSelectedAt Psi depth) Psi
      (HasType.var_nlin hlookupTarget) := by
  intro Psi' hfuture
  refine ⟨?_, ?_⟩
  · intro hcov
    obtain ⟨b, hmem, htof⟩ := hcov.2 x tau hlookupTarget
    obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp hmem
    obtain ⟨hb, hselected⟩ := resolveEntryAtRoot
      (selected.nlin hlookupCtrl) hwf Psi' hfuture b v hlookup htof
    exact ⟨b, v, hlookup, htof, hb, hselected⟩
  · intro b v hlookup htof
    exact (resolveEntryAtRoot (selected.nlin hlookupCtrl) hwf
      Psi' hfuture b v hlookup htof).choose

private theorem leafNlinShallow
    {Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {Delta : LCtx} {depth : Nat} {x : VName} {tau : Ty}
    (selected : CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget)
    (hlookupCtrl : GammaCtrl.lookup x = some tau)
    (hlookupTarget : GammaTarget.lookup x = some tau)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget) :
    CheckedLocalTermSideBasis Psi (HasType.var_nlin hlookupTarget) := by
  intro b v hlookup htof
  exact (resolveEntryAtRoot (selected.nlin hlookupCtrl) hwf
    Psi (CheckedStdFuture.refl Psi) b v hlookup htof).choose

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

/-! ## Simultaneous structural traversal -/

mutual

/-- Replay a controlled space-validity derivation in the target context and
build its fixed-depth local-side tree in the same recursion. -/
noncomputable def ofS
    {Psi : EvalCtx} {depth : Nat} {A : Finset Name}
    {GammaCtrl GammaTarget : NLCtx} {s : Space}
    (h : SValid GammaCtrl s)
    (selected : CheckedControlledContextSelectedAt Psi depth (∅ : LCtx)
      GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hPsi : Psi.names ⊆ A)
    (hcover : TargetKeysCovered A GammaCtrl GammaTarget)
    (hinputs : BinderInputsS Psi depth GammaTarget h)
    (hfree : Graded.SPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.SBinderHygiene A h) :
    ResultS Psi depth GammaTarget h :=
  match h with
  | .empty =>
      let ht : SValid GammaTarget .empty := .empty
      ⟨ht, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, PUnit.unit⟩ ⟨True.intro, PUnit.unit⟩⟩
  | .real =>
      let ht : SValid GammaTarget .real := .real
      ⟨ht, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, PUnit.unit⟩ ⟨True.intro, PUnit.unit⟩⟩
  | .dual hs =>
      let r := ofS hs selected hinc hwf hPsi hcover hinputs hfree hhyg
      let ht : SValid GammaTarget (.dual _) := .dual r.target
      ⟨ht, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, r.side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, r.side.deep⟩⟩⟩
  | .dsum hs0 hs1 =>
      let r0 := ofS hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofS hs1 selected hinc hwf hPsi hcover hinputs.2
        hfree.2 hhyg.2
      let ht : SValid GammaTarget (.dsum _ _) := .dsum r0.target r1.target
      ⟨ht, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨True.intro, r1.side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨True.intro, r1.side.deep⟩⟩⟩⟩
  | .tprod hs0 hs1 =>
      let r0 := ofS hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofS hs1 selected hinc hwf hPsi hcover hinputs.2
        hfree.2 hhyg.2
      let ht : SValid GammaTarget (.tprod _ _) := .tprod r0.target r1.target
      ⟨ht, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨True.intro, r1.side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨True.intro, r1.side.deep⟩⟩⟩⟩
  | .ker hs0 hs1 he =>
      let r0 := ofS hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofS hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofH he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SValid GammaTarget (.ker _ _ _) :=
        .ker r0.target r1.target re.target
      ⟨ht, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .coker hs0 hs1 he =>
      let r0 := ofS hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofS hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofH he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SValid GammaTarget (.coker _ _ _) :=
        .coker r0.target r1.target re.target
      ⟨ht, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .img hs0 hs1 he =>
      let r0 := ofS hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofS hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofH he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SValid GammaTarget (.img _ _ _) :=
        .img r0.target r1.target re.target
      ⟨ht, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .coimg hs0 hs1 he =>
      let r0 := ofS hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofS hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofH he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SValid GammaTarget (.coimg _ _ _) :=
        .coimg r0.target r1.target re.target
      ⟨ht, CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩

/-- Replay a controlled type-validity derivation in the target context. -/
noncomputable def ofT
    {Psi : EvalCtx} {depth : Nat} {A : Finset Name}
    {GammaCtrl GammaTarget : NLCtx} {tau : Ty} {k : Kind}
    (h : TValid GammaCtrl tau k)
    (selected : CheckedControlledContextSelectedAt Psi depth (∅ : LCtx)
      GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hPsi : Psi.names ⊆ A)
    (hcover : TargetKeysCovered A GammaCtrl GammaTarget)
    (hinputs : BinderInputsT Psi depth GammaTarget h)
    (hfree : Graded.TPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.TBinderHygiene A h) :
    ResultT Psi depth GammaTarget h :=
  match h with
  | .space hs =>
      let r := ofS hs selected hinc hwf hPsi hcover hinputs hfree hhyg
      let ht : TValid GammaTarget (.space _) .base := .space r.target
      ⟨ht, CheckedLocalSideTWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, r.side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, r.side.deep⟩⟩⟩
  | @TValid.piTy GammaCtrl tau0 tau1 k0 k1 L ht0 hbody =>
      let r0 := ofT ht0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.2.2.1
      let domain := hinputs.2.1
      let bodyResult := fun y (hy : y ∉ L) =>
        let hyPsi : y ∉ Psi.names :=
          not_mem_eval_of_ambient hPsi hhyg.1 hy
        let hyCtrl : y ∉ GammaCtrl :=
          not_mem_context_of_keys_subset hhyg.2.1 hy
        let hyTarget : y ∉ GammaTarget :=
          not_mem_target_of_covered hcover hhyg.1 hhyg.2.1 hy
        let hincY : NLCtxIncl (Finmap.insert y tau0 GammaCtrl)
            (Finmap.insert y tau0 GammaTarget) :=
          NLCtxIncl.insert_same hinc y tau0
        let hwfY : V2.CtxWF' (∅ : LCtx)
            (Finmap.insert y tau0 GammaTarget) := by
          simpa only [Basis.tof_std] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
              (b := Basis.std tau0) hwf Finmap.notMem_empty hyTarget
              domain.valid
        let selectedY := selected.insertNonlinearFuture
          hyPsi hyCtrl hyTarget domain
        ofT (hbody y hy) selectedY hincY hwfY hPsi
          (hcover.insertSame y tau0) (hinputs.2.2 y hy)
          (hfree.2 y hy) (hhyg.2.2.2 y hy)
      let ht : TValid GammaTarget (.piTy tau0 tau1) (.arrow k0 k1) :=
        .piTy L r0.target (fun y hy => (bodyResult y hy).target)
      ⟨ht, CheckedLocalSideTWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          fun y hy => ⟨True.intro,
            (bodyResult y hy).side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          fun y hy => ⟨True.intro, (bodyResult y hy).side.deep⟩⟩⟩⟩

/-- Replay a controlled subtyping derivation in the target context. -/
noncomputable def ofSub
    {Psi : EvalCtx} {depth : Nat} {A : Finset Name}
    {GammaCtrl GammaTarget : NLCtx} {s0 s1 : Space}
    (h : SubType GammaCtrl s0 s1)
    (selected : CheckedControlledContextSelectedAt Psi depth (∅ : LCtx)
      GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hPsi : Psi.names ⊆ A)
    (hcover : TargetKeysCovered A GammaCtrl GammaTarget)
    (hinputs : BinderInputsSub Psi depth GammaTarget h)
    (hfree : Graded.SubPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.SubBinderHygiene A h) :
    ResultSub Psi depth GammaTarget h :=
  match h with
  | .sub_ker hs0 hs1 he =>
      let r0 := ofS hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofS hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofH he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SubType GammaTarget (.ker _ _ _) _ :=
        .sub_ker r0.target r1.target re.target
      ⟨ht, CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .sub_coker hs0 hs1 he =>
      let r0 := ofS hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofS hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofH he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SubType GammaTarget (.coker _ _ _) _ :=
        .sub_coker r0.target r1.target re.target
      ⟨ht, CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .sub_img hs0 hs1 he =>
      let r0 := ofS hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofS hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofH he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SubType GammaTarget (.img _ _ _) _ :=
        .sub_img r0.target r1.target re.target
      ⟨ht, CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .sub_coimg hs0 hs1 he =>
      let r0 := ofS hs0 selected hinc hwf hPsi hcover hinputs.1
        hfree.1 hhyg.1
      let r1 := ofS hs1 selected hinc hwf hPsi hcover hinputs.2.1
        hfree.2.1 hhyg.2.1
      let re := ofH he selected hinc hwf hPsi hcover hinputs.2.2
        hfree.2.2 hhyg.2.2
      let ht : SubType GammaTarget (.coimg _ _ _) _ :=
        .sub_coimg r0.target r1.target re.target
      ⟨ht, CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, r0.side.shallow.descendants⟩,
          ⟨⟨True.intro, r1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, r0.side.deep⟩,
          ⟨⟨True.intro, r1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩

/-- Replay a controlled promotion-free typing derivation in the target
context while constructing its proof-indexed fixed-depth local-side tree. -/
noncomputable def ofH
    {Psi : EvalCtx} {depth : Nat} {A : Finset Name}
    {Delta : LCtx} {GammaCtrl GammaTarget : NLCtx}
    {e : Term} {tau : Ty}
    (h : HasType Delta GammaCtrl e tau)
    (selected : CheckedControlledContextSelectedAt Psi depth Delta
      GammaCtrl GammaTarget)
    (hinc : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' Delta GammaTarget)
    (hPsi : Psi.names ⊆ A)
    (hcover : TargetKeysCovered A GammaCtrl GammaTarget)
    (hinputs : BinderInputsH Psi depth GammaTarget h)
    (hfree : Graded.PromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.BinderHygiene A h) :
    ResultH Psi depth GammaTarget h :=
  match h with
  | .zero hs =>
      let selected0 := selected.restrictLinear (linearIncl_empty Delta)
      let rs := ofS hs selected0 hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs hfree hhyg
      let ht : HasType Delta GammaTarget (.zero _) (.space _) := .zero rs.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
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
      let rs := ofS hs selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let r0 := ofH h0 selected0 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_left hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.1
      let r1 := ofH h1 selected1 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf)
        hPsi hcover hinputs.2.2 hfree.2.2 hhyg.2.2
      let ht : HasType (Delta0 ∪ Delta1) GammaTarget (.smul _ _) (.space _) :=
        .smul rs.target hdisj r0.target r1.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs.side.shallow.descendants⟩,
          ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
            ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs.side.deep⟩,
          ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
            ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩⟩
  | .add hs h0 h1 =>
      let selectedEmpty := selected.restrictLinear (linearIncl_empty Delta)
      let rs := ofS hs selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let r0 := ofH h0 selected hinc hwf hPsi hcover
        hinputs.2.1 hfree.2.1 hhyg.2.1
      let r1 := ofH h1 selected hinc hwf hPsi hcover
        hinputs.2.2 hfree.2.2 hhyg.2.2
      let ht : HasType Delta GammaTarget (.add _ _) (.space _) :=
        .add rs.target r0.target r1.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs.side.shallow.descendants⟩,
          ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
            ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs.side.deep⟩,
          ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
            ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩⟩
  | .inner hs =>
      let rs := ofS hs selected hinc hwf hPsi hcover hinputs hfree hhyg
      let ht : HasType (∅ : LCtx) GammaTarget (.inner _) _ := .inner rs.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, rs.side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, rs.side.deep⟩⟩⟩
  | .real_lit r =>
      let ht : HasType (∅ : LCtx) GammaTarget (.real r) (.space .real) :=
        .real_lit r
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
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
      let rs0 := ofS hs0 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let rs1 := ofS hs1 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.1
      let r0 := ofH h0 selected0 hinc hwf0 hPsi hcover
        hinputs.2.2.1 hfree.2.2.1 hhyg.2.2.1
      let r1 := ofH h1 selected1 hinc hwf1 hPsi hcover
        hinputs.2.2.2 hfree.2.2.2 hhyg.2.2.2
      let ht : HasType (Delta0 ∪ Delta1) GammaTarget (.appL _ _ _ _) _ :=
        .app_linear rs0.target rs1.target hdisj r0.target r1.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
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
      let rs := ofS hs selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let r0 := ofH h0 selected0 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_left hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.1
      let r1 := ofH h1 selected1 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf)
        hPsi hcover hinputs.2.2 hfree.2.2 hhyg.2.2
      let ht : HasType (Delta0 ∪ Delta1) GammaTarget (.appI _ _ _) _ :=
        .app_inner rs.target hdisj r0.target r1.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs.side.shallow.descendants⟩,
          ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
            ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs.side.deep⟩,
          ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
            ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩⟩
  | .app_nonlinear h0 h1 =>
      let r0 := ofH h0 selected hinc hwf hPsi hcover
        hinputs.1 hfree.1 hhyg.1
      let r1 := ofH h1 selected hinc hwf hPsi hcover
        hinputs.2 hfree.2 hhyg.2
      let ht : HasType (∅ : LCtx) GammaTarget (.appN _ _) _ :=
        .app_nonlinear r0.target r1.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨r0.side.shallow.here, r0.side.shallow.descendants⟩,
          ⟨r1.side.shallow.here, r1.side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨r0.side.deepHere, r0.side.deepDescendants⟩,
          ⟨r1.side.deepHere, r1.side.deepDescendants⟩⟩⟩⟩
  | @HasType.var_lin GammaCtrl x s =>
      let ht : HasType (Finmap.singleton x s) GammaTarget (.var x) (.space s) :=
        .var_lin
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨leafLinShallow selected Finmap.lookup_singleton_eq hwf, PUnit.unit⟩
        ⟨leafLinDeep selected Finmap.lookup_singleton_eq hwf, PUnit.unit⟩⟩
  | @HasType.var_nlin GammaCtrl x tau hlookupCtrl =>
      let hlookupTarget := hinc x tau hlookupCtrl
      let ht : HasType (∅ : LCtx) GammaTarget (.var x) tau :=
        .var_nlin hlookupTarget
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨leafNlinShallow selected hlookupCtrl hlookupTarget hwf, PUnit.unit⟩
        ⟨leafNlinDeep selected hlookupCtrl hlookupTarget hwf, PUnit.unit⟩⟩
  | .pinv_tensor hs0 hs1 he =>
      let rs0 := ofS hs0 selected hinc hwf hPsi hcover
        hinputs.1 hfree.1 hhyg.1
      let rs1 := ofS hs1 selected hinc hwf hPsi hcover
        hinputs.2.1 hfree.2.1 hhyg.2.1
      let re := ofH he selected hinc hwf hPsi hcover
        hinputs.2.2 hfree.2.2 hhyg.2.2
      let ht : HasType (∅ : LCtx) GammaTarget (.pinvT _ _ _) _ :=
        .pinv_tensor rs0.target rs1.target re.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs0.side.shallow.descendants⟩,
          ⟨⟨True.intro, rs1.side.shallow.descendants⟩,
            ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs0.side.deep⟩,
          ⟨⟨True.intro, rs1.side.deep⟩,
            ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩⟩
  | .pinv_dual hs he =>
      let rs := ofS hs selected hinc hwf hPsi hcover
        hinputs.1 hfree.1 hhyg.1
      let re := ofH he selected hinc hwf hPsi hcover
        hinputs.2 hfree.2 hhyg.2
      let ht : HasType (∅ : LCtx) GammaTarget (.pinvD _ _) _ :=
        .pinv_dual rs.target re.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs.side.shallow.descendants⟩,
          ⟨re.side.shallow.here, re.side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs.side.deep⟩,
          ⟨re.side.deepHere, re.side.deepDescendants⟩⟩⟩⟩
  | .promote _ _ _ _ _ => False.elim hfree
  | .dsumE hs0 hs1 h0 h1 =>
      let selectedEmpty := selected.restrictLinear (linearIncl_empty Delta)
      let rs0 := ofS hs0 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let rs1 := ofS hs1 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.1
      let r0 := ofH h0 selected hinc hwf hPsi hcover
        hinputs.2.2.1 hfree.2.2.1 hhyg.2.2.1
      let r1 := ofH h1 selected hinc hwf hPsi hcover
        hinputs.2.2.2 hfree.2.2.2 hhyg.2.2.2
      let ht : HasType Delta GammaTarget (.dsumE _ _) _ :=
        .dsumE rs0.target rs1.target r0.target r1.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
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
      let rs0 := ofS hs0 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.1
      let rs1 := ofS hs1 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.1
      let r0 := ofH h0 selected0 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_left hwf)
        hPsi hcover hinputs.2.2.1 hfree.2.2.1 hhyg.2.2.1
      let r1 := ofH h1 selected1 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf)
        hPsi hcover hinputs.2.2.2 hfree.2.2.2 hhyg.2.2.2
      let ht : HasType (Delta0 ∪ Delta1) GammaTarget (.tprodE _ _) _ :=
        .tprodE rs0.target rs1.target hdisj r0.target r1.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
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
      let rs := ofS hs selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.2.2.2.1
      let domain := hinputs.2.1
      let bodyResult := fun y (hy : y ∉ L) =>
        let hyPsi : y ∉ Psi.names :=
          not_mem_eval_of_ambient hPsi hhyg.1 hy
        let hyDelta : y ∉ Delta :=
          not_mem_lctx_of_keys_subset hhyg.2.1 hy
        let hyTarget : y ∉ GammaTarget :=
          not_mem_target_of_covered hcover hhyg.1 hhyg.2.2.1 hy
        let hwfY : V2.CtxWF' (Finmap.insert y s Delta) GammaTarget := by
          simpa only [Basis.sof_stdSpace] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
              (b := Basis.stdSpace s) hwf hyDelta hyTarget domain.valid
        let selectedY := selected.insertLinearFuture hyPsi hyDelta domain
        ofH (hbody y hy) selectedY hinc hwfY hPsi hcover
          (hinputs.2.2 y hy) (hfree.2 y hy) (hhyg.2.2.2.2 y hy)
      let ht : HasType Delta GammaTarget (.llam s .real e) (.space (.dual s)) :=
        .llam_real L rs.target (fun y hy => (bodyResult y hy).target)
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs.side.shallow.descendants⟩,
          fun y hy => ⟨(bodyResult y hy).side.shallow.here,
            (bodyResult y hy).side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs.side.deep⟩,
          fun y hy => ⟨(bodyResult y hy).side.deepHere,
            (bodyResult y hy).side.deepDescendants⟩⟩⟩⟩
  | @HasType.llam_tensor Delta GammaCtrl s0 s e L hne hs0 hs hbody =>
      let selectedEmpty := selected.restrictLinear (linearIncl_empty Delta)
      let rs0 := ofS hs0 selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.1 hfree.1 hhyg.2.2.2.1
      let rs := ofS hs selectedEmpty hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf)
        hPsi hcover hinputs.2.1 hfree.2.1 hhyg.2.2.2.2.1
      let domain := hinputs.2.2.1
      let bodyResult := fun y (hy : y ∉ L) =>
        let hyPsi : y ∉ Psi.names :=
          not_mem_eval_of_ambient hPsi hhyg.1 hy
        let hyDelta : y ∉ Delta :=
          not_mem_lctx_of_keys_subset hhyg.2.1 hy
        let hyTarget : y ∉ GammaTarget :=
          not_mem_target_of_covered hcover hhyg.1 hhyg.2.2.1 hy
        let hwfY : V2.CtxWF' (Finmap.insert y s0 Delta) GammaTarget := by
          simpa only [Basis.sof_stdSpace] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
              (b := Basis.stdSpace s0) hwf hyDelta hyTarget domain.valid
        let selectedY := selected.insertLinearFuture hyPsi hyDelta domain
        ofH (hbody y hy) selectedY hinc hwfY hPsi hcover
          (hinputs.2.2.2 y hy) (hfree.2.2 y hy)
          (hhyg.2.2.2.2.2 y hy)
      let ht : HasType Delta GammaTarget (.llam s0 s e) _ :=
        .llam_tensor L hne rs0.target rs.target
          (fun y hy => (bodyResult y hy).target)
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rs0.side.shallow.descendants⟩,
          ⟨⟨True.intro, rs.side.shallow.descendants⟩,
            fun y hy => ⟨(bodyResult y hy).side.shallow.here,
              (bodyResult y hy).side.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rs0.side.deep⟩,
          ⟨⟨True.intro, rs.side.deep⟩,
            fun y hy => ⟨(bodyResult y hy).side.deepHere,
              (bodyResult y hy).side.deepDescendants⟩⟩⟩⟩⟩
  | .embed hsub =>
      let r := ofSub hsub selected hinc hwf hPsi hcover
        hinputs hfree hhyg
      let ht : HasType (∅ : LCtx) GammaTarget (.embed _) _ := .embed r.target
      ⟨ht, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, r.side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, r.side.deep⟩⟩⟩
  | @HasType.nllam GammaCtrl tau0 tau1 k0 k1 e L ht hbody =>
      let rt := ofT ht selected hinc hwf hPsi hcover
        hinputs.1 hfree.1 hhyg.2.2.1
      let domain := hinputs.2.1
      let bodyResult := fun y (hy : y ∉ L) =>
        let hyPsi : y ∉ Psi.names :=
          not_mem_eval_of_ambient hPsi hhyg.1 hy
        let hyCtrl : y ∉ GammaCtrl :=
          not_mem_context_of_keys_subset hhyg.2.1 hy
        let hyTarget : y ∉ GammaTarget :=
          not_mem_target_of_covered hcover hhyg.1 hhyg.2.1 hy
        let hincY : NLCtxIncl (Finmap.insert y tau0 GammaCtrl)
            (Finmap.insert y tau0 GammaTarget) :=
          NLCtxIncl.insert_same hinc y tau0
        let hwfY : V2.CtxWF' (∅ : LCtx)
            (Finmap.insert y tau0 GammaTarget) := by
          simpa only [Basis.tof_std] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
              (b := Basis.std tau0) hwf Finmap.notMem_empty hyTarget
              domain.valid
        let selectedY := selected.insertNonlinearFuture
          hyPsi hyCtrl hyTarget domain
        ofH (hbody y hy) selectedY hincY hwfY hPsi
          (hcover.insertSame y tau0) (hinputs.2.2 y hy)
          (hfree.2 y hy) (hhyg.2.2.2 y hy)
      let hout : HasType (∅ : LCtx) GammaTarget (.nllam tau0 e)
          (.piTy tau0 tau1) :=
        .nllam L rt.target (fun y hy => (bodyResult y hy).target)
      ⟨hout, CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, rt.side.shallow.descendants⟩,
          fun y hy => ⟨(bodyResult y hy).side.shallow.here,
            (bodyResult y hy).side.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, rt.side.deep⟩,
          fun y hy => ⟨(bodyResult y hy).side.deepHere,
            (bodyResult y hy).side.deepDescendants⟩⟩⟩⟩

end

end RawCertifiedPairControlledSourceBuilder
end GLang
