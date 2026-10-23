import GLang.Proofs.Progress.Certificates.RawCertifiedWeaken
import GLang.Proofs.Adequacy.Raw.Context.RawConsistent
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLift
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLower
import GLang.Proofs.Adequacy.Foundations.StrengthenedMono

namespace GLang
namespace RawCertifiedExactAnchorStore

open RawCertifiedOperational

/-- Every concrete evaluator lookup has an exact checked realization of its
literal basis.  No source-context coverage or inferred-type equality is
needed by the variable rule once its typing derivation supplies `tof b`. -/
def CheckedExactLookupStore (Gamma : NLCtx) (Psi : EvalCtx) : Prop :=
  forall {x : VName} {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi (x, b) = some v ->
      exists tauV, C.TyAt Gamma Psi b tauV

/-- Exact lookup stores weaken along nonlinear-context inclusion. -/
theorem CheckedExactLookupStore.nlMono
    {Gamma Gamma' : NLCtx} {Psi : EvalCtx}
    (store : CheckedExactLookupStore Gamma Psi)
    (hGamma : NLCtxIncl Gamma Gamma') :
    CheckedExactLookupStore Gamma' Psi := by
  intro x b v hlookup
  obtain ⟨tauV, hanchor⟩ := store hlookup
  exact ⟨tauV, C.TyAt.weaken hanchor hGamma⟩

/-- Install one fresh exact anchor at the same nonlinear context.  Exact
anchors describe the lookup key's basis realization and therefore do not
depend on the syntax of the value stored at that key. -/
theorem CheckedExactLookupStore.extendValue
    {Gamma : NLCtx} {Psi : EvalCtx}
    (store : CheckedExactLookupStore Gamma Psi)
    {x : VName} {b : Basis} (hkey : (x, b) ∉ Psi)
    {v : ValExpr} {tauV : ValTy}
    (hnew : C.TyAt Gamma Psi b tauV) :
    CheckedExactLookupStore Gamma
      (Psi.extend x b v) := by
  intro y b' v' hlookup
  have hsub : Psi.Subctx (Psi.extend x b v) :=
    EvalCtx.Subctx.extend_right_of_key_fresh hkey v
  by_cases hkey : (y, b') = (x, b)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
    rw [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert] at hlookup
    obtain rfl := Option.some.inj hlookup
    exact ⟨tauV, RawCertifiedOperational.S.TyAt.toC
      ((RawCertifiedOperational.C.TyAt.toS hnew).mono hsub)⟩
  · have hold : EvalCtx.lookup Psi (y, b') = some v' := by
      simpa only [EvalCtx.lookup, EvalCtx.extend,
        Finmap.lookup_insert_of_ne _ hkey] using hlookup
    obtain ⟨tauV', hanchor⟩ := store hold
    exact ⟨tauV', RawCertifiedOperational.S.TyAt.toC
      ((RawCertifiedOperational.C.TyAt.toS hanchor).mono hsub)⟩

/-- Synthetic-variable specialization of `extendValue`, used by checked
binder rules. -/
theorem CheckedExactLookupStore.extend
    {Gamma : NLCtx} {Psi : EvalCtx}
    (store : CheckedExactLookupStore Gamma Psi)
    {x : VName} (hx : x ∉ Psi.names)
    {b : Basis} {tauV : ValTy}
    (hnew : C.TyAt Gamma Psi b tauV) :
    CheckedExactLookupStore Gamma
      (Psi.extend x b (.var x tauV)) :=
  store.extendValue (by
    intro hmem
    exact hx (Finset.mem_image.mpr
      ⟨(x, b), Finmap.mem_keys.mpr hmem, rfl⟩)) hnew

/-- Simultaneously install a fresh standard nonlinear binder in the source
and evaluator contexts.  The supplied parent-world anchor is exactly the
domain anchor projected from the enclosing checked Pi certificate. -/
theorem CheckedExactLookupStore.extendNonlinearStandard
    {Gamma : NLCtx} {Psi : EvalCtx}
    (store : CheckedExactLookupStore Gamma Psi)
    {x : VName} (hxPsi : x ∉ Psi.names) (hxGamma : x ∉ Gamma)
    {tau : Ty} {tauV : ValTy}
    (hnew : C.TyAt Gamma Psi (Basis.std tau) tauV) :
    CheckedExactLookupStore (Finmap.insert x tau Gamma)
      (Psi.extend x (Basis.std tau) (.var x tauV)) := by
  let hGamma : NLCtxIncl Gamma (Finmap.insert x tau Gamma) :=
    (NLCtxIncl.refl Gamma).insert_right hxGamma tau
  intro y b v hlookup
  exact CheckedExactLookupStore.nlMono
    (CheckedExactLookupStore.extend store hxPsi hnew) hGamma hlookup

/-- Linear-binder spelling of `extend`: the nonlinear context is unchanged,
and the standard-space anchor is supplied by the enclosing checked type. -/
theorem CheckedExactLookupStore.extendLinearStandard
    {Gamma : NLCtx} {Psi : EvalCtx}
    (store : CheckedExactLookupStore Gamma Psi)
    {x : VName} (hxPsi : x ∉ Psi.names)
    {s : Space} {tauV : ValTy}
    (hnew : C.TyAt Gamma Psi (Basis.stdSpace s) tauV) :
    CheckedExactLookupStore Gamma
      (Psi.extend x (Basis.stdSpace s) (.var x tauV)) :=
  store.extend hxPsi hnew

end RawCertifiedExactAnchorStore
end GLang
