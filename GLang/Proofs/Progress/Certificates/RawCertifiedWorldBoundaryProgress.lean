import GLang.Proofs.Progress.Certificates.RawCertifiedWeaken
import GLang.Proofs.Progress.Certificates.RawCertifiedWorldBinderProgress
import GLang.Proofs.Adequacy.Raw.RawLocalCtxWFPromotion
import GLang.Proofs.Progress.Certificates.RawCertifiedFrameApplicationReanchor

namespace GLang
namespace RawCertifiedWorldBoundaryProgress

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedWorldBinderProgress
open RawCertifiedFrameApplicationReanchor

private theorem nlCtxIncl_union_right
    {left right : NLCtx} (hdisj : Finmap.Disjoint left right) :
    NLCtxIncl right (left ∪ right) := by
  intro x tau hx
  have hxRight : x ∈ right := Finmap.mem_of_lookup_eq_some hx
  have hxLeft : x ∉ left := fun hm => hdisj x hm hxRight
  rw [Finmap.lookup_union_right hxLeft]
  exact hx

/-- Nonlinear application over a restricted evaluator world.  This is the
reviewed exact dependent cut, with the world witness passed unchanged to the
two recursive calls. -/
theorem checked_arm_app_nonlinear_world_of_tyAt_appCut
    (happCut : CheckedTyAtAppCut) (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e0 e1 : Term} {tau0 tau1 : Ty}
      (_ht0 : HasType ∅ Gamma e0 (.piTy tau0 tau1))
      (_ht1 : HasType ∅ Gamma e1 tau0),
      cMotiveHWorld W ∅ Gamma e0 (.piTy tau0 tau1) →
      cMotiveHWorld W ∅ Gamma e1 tau0 →
      cMotiveHWorld W ∅ Gamma (.appN e0 e1)
        (Ty.instantiate e1 tau1) := by
  intro Gamma e0 e1 tau0 tau1 _ht0 _ht1 ih0 ih1 Psi hW hP hcov hwf
  obtain ⟨env0, tauvFun, hfun⟩ := ih0 Psi hW hP hcov hwf
  obtain ⟨env1, tauvArg, harg⟩ := ih1 Psi hW hP hcov hwf
  obtain ⟨_arg, _tauArg, out, tauOut, _harg', hstep⟩ :=
    checkedAppN_at_frame happCut hP hcov hwf
      (by simpa only [Basis.std] using hfun) harg
  rw [show Basis.std (Ty.instantiate e1 tau1) =
      Basis.instantiate e1 (Basis.std tau1) from
    Basis.std_openRec e1 tau1 0]
  exact ⟨out, tauOut, hstep⟩

/-- Promotion over a restricted evaluator world.  The evaluator is
unchanged, while `CtxWF'.promote_inner` derives the recursive source world. -/
theorem checked_arm_promote_world (W : EvalCtx → Prop) :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty} (lin : LCtx),
      Finmap.Disjoint lin Delta → Finmap.Disjoint lin.toNL Gamma →
      PromoteFresh lin Delta Gamma →
      ∀ (ht : HasType (lin ∪ Delta) Gamma e tau),
        cMotiveHWorld W (lin ∪ Delta) Gamma e tau →
        cMotiveHWorld W Delta (lin.toNL ∪ Gamma) e tau := by
  intro Delta Gamma e tau lin hdDelta hdGamma hfresh ht ih
    Psi hW hP hcov hwf
  have hwfInner : V2.CtxWF' (lin ∪ Delta) Gamma :=
    RawLocalCtxWFPromotion.V2.CtxWF'.promote_inner
      hwf hdDelta hdGamma hfresh
  obtain ⟨v, tauv, hterm⟩ :=
    ih Psi hW hP (hcov.promote hdGamma) hwfInner
  have hle : NLCtxIncl Gamma (lin.toNL ∪ Gamma) :=
    nlCtxIncl_union_right hdGamma
  have htyAt : C.TyAt (lin.toNL ∪ Gamma) Psi (Basis.std tau) tauv :=
    C.TyAt.weaken hterm.tyAt hle
  have hbv : Basis.BasisValid (lin.toNL ∪ Gamma) (Basis.std tau) :=
    raw_basisValid_mono hterm.basisValid hle
  have htyped : Nonempty
      (HasType Delta (lin.toNL ∪ Gamma) e (Basis.tof (Basis.std tau))) := by
    obtain ⟨hsource⟩ := hterm.hasType
    simpa only [Basis.tof_std] using
      (show Nonempty (HasType Delta (lin.toNL ∪ Gamma) e tau) from
        ⟨HasType.promote lin hdDelta hdGamma hfresh
          (by simpa only [Basis.tof_std] using hsource)⟩)
  exact ⟨v, tauv,
    C.Term.promote lin hdDelta hdGamma hfresh (NLCtxIncl.refl _) htyped hbv htyAt hterm⟩

end RawCertifiedWorldBoundaryProgress
end GLang
