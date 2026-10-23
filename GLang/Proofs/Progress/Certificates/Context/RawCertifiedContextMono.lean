import GLang.Proofs.Progress.Certificates.RawCertifiedProgressArms
import GLang.Proofs.Progress.Certificates.RawCertifiedWeaken

/-!
# Nonlinear source-context transport for checked operational certificates

This file isolates the source-context weakening needed by the checked
progress promotion arm.  The source-context mono lemmas themselves
(`svalid_mono_nl`, `tvalid_mono_nl`, `hasType_mono_nl_checked`,
`NLCtxIncl.insert_same`) and the admissible checked weakening lemmas
`C.*.weaken` live in `RawCertifiedWeaken`, low in the import graph.
-/

namespace GLang
namespace RawCertifiedOperational

open Basis (BasisValid)

/-- The exact checked transport required by the promotion progress arm.  It
is named separately so the arm below states no stronger requirement than it
actually consumes. -/
def CheckedTyAtNLCtxMono : Prop :=
  ∀ {Gamma Gamma' : NLCtx} {Psi : EvalCtx} {b : Basis} {tauv : ValTy},
    NLCtxIncl Gamma Gamma' → C.TyAt Gamma Psi b tauv →
      C.TyAt Gamma' Psi b tauv

/-- The right summand embeds in a disjoint left-priority union. -/
theorem nlCtxIncl_union_right {left right : NLCtx}
    (hdisj : Finmap.Disjoint left right) :
    NLCtxIncl right (left ∪ right) := by
  intro x tau hx
  have hxRight : x ∈ right := Finmap.mem_of_lookup_eq_some hx
  have hxLeft : x ∉ left := fun hm => hdisj x hm hxRight
  rw [Finmap.lookup_union_right hxLeft]
  exact hx

theorem checked_arm_promote_of_tyAt_mono
    (hmono : CheckedTyAtNLCtxMono) :
    ∀ {Delta : LCtx} {Gamma' : NLCtx} {e : Term} {tau : Ty} (lin : LCtx),
      Finmap.Disjoint lin Delta → Finmap.Disjoint lin.toNL Gamma' →
      PromoteFresh lin Delta Gamma' →
      ∀ (_ht : HasType (lin ∪ Delta) Gamma' e tau),
        RawCertifiedProgressScratch.cMotiveH (lin ∪ Delta) Gamma' e tau →
        RawCertifiedProgressScratch.cMotiveH
          Delta (lin.toNL ∪ Gamma') e tau := by
  intro Delta Gamma' e tau lin hdDelta hdGamma hfresh _ht ih
    Psi hP hcov
  obtain ⟨v, tauv, hterm⟩ := ih Psi hP (hcov.promote hdGamma)
  have hle : NLCtxIncl Gamma' (lin.toNL ∪ Gamma') :=
    nlCtxIncl_union_right hdGamma
  have htyAt : C.TyAt (lin.toNL ∪ Gamma') Psi (Basis.std tau) tauv :=
    hmono hle hterm.tyAt
  have hbv : BasisValid (lin.toNL ∪ Gamma') (Basis.std tau) :=
    raw_basisValid_mono hterm.basisValid hle
  have htyped : Nonempty
      (HasType Delta (lin.toNL ∪ Gamma') e (Basis.tof (Basis.std tau))) := by
    obtain ⟨hsource⟩ := hterm.hasType
    simpa only [Basis.tof_std] using
      (show Nonempty (HasType Delta (lin.toNL ∪ Gamma') e tau) from
        ⟨HasType.promote lin hdDelta hdGamma hfresh
          (by simpa only [Basis.tof_std] using hsource)⟩)
  exact ⟨v, tauv,
    C.Term.promote lin hdDelta hdGamma hfresh (NLCtxIncl.refl _) htyped hbv htyAt hterm⟩

end RawCertifiedOperational
end GLang
