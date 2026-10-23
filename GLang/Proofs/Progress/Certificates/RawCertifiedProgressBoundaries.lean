import GLang.Proofs.Progress.Binders
import GLang.Proofs.Progress.DependentApplication
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedContextMono
import GLang.Proofs.Progress.Certificates.RawCertifiedRenameProof
import GLang.Proofs.Progress.Certificates.RawCertifiedCheckedSubst

/-!
# Constructive administrative transports for checked standard progress

This module is the current-facing assembly point for the two constructive
administrative transports used by checked progress.  They are deliberately
narrow:

* `RenameProof.checkedRenameLaws` constructively inhabits the already-audited
  three-field `CheckedRenameLaws` interface.  It says only that a complete
  checked certificate can be renamed across a fresh binder (or specialized
  from a symbolic linear variable to one delta column).
* `RawCertifiedOperational.checkedTyAtAppCut` cuts one fresh nonlinear
  placeholder out of one opened, exact `C.TyAt` codomain.  It is proved by
  the five-way checked substitution induction and is not an assumption.

The four binder arms and nonlinear application below are consequences of
exactly those constructive transports.  Promotion is discharged separately by the
admissible weakening lemma `C.TyAt.weaken`; it introduces no third boundary.

The final section also constructs the existing unindexed
`CheckedProgressOpenArms` as far as its interface permits.  Its residual
record contains only the two variable/history arms and four *unindexed*
binder arms.  The latter are already proved above with the necessary local
`CtxWF'` premise; removing them from the residual therefore belongs to the
WF-indexed master integration, not to another semantic assumption.
-/

namespace GLang
namespace RawCertifiedProgressBoundaries

open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedBinderProgressSpike

/-! ## Constructive administrative transports -/

/-! ## Four WF-indexed binder arms -/

/-- Checked Pi formation, with the local source-context WF fact threaded to
the chosen fresh name. -/
theorem checked_arm_ty_pi_wf :
    ∀ {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind}
      (L : Finset Name)
      (ht0 : TValid Gamma tau0 k0)
      (ht1 : ∀ y, y ∉ L →
        TValid (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1),
      cMotiveTWF Gamma tau0 →
      (∀ y, y ∉ L →
        cMotiveTWF (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1)) →
      cMotiveTWF Gamma (.piTy tau0 tau1) :=
  RawCertifiedBinderProgressSpike.checked_arm_ty_pi_wf
    RawCertifiedOperational.RenameProof.checkedRenameLaws

/-- Checked real-codomain linear abstraction. -/
theorem checked_arm_llam_real_wf :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {s : Space} {e : Term}
      (L : Finset Name),
      SValid Gamma s →
      (∀ y, y ∉ L → HasType (Finmap.insert y s Delta) Gamma
        (Term.openVar y e) (.space .real)) →
      cMotiveSWF Gamma s →
      (∀ y, y ∉ L → cMotiveHWF (Finmap.insert y s Delta) Gamma
        (Term.openVar y e) (.space .real)) →
      cMotiveHWF Delta Gamma (.llam s .real e) (.space (.dual s)) :=
  RawCertifiedBinderProgressSpike.checked_arm_llam_real_wf
    RawCertifiedOperational.RenameProof.checkedRenameLaws

/-- Checked tensor-codomain linear abstraction. -/
theorem checked_arm_llam_tensor_wf :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {s0 s : Space} {e : Term}
      (L : Finset Name),
      s ≠ .real → SValid Gamma s0 → SValid Gamma s →
      (∀ y, y ∉ L → HasType (Finmap.insert y s0 Delta) Gamma
        (Term.openVar y e) (.space s)) →
      cMotiveSWF Gamma s0 → cMotiveSWF Gamma s →
      (∀ y, y ∉ L → cMotiveHWF (Finmap.insert y s0 Delta) Gamma
        (Term.openVar y e) (.space s)) →
      cMotiveHWF Delta Gamma (.llam s0 s e)
        (.space (.tprod (.dual s0) s)) :=
  RawCertifiedBinderProgressSpike.checked_arm_llam_tensor_wf
    RawCertifiedOperational.RenameProof.checkedRenameLaws

/-- Checked nonlinear abstraction. -/
theorem checked_arm_nllam_wf :
    ∀ {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind} {e : Term}
      (L : Finset Name)
      (ht : TValid Gamma (.piTy tau0 tau1) (.arrow k0 k1))
      (hbody : ∀ y, y ∉ L → HasType ∅ (Finmap.insert y tau0 Gamma)
        (Term.openVar y e) (Ty.openVar y tau1)),
      cMotiveTWF Gamma (.piTy tau0 tau1) →
      (∀ y, y ∉ L → cMotiveHWF ∅ (Finmap.insert y tau0 Gamma)
        (Term.openVar y e) (Ty.openVar y tau1)) →
      cMotiveHWF ∅ Gamma (.nllam tau0 e) (.piTy tau0 tau1) :=
  RawCertifiedBinderProgressSpike.checked_arm_nllam_wf
    RawCertifiedOperational.RenameProof.checkedRenameLaws

/-- The four cofinite binder fields, packaged for the WF-indexed mutual
master.  This record contains no assumptions beyond constructive renaming. -/
structure CheckedBinderArmsWF : Prop where
  ty_pi :
    ∀ {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind}
      (L : Finset Name)
      (ht0 : TValid Gamma tau0 k0)
      (ht1 : ∀ y, y ∉ L →
        TValid (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1),
      cMotiveTWF Gamma tau0 →
      (∀ y, y ∉ L →
        cMotiveTWF (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1)) →
      cMotiveTWF Gamma (.piTy tau0 tau1)
  llam_real :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {s : Space} {e : Term}
      (L : Finset Name),
      SValid Gamma s →
      (∀ y, y ∉ L → HasType (Finmap.insert y s Delta) Gamma
        (Term.openVar y e) (.space .real)) →
      cMotiveSWF Gamma s →
      (∀ y, y ∉ L → cMotiveHWF (Finmap.insert y s Delta) Gamma
        (Term.openVar y e) (.space .real)) →
      cMotiveHWF Delta Gamma (.llam s .real e) (.space (.dual s))
  llam_tensor :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {s0 s : Space} {e : Term}
      (L : Finset Name),
      s ≠ .real → SValid Gamma s0 → SValid Gamma s →
      (∀ y, y ∉ L → HasType (Finmap.insert y s0 Delta) Gamma
        (Term.openVar y e) (.space s)) →
      cMotiveSWF Gamma s0 → cMotiveSWF Gamma s →
      (∀ y, y ∉ L → cMotiveHWF (Finmap.insert y s0 Delta) Gamma
        (Term.openVar y e) (.space s)) →
      cMotiveHWF Delta Gamma (.llam s0 s e)
        (.space (.tprod (.dual s0) s))
  nllam :
    ∀ {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind} {e : Term}
      (L : Finset Name)
      (ht : TValid Gamma (.piTy tau0 tau1) (.arrow k0 k1))
      (hbody : ∀ y, y ∉ L → HasType ∅ (Finmap.insert y tau0 Gamma)
        (Term.openVar y e) (Ty.openVar y tau1)),
      cMotiveTWF Gamma (.piTy tau0 tau1) →
      (∀ y, y ∉ L → cMotiveHWF ∅ (Finmap.insert y tau0 Gamma)
        (Term.openVar y e) (Ty.openVar y tau1)) →
      cMotiveHWF ∅ Gamma (.nllam tau0 e) (.piTy tau0 tau1)

/-- All four checked binder arms are closed by constructive renaming. -/
theorem checkedBinderArmsWF : CheckedBinderArmsWF where
  ty_pi := checked_arm_ty_pi_wf
  llam_real := checked_arm_llam_real_wf
  llam_tensor := checked_arm_llam_tensor_wf
  nllam := checked_arm_nllam_wf

/-! ## Nonlinear application -/

/-- Nonlinear application with the source-context WF fact required by the
checked dependent cut. -/
theorem checked_arm_app_nonlinear :
    ∀ {Gamma : NLCtx} {e0 e1 : Term} {tau0 tau1 : Ty}
      (ht0 : HasType ∅ Gamma e0 (.piTy tau0 tau1))
      (ht1 : HasType ∅ Gamma e1 tau0),
      V2.CtxWF' ∅ Gamma →
      cMotiveH ∅ Gamma e0 (.piTy tau0 tau1) →
      cMotiveH ∅ Gamma e1 tau0 →
      cMotiveH ∅ Gamma (.appN e0 e1) (Ty.instantiate e1 tau1) :=
  RawCertifiedProgressScratch.checked_arm_app_nonlinear_of_tyAt_appCut
    RawCertifiedOperational.checkedTyAtAppCut

/-- The same closed nonlinear-application arm lifted to the WF-indexed
motives.  All three source judgments use the same context, so the caller's
one WF certificate is reused literally. -/
theorem checked_arm_app_nonlinear_wf :
    ∀ {Gamma : NLCtx} {e0 e1 : Term} {tau0 tau1 : Ty}
      (ht0 : HasType ∅ Gamma e0 (.piTy tau0 tau1))
      (ht1 : HasType ∅ Gamma e1 tau0),
      cMotiveHWF ∅ Gamma e0 (.piTy tau0 tau1) →
      cMotiveHWF ∅ Gamma e1 tau0 →
      cMotiveHWF ∅ Gamma (.appN e0 e1) (Ty.instantiate e1 tau1) := by
  intro Gamma e0 e1 tau0 tau1 ht0 ht1 ih0 ih1 Psi hP hcov hwf
  exact checked_arm_app_nonlinear ht0 ht1 hwf
    (fun Psi' hP' hcov' => ih0 Psi' hP' hcov' hwf)
    (fun Psi' hP' hcov' => ih1 Psi' hP' hcov' hwf)
    Psi hP hcov

/-! ## Promotion from the administrative context rule -/

/-- Exact basis validity is already stored at the root of every checked
`TyAt` certificate. -/
theorem checkedTyAt_basisValid
    (h : C.TyAt Gamma Psi b tauv) : Basis.BasisValid Gamma b :=
  h.basisValid

/-- The admissible weakening lemma `C.TyAt.weaken` supplies exactly the
hereditary operation isolated by `CheckedTyAtNLCtxMono`.  No value, basis,
evaluator, or realized type changes. -/
theorem checkedTyAtNLCtxMono_from_rule : CheckedTyAtNLCtxMono := by
  intro Gamma Gamma' Psi b tauv hGamma hty
  exact C.TyAt.weaken hty hGamma

theorem checked_arm_promote :
    ∀ {Delta : LCtx} {Gamma' : NLCtx} {e : Term} {tau : Ty}
      (lin : LCtx),
      Finmap.Disjoint lin Delta → Finmap.Disjoint lin.toNL Gamma' →
      PromoteFresh lin Delta Gamma' →
      ∀ (ht : HasType (lin ∪ Delta) Gamma' e tau),
        cMotiveH (lin ∪ Delta) Gamma' e tau →
        cMotiveH Delta (lin.toNL ∪ Gamma') e tau :=
  RawCertifiedOperational.checked_arm_promote_of_tyAt_mono
    checkedTyAtNLCtxMono_from_rule

structure CheckedProgressUnindexedResidual : Prop where
  ty_pi :
    ∀ {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind}
      (L : Finset Name)
      (ht0 : TValid Gamma tau0 k0)
      (ht1 : ∀ y, y ∉ L →
        TValid (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1),
      cMotiveT Gamma tau0 →
      (∀ y, y ∉ L →
        cMotiveT (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1)) →
      cMotiveT Gamma (.piTy tau0 tau1)
  var_lin :
    ∀ {Gamma : NLCtx} {x : Name} {s : Space},
      cMotiveH (Finmap.singleton x s) Gamma (.var x) (.space s)
  var_nlin :
    ∀ {Gamma : NLCtx} {x : Name} {tau : Ty},
      Gamma.lookup x = some tau → cMotiveH ∅ Gamma (.var x) tau
  llam_real :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {s : Space} {e : Term}
      (L : Finset Name),
      SValid Gamma s →
      (∀ y, y ∉ L → HasType (Finmap.insert y s Delta) Gamma
        (Term.openVar y e) (.space .real)) →
      cMotiveS Gamma s →
      (∀ y, y ∉ L → cMotiveH (Finmap.insert y s Delta) Gamma
        (Term.openVar y e) (.space .real)) →
      cMotiveH Delta Gamma (.llam s .real e) (.space (.dual s))
  llam_tensor :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {s0 s : Space} {e : Term}
      (L : Finset Name),
      s ≠ .real → SValid Gamma s0 → SValid Gamma s →
      (∀ y, y ∉ L → HasType (Finmap.insert y s0 Delta) Gamma
        (Term.openVar y e) (.space s)) →
      cMotiveS Gamma s0 → cMotiveS Gamma s →
      (∀ y, y ∉ L → cMotiveH (Finmap.insert y s0 Delta) Gamma
        (Term.openVar y e) (.space s)) →
      cMotiveH Delta Gamma (.llam s0 s e)
        (.space (.tprod (.dual s0) s))
  nllam :
    ∀ {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind} {e : Term}
      (L : Finset Name)
      (ht : TValid Gamma (.piTy tau0 tau1) (.arrow k0 k1))
      (hbody : ∀ y, y ∉ L → HasType ∅ (Finmap.insert y tau0 Gamma)
        (Term.openVar y e) (Ty.openVar y tau1)),
      cMotiveT Gamma (.piTy tau0 tau1) →
      (∀ y, y ∉ L → cMotiveH ∅ (Finmap.insert y tau0 Gamma)
        (Term.openVar y e) (Ty.openVar y tau1)) →
      cMotiveH ∅ Gamma (.nllam tau0 e) (.piTy tau0 tau1)
  app_nonlinear :
    ∀ {Gamma : NLCtx} {e0 e1 : Term} {tau0 tau1 : Ty}
      (ht0 : HasType ∅ Gamma e0 (.piTy tau0 tau1))
      (ht1 : HasType ∅ Gamma e1 tau0),
      cMotiveH ∅ Gamma e0 (.piTy tau0 tau1) →
      cMotiveH ∅ Gamma e1 tau0 →
      cMotiveH ∅ Gamma (.appN e0 e1) (Ty.instantiate e1 tau1)

theorem checkedProgressOpenArms_of_residual
    (residual : CheckedProgressUnindexedResidual) :
    CheckedProgressOpenArms where
  ty_pi := residual.ty_pi
  var_lin := residual.var_lin
  var_nlin := residual.var_nlin
  promote := checked_arm_promote
  llam_real := residual.llam_real
  llam_tensor := residual.llam_tensor
  nllam := residual.nllam
  app_nonlinear := residual.app_nonlinear

theorem checked_progress_master_of_residual
    (residual : CheckedProgressUnindexedResidual) :
    (∀ {Gamma : NLCtx} {s : Space}, SValid Gamma s → cMotiveS Gamma s)
  ∧ (∀ {Gamma : NLCtx} {tau : Ty} {k : Kind},
      TValid Gamma tau k → cMotiveT Gamma tau)
  ∧ (∀ {Gamma : NLCtx} {s0 s1 : Space},
      SubType Gamma s0 s1 → cMotiveSub Gamma s0 s1)
  ∧ (∀ {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty},
      HasType Delta Gamma e tau → cMotiveH Delta Gamma e tau) :=
  checked_progress_master_of (checkedProgressOpenArms_of_residual residual)

theorem certifiedStdProgress_of_residual
    (residual : CheckedProgressUnindexedResidual) : CertifiedStdProgress :=
  certifiedStdProgress_of (checkedProgressOpenArms_of_residual residual)

end RawCertifiedProgressBoundaries
end GLang
