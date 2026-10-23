import GLang.Proofs.Progress.Certificates.RawCertifiedWorldProgressArms
import GLang.Proofs.Progress.Certificates.RawCertifiedWorldBoundaryProgress
import GLang.Proofs.Progress.Certificates.RawCertifiedProgressBoundaries
import GLang.Proofs.Progress.Certificates.RawCertifiedPiBasisTransport

/-!
# Local-side checked progress master

This module combines the 26 concrete checked arms, the four reviewed binder
arms, nonlinear application, promotion, and the hereditary variable store in
the actual generated four-way source recursor.  Its side certificate follows
the source derivation exactly: only variable leaves require a root evaluator
basis-validity fact, while binder-added standard keys are discharged from the
local `CtxWF'`.
-/

namespace GLang
namespace RawCertifiedLocalProgressMaster

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedWorldBinderProgress
open RawCertifiedWorldProgressArms
open RawCertifiedWorldBoundaryProgress
open RawCertifiedPiBasisTransport

def cMotiveSLocal (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (Gamma : NLCtx) (s : Space) (h : SValid Gamma s) : Prop :=
  CheckedLocalSideS Psi0 h → cMotiveSWorld W Gamma s

def cMotiveTLocal (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (Gamma : NLCtx) (tau : Ty) (k : Kind) (h : TValid Gamma tau k) : Prop :=
  CheckedLocalSideT Psi0 h → cMotiveTWorld W Gamma tau

def cMotiveSubLocal (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (Gamma : NLCtx) (s0 s1 : Space) (h : SubType Gamma s0 s1) : Prop :=
  CheckedLocalSideSub Psi0 h → cMotiveSubWorld W Gamma s0 s1

def cMotiveHLocal (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (Delta : LCtx) (Gamma : NLCtx) (e : Term) (tau : Ty)
    (h : HasType Delta Gamma e tau) : Prop :=
  CheckedLocalSideBases Psi0 h → cMotiveHWorld W Delta Gamma e tau

/-! ## Space/type handlers with descendant extraction -/

private theorem local_empty (Psi0 : EvalCtx) (W : EvalCtx → Prop) :
    cMotiveSLocal Psi0 W Gamma .empty SValid.empty := by
  intro _side
  exact checked_arm_empty_world W

private theorem local_real (Psi0 : EvalCtx) (W : EvalCtx → Prop) :
    cMotiveSLocal Psi0 W Gamma .real SValid.real := by
  intro _side
  exact checked_arm_real_world W

private theorem local_dual (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs : SValid Gamma s)
    (ih : cMotiveSLocal Psi0 W Gamma s hs) :
    cMotiveSLocal Psi0 W Gamma (.dual s) (.dual hs) := by
  intro side
  exact checked_arm_dual_world W hs
    (ih (CheckedLocalSideS.ofBelowPair side.descendants))

private theorem local_dsum (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (ih0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ih1 : cMotiveSLocal Psi0 W Gamma s1 hs1) :
    cMotiveSLocal Psi0 W Gamma (.dsum s0 s1) (.dsum hs0 hs1) := by
  intro side
  exact checked_arm_dsum_world W hs0 hs1
    (ih0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideS.ofBelowPair side.descendants.2))

private theorem local_tprod (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (ih0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ih1 : cMotiveSLocal Psi0 W Gamma s1 hs1) :
    cMotiveSLocal Psi0 W Gamma (.tprod s0 s1) (.tprod hs0 hs1) := by
  intro side
  exact checked_arm_tprod_world W hs0 hs1
    (ih0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideS.ofBelowPair side.descendants.2))

private theorem local_ker (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1)))
    (ih0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ih1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ihe : cMotiveHLocal Psi0 W ∅ Gamma e
      (.space (.tprod (.dual s0) s1)) he) :
    cMotiveSLocal Psi0 W Gamma (.ker s0 s1 e) (.ker hs0 hs1 he) := by
  intro side
  exact checked_arm_ker_world W hs0 hs1 he
    (ih0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ihe (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_coker (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1)))
    (ih0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ih1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ihe : cMotiveHLocal Psi0 W ∅ Gamma e
      (.space (.tprod (.dual s0) s1)) he) :
    cMotiveSLocal Psi0 W Gamma (.coker s0 s1 e) (.coker hs0 hs1 he) := by
  intro side
  exact checked_arm_coker_world W hs0 hs1 he
    (ih0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ihe (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_img (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1)))
    (ih0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ih1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ihe : cMotiveHLocal Psi0 W ∅ Gamma e
      (.space (.tprod (.dual s0) s1)) he) :
    cMotiveSLocal Psi0 W Gamma (.img s0 s1 e) (.img hs0 hs1 he) := by
  intro side
  exact checked_arm_img_world W hs0 hs1 he
    (ih0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ihe (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_coimg (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1)))
    (ih0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ih1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ihe : cMotiveHLocal Psi0 W ∅ Gamma e
      (.space (.tprod (.dual s0) s1)) he) :
    cMotiveSLocal Psi0 W Gamma (.coimg s0 s1 e) (.coimg hs0 hs1 he) := by
  intro side
  exact checked_arm_coimg_world W hs0 hs1 he
    (ih0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ihe (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_ty_space (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs : SValid Gamma s)
    (ih : cMotiveSLocal Psi0 W Gamma s hs) :
    cMotiveTLocal Psi0 W Gamma (.space s) .base (.space hs) := by
  intro side
  exact checked_arm_ty_space_world W hs
    (ih (CheckedLocalSideS.ofBelowPair side.descendants))

private theorem local_ty_pi (laws : CheckedRenameLaws)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop) (hclosed : StdExtensionClosed W)
    (L : Finset Name) (ht0 : TValid Gamma tau0 k0)
    (ht1 : ∀ y, y ∉ L →
      TValid (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1)
    (ih0 : cMotiveTLocal Psi0 W Gamma tau0 k0 ht0)
    (ih1 : ∀ y (hy : y ∉ L), cMotiveTLocal Psi0 W
      (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1 (ht1 y hy)) :
    cMotiveTLocal Psi0 W Gamma (.piTy tau0 tau1) (.arrow k0 k1)
      (.piTy L ht0 ht1) := by
  intro side
  exact checked_arm_ty_pi_world laws W hclosed L ht0 ht1
    (ih0 (CheckedLocalSideT.ofBelowPair side.descendants.1))
    (fun y hy => ih1 y hy
      (CheckedLocalSideT.ofBelowPair (side.descendants.2 y hy)))

/-! ## Subtyping handlers -/

private theorem local_sub_ker (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1)))
    (ih0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ih1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ihe : cMotiveHLocal Psi0 W ∅ Gamma e
      (.space (.tprod (.dual s0) s1)) he) :
    cMotiveSubLocal Psi0 W Gamma (.ker s0 s1 e) s0
      (.sub_ker hs0 hs1 he) := by
  intro side
  exact checked_arm_sub_ker_world W hs0 hs1 he
    (ih0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ihe (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_sub_coker (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1)))
    (ih0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ih1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ihe : cMotiveHLocal Psi0 W ∅ Gamma e
      (.space (.tprod (.dual s0) s1)) he) :
    cMotiveSubLocal Psi0 W Gamma (.coker s0 s1 e) s0
      (.sub_coker hs0 hs1 he) := by
  intro side
  exact checked_arm_sub_coker_world W hs0 hs1 he
    (ih0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ihe (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_sub_img (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1)))
    (ih0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ih1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ihe : cMotiveHLocal Psi0 W ∅ Gamma e
      (.space (.tprod (.dual s0) s1)) he) :
    cMotiveSubLocal Psi0 W Gamma (.img s0 s1 e) s1
      (.sub_img hs0 hs1 he) := by
  intro side
  exact checked_arm_sub_img_world W hs0 hs1 he
    (ih0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ihe (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_sub_coimg (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1)))
    (ih0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ih1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ihe : cMotiveHLocal Psi0 W ∅ Gamma e
      (.space (.tprod (.dual s0) s1)) he) :
    cMotiveSubLocal Psi0 W Gamma (.coimg s0 s1 e) s1
      (.sub_coimg hs0 hs1 he) := by
  intro side
  exact checked_arm_sub_coimg_world W hs0 hs1 he
    (ih0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ihe (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

/-! ## Term handlers -/

private theorem local_zero (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs : SValid Gamma s)
    (ihs : cMotiveSLocal Psi0 W Gamma s hs) :
    cMotiveHLocal Psi0 W Delta Gamma (.zero s) (.space s) (.zero hs) := by
  intro side
  exact checked_arm_zero_world W hs
    (ihs (CheckedLocalSideS.ofBelowPair side.descendants))

private theorem local_smul (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs : SValid Gamma s) (hdisj : Finmap.Disjoint Delta0 Delta1)
    (ht0 : HasType Delta0 Gamma e0 (.space .real))
    (ht1 : HasType Delta1 Gamma e1 (.space s))
    (ihs : cMotiveSLocal Psi0 W Gamma s hs)
    (ih0 : cMotiveHLocal Psi0 W Delta0 Gamma e0 (.space .real) ht0)
    (ih1 : cMotiveHLocal Psi0 W Delta1 Gamma e1 (.space s) ht1) :
    cMotiveHLocal Psi0 W (Delta0 ∪ Delta1) Gamma (.smul e0 e1)
      (.space s) (.smul hs hdisj ht0 ht1) := by
  intro side
  exact checked_arm_smul_world W hs hdisj ht0 ht1
    (ihs (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih0 (CheckedLocalSideBases.ofBelowPair side.descendants.2.1))
    (ih1 (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_add (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs : SValid Gamma s)
    (ht0 : HasType Delta Gamma e0 (.space s))
    (ht1 : HasType Delta Gamma e1 (.space s))
    (ihs : cMotiveSLocal Psi0 W Gamma s hs)
    (ih0 : cMotiveHLocal Psi0 W Delta Gamma e0 (.space s) ht0)
    (ih1 : cMotiveHLocal Psi0 W Delta Gamma e1 (.space s) ht1) :
    cMotiveHLocal Psi0 W Delta Gamma (.add e0 e1) (.space s)
      (.add hs ht0 ht1) := by
  intro side
  exact checked_arm_add_world W hs ht0 ht1
    (ihs (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih0 (CheckedLocalSideBases.ofBelowPair side.descendants.2.1))
    (ih1 (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_inner (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs : SValid Gamma s)
    (ihs : cMotiveSLocal Psi0 W Gamma s hs) :
    cMotiveHLocal Psi0 W ∅ Gamma (.inner s)
      (.space (.tprod (.dual s) (.dual s))) (.inner hs) := by
  intro side
  exact checked_arm_inner_world W hs
    (ihs (CheckedLocalSideS.ofBelowPair side.descendants))

private theorem local_real_lit (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (r : ℝ) :
    cMotiveHLocal Psi0 W ∅ Gamma (.real r) (.space .real) (.real_lit r) := by
  intro _side
  exact checked_arm_real_lit_world W r

private theorem local_app_linear (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (ht0 : HasType Delta0 Gamma e0 (.space (.tprod (.dual s0) s1)))
    (ht1 : HasType Delta1 Gamma e1 (.space s0))
    (ihs0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ihs1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ih0 : cMotiveHLocal Psi0 W Delta0 Gamma e0
      (.space (.tprod (.dual s0) s1)) ht0)
    (ih1 : cMotiveHLocal Psi0 W Delta1 Gamma e1 (.space s0) ht1) :
    cMotiveHLocal Psi0 W (Delta0 ∪ Delta1) Gamma (.appL s0 s1 e0 e1)
      (.space s1) (.app_linear hs0 hs1 hdisj ht0 ht1) := by
  intro side
  exact checked_arm_app_linear_world W hs0 hs1 hdisj ht0 ht1
    (ihs0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ihs1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ih0 (CheckedLocalSideBases.ofBelowPair side.descendants.2.2.1))
    (ih1 (CheckedLocalSideBases.ofBelowPair side.descendants.2.2.2))

private theorem local_app_inner (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs : SValid Gamma s) (hdisj : Finmap.Disjoint Delta0 Delta1)
    (ht0 : HasType Delta0 Gamma e0 (.space (.dual s)))
    (ht1 : HasType Delta1 Gamma e1 (.space s))
    (ihs : cMotiveSLocal Psi0 W Gamma s hs)
    (ih0 : cMotiveHLocal Psi0 W Delta0 Gamma e0 (.space (.dual s)) ht0)
    (ih1 : cMotiveHLocal Psi0 W Delta1 Gamma e1 (.space s) ht1) :
    cMotiveHLocal Psi0 W (Delta0 ∪ Delta1) Gamma (.appI s e0 e1)
      (.space .real) (.app_inner hs hdisj ht0 ht1) := by
  intro side
  exact checked_arm_app_inner_world W hs hdisj ht0 ht1
    (ihs (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih0 (CheckedLocalSideBases.ofBelowPair side.descendants.2.1))
    (ih1 (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_app_nonlinear (happCut : CheckedTyAtAppCut)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (ht0 : HasType ∅ Gamma e0 (.piTy tau0 tau1))
    (ht1 : HasType ∅ Gamma e1 tau0)
    (ih0 : cMotiveHLocal Psi0 W ∅ Gamma e0 (.piTy tau0 tau1) ht0)
    (ih1 : cMotiveHLocal Psi0 W ∅ Gamma e1 tau0 ht1) :
    cMotiveHLocal Psi0 W ∅ Gamma (.appN e0 e1)
      (Ty.instantiate e1 tau1) (.app_nonlinear ht0 ht1) := by
  intro side
  exact checked_arm_app_nonlinear_world_of_tyAt_appCut happCut W ht0 ht1
    (ih0 (CheckedLocalSideBases.ofBelowPair side.descendants.1))
    (ih1 (CheckedLocalSideBases.ofBelowPair side.descendants.2))

private theorem local_var_lin (hexact : CheckedExactBasisTyProgress)
    (Psi0 : EvalCtx) (hroot : CheckedStdStoreRoot Psi0) :
    cMotiveHLocal Psi0 (CheckedStdFuture Psi0)
      (Finmap.singleton x s) Gamma (.var x) (.space s) .var_lin := by
  intro side Psi hfuture hP hcov hwf
  exact checked_var_lin_of_rootFuture hexact hroot hfuture hP hcov hwf side

private theorem local_var_nlin (hexact : CheckedExactBasisTyProgress)
    (Psi0 : EvalCtx) (hroot : CheckedStdStoreRoot Psi0)
    (hGamma : Gamma.lookup x = some tau) :
    cMotiveHLocal Psi0 (CheckedStdFuture Psi0)
      ∅ Gamma (.var x) tau (.var_nlin hGamma) := by
  intro side Psi hfuture hP hcov hwf
  exact checked_var_nlin_of_rootFuture hexact hroot hfuture hGamma
    hP hcov hwf side

private theorem local_pinv_tensor (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (ht : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1)))
    (ihs0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ihs1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ih : cMotiveHLocal Psi0 W ∅ Gamma e
      (.space (.tprod (.dual s0) s1)) ht) :
    cMotiveHLocal Psi0 W ∅ Gamma (.pinvT s0 s1 e)
      (.space (.tprod (.dual s1) s0)) (.pinv_tensor hs0 hs1 ht) := by
  intro side
  exact checked_arm_pinv_tensor_world W hs0 hs1 ht
    (ihs0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ihs1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ih (CheckedLocalSideBases.ofBelowPair side.descendants.2.2))

private theorem local_pinv_dual (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs : SValid Gamma s)
    (ht : HasType ∅ Gamma e (.space (.dual s)))
    (ihs : cMotiveSLocal Psi0 W Gamma s hs)
    (ih : cMotiveHLocal Psi0 W ∅ Gamma e (.space (.dual s)) ht) :
    cMotiveHLocal Psi0 W ∅ Gamma (.pinvD s e)
      (.space (.tprod (.dual .real) s)) (.pinv_dual hs ht) := by
  intro side
  exact checked_arm_pinv_dual_world W hs ht
    (ihs (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ih (CheckedLocalSideBases.ofBelowPair side.descendants.2))

private theorem local_promote (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (lin : LCtx) (hdisjDelta : Finmap.Disjoint lin Delta)
    (hdisjGamma : Finmap.Disjoint lin.toNL Gamma)
    (hfresh : PromoteFresh lin Delta Gamma)
    (ht : HasType (lin ∪ Delta) Gamma e tau)
    (ih : cMotiveHLocal Psi0 W (lin ∪ Delta) Gamma e tau ht) :
    cMotiveHLocal Psi0 W Delta (lin.toNL ∪ Gamma) e tau
      (.promote lin hdisjDelta hdisjGamma hfresh ht) := by
  intro side
  exact checked_arm_promote_world W lin hdisjDelta hdisjGamma hfresh ht
    (ih side.promoteInner)

private theorem local_dsumE (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (ht0 : HasType Delta Gamma e0 (.space s0))
    (ht1 : HasType Delta Gamma e1 (.space s1))
    (ihs0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ihs1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ih0 : cMotiveHLocal Psi0 W Delta Gamma e0 (.space s0) ht0)
    (ih1 : cMotiveHLocal Psi0 W Delta Gamma e1 (.space s1) ht1) :
    cMotiveHLocal Psi0 W Delta Gamma (.dsumE e0 e1)
      (.space (.dsum s0 s1)) (.dsumE hs0 hs1 ht0 ht1) := by
  intro side
  exact checked_arm_dsumE_world W hs0 hs1 ht0 ht1
    (ihs0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ihs1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ih0 (CheckedLocalSideBases.ofBelowPair side.descendants.2.2.1))
    (ih1 (CheckedLocalSideBases.ofBelowPair side.descendants.2.2.2))

private theorem local_tprodE (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (ht0 : HasType Delta0 Gamma e0 (.space s0))
    (ht1 : HasType Delta1 Gamma e1 (.space s1))
    (ihs0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ihs1 : cMotiveSLocal Psi0 W Gamma s1 hs1)
    (ih0 : cMotiveHLocal Psi0 W Delta0 Gamma e0 (.space s0) ht0)
    (ih1 : cMotiveHLocal Psi0 W Delta1 Gamma e1 (.space s1) ht1) :
    cMotiveHLocal Psi0 W (Delta0 ∪ Delta1) Gamma (.tprodE e0 e1)
      (.space (.tprod s0 s1)) (.tprodE hs0 hs1 hdisj ht0 ht1) := by
  intro side
  exact checked_arm_tprodE_world W hs0 hs1 hdisj ht0 ht1
    (ihs0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ihs1 (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (ih0 (CheckedLocalSideBases.ofBelowPair side.descendants.2.2.1))
    (ih1 (CheckedLocalSideBases.ofBelowPair side.descendants.2.2.2))

private theorem local_llam_real (laws : CheckedRenameLaws)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop) (hclosed : StdExtensionClosed W)
    (L : Finset Name) (hs : SValid Gamma s)
    (hbody : ∀ y, y ∉ L → HasType (Finmap.insert y s Delta) Gamma
      (Term.openVar y e) (.space .real))
    (ihs : cMotiveSLocal Psi0 W Gamma s hs)
    (ihbody : ∀ y (hy : y ∉ L), cMotiveHLocal Psi0 W
      (Finmap.insert y s Delta) Gamma (Term.openVar y e) (.space .real)
      (hbody y hy)) :
    cMotiveHLocal Psi0 W Delta Gamma (.llam s .real e) (.space (.dual s))
      (.llam_real L hs hbody) := by
  intro side
  exact checked_arm_llam_real_world laws W hclosed L hs hbody
    (ihs (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (fun y hy => ihbody y hy
      (CheckedLocalSideBases.ofBelowPair (side.descendants.2 y hy)))

private theorem local_llam_tensor (laws : CheckedRenameLaws)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop) (hclosed : StdExtensionClosed W)
    (L : Finset Name) (hne : s ≠ .real)
    (hs0 : SValid Gamma s0) (hs : SValid Gamma s)
    (hbody : ∀ y, y ∉ L → HasType (Finmap.insert y s0 Delta) Gamma
      (Term.openVar y e) (.space s))
    (ihs0 : cMotiveSLocal Psi0 W Gamma s0 hs0)
    (ihs : cMotiveSLocal Psi0 W Gamma s hs)
    (ihbody : ∀ y (hy : y ∉ L), cMotiveHLocal Psi0 W
      (Finmap.insert y s0 Delta) Gamma (Term.openVar y e) (.space s)
      (hbody y hy)) :
    cMotiveHLocal Psi0 W Delta Gamma (.llam s0 s e)
      (.space (.tprod (.dual s0) s)) (.llam_tensor L hne hs0 hs hbody) := by
  intro side
  exact checked_arm_llam_tensor_world laws W hclosed L hne hs0 hs hbody
    (ihs0 (CheckedLocalSideS.ofBelowPair side.descendants.1))
    (ihs (CheckedLocalSideS.ofBelowPair side.descendants.2.1))
    (fun y hy => ihbody y hy
      (CheckedLocalSideBases.ofBelowPair (side.descendants.2.2 y hy)))

private theorem local_embed (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hsub : SubType Gamma s0 s1)
    (ih : cMotiveSubLocal Psi0 W Gamma s0 s1 hsub) :
    cMotiveHLocal Psi0 W ∅ Gamma (.embed s0)
      (.space (.tprod (.dual s0) s1)) (.embed hsub) := by
  intro side
  exact checked_arm_embed_world W hsub
    (ih (CheckedLocalSideSub.ofBelowPair side.descendants))

private theorem local_nllam (laws : CheckedRenameLaws)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop) (hclosed : StdExtensionClosed W)
    (L : Finset Name)
    (ht : TValid Gamma (.piTy tau0 tau1) (.arrow k0 k1))
    (hbody : ∀ y, y ∉ L → HasType ∅ (Finmap.insert y tau0 Gamma)
      (Term.openVar y e) (Ty.openVar y tau1))
    (ihT : cMotiveTLocal Psi0 W Gamma (.piTy tau0 tau1)
      (.arrow k0 k1) ht)
    (ihbody : ∀ y (hy : y ∉ L), cMotiveHLocal Psi0 W ∅
      (Finmap.insert y tau0 Gamma) (Term.openVar y e) (Ty.openVar y tau1)
      (hbody y hy)) :
    cMotiveHLocal Psi0 W ∅ Gamma (.nllam tau0 e) (.piTy tau0 tau1)
      (.nllam L ht hbody) := by
  intro side
  exact checked_arm_nllam_world laws W hclosed L ht hbody
    (ihT (CheckedLocalSideT.ofBelowPair side.descendants.1))
    (fun y hy => ihbody y hy
      (CheckedLocalSideBases.ofBelowPair (side.descendants.2 y hy)))

/-! ## Generated mutual master -/

/-- The complete checked standard-progress induction below one fixed root
evaluator.  The proof follows the generated four-way source recursor, so the
local side-basis tree and the recursive checked evaluation are indexed by the
same source derivation.  Binder recursion ranges only over standard-key
futures of `Psi0`; promotion keeps that world and reconstructs its smaller
source context constructively. -/
theorem checked_local_progress_master
    (laws : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    (hexact : CheckedExactBasisTyProgress)
    (Psi0 : EvalCtx) (hroot : CheckedStdStoreRoot Psi0) :
    (forall {Gamma : NLCtx} {s : Space} (h : SValid Gamma s),
      cMotiveSLocal Psi0 (CheckedStdFuture Psi0) Gamma s h) /\
    (forall {Gamma : NLCtx} {tau : Ty} {k : Kind}
      (h : TValid Gamma tau k),
      cMotiveTLocal Psi0 (CheckedStdFuture Psi0) Gamma tau k h) /\
    (forall {Gamma : NLCtx} {s0 s1 : Space}
      (h : SubType Gamma s0 s1),
      cMotiveSubLocal Psi0 (CheckedStdFuture Psi0) Gamma s0 s1 h) /\
    (forall {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
      (h : HasType Delta Gamma e tau),
      cMotiveHLocal Psi0 (CheckedStdFuture Psi0) Delta Gamma e tau h) := by
  have hclosed : StdExtensionClosed (CheckedStdFuture Psi0) :=
    checkedStdFuture_extensionClosed Psi0
  refine ⟨@fun Gamma s h => ?_, @fun Gamma tau k h => ?_,
    @fun Gamma s0 s1 h => ?_, @fun Delta Gamma e tau h => ?_⟩
  all_goals
    exact h.rec
      (motive_1 := fun Gamma' s' h' =>
        cMotiveSLocal Psi0 (CheckedStdFuture Psi0) Gamma' s' h')
      (motive_2 := fun Gamma' tau' k' h' =>
        cMotiveTLocal Psi0 (CheckedStdFuture Psi0) Gamma' tau' k' h')
      (motive_3 := fun Gamma' s0' s1' h' =>
        cMotiveSubLocal Psi0 (CheckedStdFuture Psi0) Gamma' s0' s1' h')
      (motive_4 := fun Delta' Gamma' e' tau' h' =>
        cMotiveHLocal Psi0 (CheckedStdFuture Psi0)
          Delta' Gamma' e' tau' h')
      -- SValid (9)
      (local_empty Psi0 _) (local_real Psi0 _) (local_dual Psi0 _)
      (local_dsum Psi0 _) (local_tprod Psi0 _) (local_ker Psi0 _)
      (local_coker Psi0 _) (local_img Psi0 _) (local_coimg Psi0 _)
      -- TValid (2)
      (local_ty_space Psi0 _)
      (local_ty_pi laws Psi0 _ hclosed)
      -- SubType (4)
      (local_sub_ker Psi0 _) (local_sub_coker Psi0 _)
      (local_sub_img Psi0 _) (local_sub_coimg Psi0 _)
      -- HasType (19)
      (local_zero Psi0 _) (local_smul Psi0 _) (local_add Psi0 _)
      (local_inner Psi0 _) (local_real_lit Psi0 _)
      (local_app_linear Psi0 _) (local_app_inner Psi0 _)
      (local_app_nonlinear happCut Psi0 _)
      (local_var_lin hexact Psi0 hroot)
      (local_var_nlin hexact Psi0 hroot)
      (local_pinv_tensor Psi0 _) (local_pinv_dual Psi0 _)
      (local_promote Psi0 _) (local_dsumE Psi0 _) (local_tprodE Psi0 _)
      (local_llam_real laws Psi0 _ hclosed)
      (local_llam_tensor laws Psi0 _ hclosed)
      (local_embed Psi0 _)
      (local_nllam laws Psi0 _ hclosed)

/-- Root specialization of the generated master.  This is the honest
standard-basis progress statement: its local basis certificate is indexed by
the chosen source typing derivation, and its result is a checked evaluation
constructed by progress. -/
theorem checked_std_progress_at_root
    (laws : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    (hexact : CheckedExactBasisTyProgress)
    {Psi : EvalCtx} (hroot : CheckedStdStoreRoot Psi)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (ht : HasType Delta Gamma e tau)
    (hside : CheckedLocalSideBases Psi ht)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered Delta Gamma Psi)
    (hwf : V2.CtxWF' Delta Gamma) :
    exists v tauv,
      C.Term Delta Gamma Psi e (Basis.std tau) v tauv := by
  exact (checked_local_progress_master laws happCut hexact Psi hroot).2.2.2
    ht hside Psi (CheckedStdFuture.refl Psi) hP hcov hwf

/-! ## Current store and requested-basis adapters -/

theorem checkedVarRecipeFrom_of_basisTransportWF
    (htransport : CheckedBasisTransportWF)
    (Psi0 : EvalCtx) (x : VName) (b : Basis) (v : ValExpr) :
    CheckedVarRecipeFrom Psi0 x b v := by
  unfold CheckedBasisTransportWF at htransport
  intro Psi _hsub Delta Gamma tauv hP hcov hstored hwf hbv hterm
  obtain ⟨k, ⟨htofValid⟩⟩ := hbv.tof_tvalid
  have hstdValid : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
    Basis.std_valid (Basis.tof b) htofValid
  obtain ⟨w, tauw, hw⟩ := htransport Delta Gamma Psi (.var x)
    b (Basis.std (Basis.tof b)) v tauv hP hcov hstored hwf hbv
    hterm.tyAt.isTyBasis hstdValid (Basis.isTyBasis_std (Basis.tof b))
    (Basis.tof_std (Basis.tof b)) hterm
  exact ⟨w, tauw, hw⟩

/-- A full checked transport proof is a concrete current entry builder.
The creation-time semantic payload is not needed here: the recipe accepts the
direct current-world checked variable node and transports that node using its
current `CtxWF'` evidence. -/
theorem checkedRawEntryBuilder_of_basisTransportWF
    (htransport : CheckedBasisTransportWF) : CheckedRawEntryBuilder := by
  intro orc Delta Gamma Psi GammaV sigma rho x b v tauv
    _hraw _hstore _hfresh _hbv _hisTy
  exact checkedVarRecipeFrom_of_basisTransportWF htransport
    (Psi.extend x b v) x b v

/-- Consequently `RawConsistent` supplies the complete checked root-store
package once checked basis transport is available. -/
theorem checkedStdStoreRoot_of_rawConsistent_and_transport
    (htransport : CheckedBasisTransportWF)
    (hraw : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    CheckedStdStoreRoot Psi :=
  checkedStdStoreRoot_of_rawConsistent
    (checkedRawEntryBuilder_of_basisTransportWF htransport) hraw

/-- Transport the root standard-progress result to a caller-selected basis.
The target value may differ from the standard-progress value, exactly as in
the operational change-of-basis rule, but the source term and requested basis
are literal in the conclusion. -/
theorem checked_progress_at_root_basis
    (laws : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    (hexact : CheckedExactBasisTyProgress)
    (htransport : CheckedBasisTransportWF)
    {Psi : EvalCtx} (hroot : CheckedStdStoreRoot Psi)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {b : Basis}
    (ht : HasType Delta Gamma e (Basis.tof b))
    (hside : CheckedLocalSideBases Psi ht)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered Delta Gamma Psi)
    (hwf : V2.CtxWF' Delta Gamma)
    (hb : Basis.BasisValid Gamma b)
    (hisTy : Basis.IsTyBasis b) :
    exists v tauv, C.Term Delta Gamma Psi e b v tauv := by
  unfold CheckedBasisTransportWF at htransport
  obtain ⟨v0, tauv0, hstd⟩ := checked_std_progress_at_root
    laws happCut hexact hroot ht hside hP hcov hwf
  obtain ⟨k, ⟨htof⟩⟩ := hb.tof_tvalid
  have hbstd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
    Basis.std_valid (Basis.tof b) htof
  exact htransport Delta Gamma Psi e (Basis.std (Basis.tof b)) b
    v0 tauv0 hP hcov.drop_lin hroot.storedWF hwf hbstd
    (Basis.isTyBasis_std (Basis.tof b)) hb hisTy
    (by simp only [Basis.tof_std]) hstd
