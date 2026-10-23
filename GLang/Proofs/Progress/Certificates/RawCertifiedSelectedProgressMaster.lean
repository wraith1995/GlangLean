import GLang.Proofs.Progress.MutualCertificates
import GLang.Proofs.Progress.Certificates.RawCertifiedWorldProgressArms
import GLang.Proofs.Progress.Certificates.RawCertifiedWorldBoundaryProgress
import GLang.Proofs.Progress.Certificates.RawCertifiedPiBasisTransport

/-!
# Selected-basis checked progress master

This is the source half of the fuel-indexed checked progress/COB mutual.
It is deliberately parametric in the property required of a basis selected
by a variable leaf.  The two variable callbacks are the only consumers of
that property; all other source constructors are discharged by the existing
checked world arms.

The richer `CheckedLocalSide*With` trees pair the already reviewed shallow
rule-local validity evidence with the selected-basis evidence at every
variable descendant.  There are no axioms or admissions in this module.
-/

namespace GLang
namespace RawCertifiedSelectedProgressMaster

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore
open RawCertifiedWorldBinderProgress
open RawCertifiedWorldProgressArms
open RawCertifiedWorldBoundaryProgress
open RawCertifiedPiBasisTransport
open RawCertifiedCobProgressMutualSpike

/-! ## Repackaging immediate descendants -/

private def sideSOfPairs
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {W : EvalCtx → Prop}
    {Gamma : NLCtx} {s : Space} {h : SValid Gamma s}
    (shallow : PProd True
      (SValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi0 he) h))
    (deep : PProd True
      (SValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWithWorld selected Psi0 W he) h)) :
    CheckedLocalSideSWithWorld selected Psi0 W h :=
  { shallow := CheckedLocalSideS.ofBelowPair shallow
    deep := deep.2 }

private def sideTOfPairs
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {W : EvalCtx → Prop}
    {Gamma : NLCtx} {tau : Ty} {k : Kind} {h : TValid Gamma tau k}
    (shallow : PProd True
      (TValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi0 he) h))
    (deep : PProd True
      (TValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWithWorld selected Psi0 W he) h)) :
    CheckedLocalSideTWithWorld selected Psi0 W h :=
  { shallow := CheckedLocalSideT.ofBelowPair shallow
    deep := deep.2 }

private def sideSubOfPairs
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {W : EvalCtx → Prop}
    {Gamma : NLCtx} {s0 s1 : Space} {h : SubType Gamma s0 s1}
    (shallow : PProd True
      (SubType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi0 he) h))
    (deep : PProd True
      (SubType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWithWorld selected Psi0 W he) h)) :
    CheckedLocalSideSubWithWorld selected Psi0 W h :=
  { shallow := CheckedLocalSideSub.ofBelowPair shallow
    deep := deep.2 }

private def sideHOfPairs
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {W : EvalCtx → Prop}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau}
    (shallow : PProd (CheckedLocalTermSideBasis Psi0 h)
      (HasType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi0 he) h))
    (deep : PProd (CheckedLocalTermSideBasisWithWorld selected Psi0 W h)
      (HasType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWithWorld selected Psi0 W he) h)) :
    CheckedLocalSideBasesWithWorld selected Psi0 W h :=
  { shallow := CheckedLocalSideBases.ofBelowPair shallow
    deepHere := deep.1
    deepDescendants := deep.2 }

private def sideHPromoteInner
    {selected : CheckedSelectedBasisSide} {Psi0 : EvalCtx}
    {W : EvalCtx → Prop}
    {Delta lin : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {hdisjDelta : Finmap.Disjoint lin Delta}
    {hdisjGamma : Finmap.Disjoint lin.toNL Gamma}
    {hfresh : PromoteFresh lin Delta Gamma}
    {hinner : HasType (lin ∪ Delta) Gamma e tau}
    (side : CheckedLocalSideBasesWithWorld selected Psi0 W
      (.promote lin hdisjDelta hdisjGamma hfresh hinner)) :
    CheckedLocalSideBasesWithWorld selected Psi0 W hinner :=
  { shallow := side.shallow.promoteInner
    deepHere := side.deepDescendants.1
    deepDescendants := side.deepDescendants.2 }

/-! ## Parametric motives and the two genuine variable seams -/

def cMotiveSSelected (selected : CheckedSelectedBasisSide)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (Gamma : NLCtx) (s : Space) (h : SValid Gamma s) : Prop :=
  CheckedLocalSideSWithWorld selected Psi0 W h → cMotiveSWorld W Gamma s

def cMotiveTSelected (selected : CheckedSelectedBasisSide)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (Gamma : NLCtx) (tau : Ty) (k : Kind) (h : TValid Gamma tau k) : Prop :=
  CheckedLocalSideTWithWorld selected Psi0 W h → cMotiveTWorld W Gamma tau

def cMotiveSubSelected (selected : CheckedSelectedBasisSide)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (Gamma : NLCtx) (s0 s1 : Space) (h : SubType Gamma s0 s1) : Prop :=
  CheckedLocalSideSubWithWorld selected Psi0 W h → cMotiveSubWorld W Gamma s0 s1

def cMotiveHSelected (selected : CheckedSelectedBasisSide)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (Delta : LCtx) (Gamma : NLCtx) (e : Term) (tau : Ty)
    (h : HasType Delta Gamma e tau) : Prop :=
  CheckedLocalSideBasesWithWorld selected Psi0 W h →
    cMotiveHWorld W Delta Gamma e tau

/-- The source recursion is generic except for its two evaluator lookup
leaves.  A depth layer later instantiates these callbacks from the scoped
exact-type and basis-transport constructions of the preceding layer. -/
structure CheckedSelectedVarArms
    (selected : CheckedSelectedBasisSide)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop) : Prop where
  lin : forall {Gamma : NLCtx} {x : VName} {s : Space},
    cMotiveHSelected selected Psi0 W
      (Finmap.singleton x s) Gamma (.var x) (.space s) .var_lin
  nlin : forall {Gamma : NLCtx} {x : VName} {tau : Ty}
      (hGamma : Gamma.lookup x = some tau),
    cMotiveHSelected selected Psi0 W
      (∅ : LCtx) Gamma (.var x) tau (.var_nlin hGamma)

/-- The term projection at an arbitrary selected-basis layer and evaluator
world relation. -/
def CheckedTermProgressWithWorld
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx)
    (W : EvalCtx → Prop) : Prop :=
  forall {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau),
    cMotiveHSelected selected Psi0 W Delta Gamma e tau h

/-- Backwards-compatible standard-future specialization. -/
abbrev CheckedTermProgressWith
    (selected : CheckedSelectedBasisSide) (Psi0 : EvalCtx) : Prop :=
  CheckedTermProgressWithWorld selected Psi0 (CheckedStdFuture Psi0)

/-- Fuel-indexed spelling consumed by checked COB at the next basis layer. -/
abbrev CheckedTermProgressDepth (Psi0 : EvalCtx) (n : Nat) : Prop :=
  CheckedTermProgressWith (CheckedSelectedBasisAt Psi0 n) Psi0

/-- Exact checked type realization for bases admitted at one depth. -/
def CheckedExactBasisTyProgressDepth (Psi0 : EvalCtx) (n : Nat) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    (hb : Basis.BasisValid Gamma b),
    CheckedStdFuture Psi0 Psi ->
    CheckedLocalSideBasisDepth Psi0 n hb ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> forall (Delta : LCtx), V2.CtxWF' Delta Gamma ->
    Basis.IsTyBasis b -> exists tauv, C.TyAt Gamma Psi b tauv

/-- Checked transport from an admitted basis to its literal standard basis.
The source checked term supplies the source exact-type certificate; the
proof-indexed side tree supplies every recursive COB/source call. -/
def CheckedBasisToStdDepth (Psi0 : EvalCtx) (n : Nat) : Prop :=
  forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauv : ValTy}
    (hb : Basis.BasisValid Gamma b),
    CheckedStdFuture Psi0 Psi ->
    CheckedLocalSideBasisDepth Psi0 n hb ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
    C.Term Delta Gamma Psi e b v tauv ->
    exists w tauw,
      C.Term Delta Gamma Psi e (Basis.std (Basis.tof b)) w tauw

/-! ## The two variable layers -/

/-- At source depth zero an actual evaluator lookup contradicts the
future-aware `NoCheckedSelectedBasis` certificate.  This closes both
variable constructors without a semantic premise. -/
theorem checkedSelectedVarArms_zero (Psi0 : EvalCtx) :
    CheckedSelectedVarArms (CheckedSelectedBasisAt Psi0 0)
      Psi0 (CheckedStdFuture Psi0) := by
  constructor
  · intro Gamma x s side Psi hfuture _hP hcov _hwf
    obtain ⟨b, v, hlookup, _htof, _hb, hfalse⟩ :=
      (side.deepHere Psi hfuture).1 hcov
    exact False.elim hfalse
  · intro Gamma x tau hGamma side Psi hfuture _hP hcov _hwf
    obtain ⟨b, v, hlookup, _htof, _hb, hfalse⟩ :=
      (side.deepHere Psi hfuture).1 hcov
    exact False.elim hfalse

/-- At source depth `n+1`, the future-aware leaf certificate supplies the
selected basis at depth `n`, regardless of whether the key belongs to the
raw root or was introduced by a checked binder.  Exact realization builds
the direct variable node and checked transport standardizes that same node. -/
theorem checkedSelectedVarArms_succ
    (Psi0 : EvalCtx) (n : Nat)
    (hrootStored : V2.StoredWF Psi0)
    (hexact : CheckedExactBasisTyProgressDepth Psi0 n)
    (htransport : CheckedBasisToStdDepth Psi0 n) :
    CheckedSelectedVarArms (CheckedSelectedBasisAt Psi0 (n + 1))
      Psi0 (CheckedStdFuture Psi0) := by
  constructor
  · intro Gamma x s side Psi hfuture hP hcov hwf
    obtain ⟨b, v, hlookup, htof, hb, hdepth⟩ :=
      (side.deepHere Psi hfuture).1 hcov
    have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
    have hstored : V2.StoredWF Psi := hfuture.storedWF hrootStored
    have hisTy : Basis.IsTyBasis b := hstored x b hmem
    obtain ⟨tauv, htyAt⟩ := hexact hb hfuture hdepth hP
      hcov.drop_lin hstored (Finmap.singleton x s) hwf hisTy
    have hdirect : C.Term (Finmap.singleton x s) Gamma Psi
        (.var x) b v tauv :=
      .var_lin hlookup htof hb htyAt
    obtain ⟨w, tauw, hstd⟩ := htransport hb hfuture hdepth hP
      hcov.drop_lin hstored hwf hdirect
    rw [htof] at hstd
    exact ⟨w, tauw, hstd⟩
  · intro Gamma x tau hGamma side Psi hfuture hP hcov hwf
    obtain ⟨b, v, hlookup, htof, hb, hdepth⟩ :=
      (side.deepHere Psi hfuture).1 hcov
    have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
    have hstored : V2.StoredWF Psi := hfuture.storedWF hrootStored
    have hisTy : Basis.IsTyBasis b := hstored x b hmem
    obtain ⟨tauv, htyAt⟩ := hexact hb hfuture hdepth hP hcov
      hstored (∅ : LCtx) hwf hisTy
    have hGamma' : Gamma.lookup x = some (Basis.tof b) := by
      rw [htof]
      exact hGamma
    have hdirect : C.Term (∅ : LCtx) Gamma Psi (.var x) b v tauv :=
      .var_nlin hlookup hGamma' hb htyAt
    obtain ⟨w, tauw, hstd⟩ := htransport hb hfuture hdepth hP hcov
      hstored hwf hdirect
    rw [htof] at hstd
    exact ⟨w, tauw, hstd⟩

/-! ## Generated four-way source induction -/

/-- The generated four-way recursor specialized to its term projection.  It
still supplies handlers for all 34 mutually recursive source constructors;
only the two variable leaves are provided by `vars`.  This is the projection
consumed by the depth-layered COB construction. -/
theorem checked_selected_term_progress
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (selected : CheckedSelectedBasisSide)
    (Psi0 : EvalCtx) (W : EvalCtx → Prop)
    (hclosed : StdExtensionClosed W)
    (vars : CheckedSelectedVarArms selected Psi0 W) :
    forall {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
      (h : HasType Delta Gamma e tau),
      cMotiveHSelected selected Psi0 W Delta Gamma e tau h := by
  intro Delta Gamma e tau h
  apply HasType.rec
      (motive_1 := fun Gamma' s' h' =>
        cMotiveSSelected selected Psi0 W Gamma' s' h')
      (motive_2 := fun Gamma' tau' k' h' =>
        cMotiveTSelected selected Psi0 W Gamma' tau' k' h')
      (motive_3 := fun Gamma' s0' s1' h' =>
        cMotiveSubSelected selected Psi0 W Gamma' s0' s1' h')
      (motive_4 := fun Delta' Gamma' e' tau' h' =>
        cMotiveHSelected selected Psi0 W Delta' Gamma' e' tau' h')
  case empty =>
        intro _Gamma _side
        exact checked_arm_empty_world W
  case real =>
        intro _Gamma _side
        exact checked_arm_real_world W
  case dual =>
        intro _Gamma _s hs ih side
        exact checked_arm_dual_world W hs
          (ih (sideSOfPairs side.shallow.descendants side.deep))
  case dsum =>
        intro _Gamma _s0 _s1 hs0 hs1 ih0 ih1 side
        exact checked_arm_dsum_world W hs0 hs1
          (ih0 (sideSOfPairs side.shallow.descendants.1 side.deep.1))
          (ih1 (sideSOfPairs side.shallow.descendants.2 side.deep.2))
  case tprod =>
        intro _Gamma _s0 _s1 hs0 hs1 ih0 ih1 side
        exact checked_arm_tprod_world W hs0 hs1
          (ih0 (sideSOfPairs side.shallow.descendants.1 side.deep.1))
          (ih1 (sideSOfPairs side.shallow.descendants.2 side.deep.2))
  case ker =>
        intro _Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe side
        exact checked_arm_ker_world W hs0 hs1 he
          (ih0 (sideSOfPairs side.shallow.descendants.1 side.deep.1))
          (ih1 (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
          (ihe (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case coker =>
        intro _Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe side
        exact checked_arm_coker_world W hs0 hs1 he
          (ih0 (sideSOfPairs side.shallow.descendants.1 side.deep.1))
          (ih1 (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
          (ihe (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case img =>
        intro _Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe side
        exact checked_arm_img_world W hs0 hs1 he
          (ih0 (sideSOfPairs side.shallow.descendants.1 side.deep.1))
          (ih1 (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
          (ihe (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case coimg =>
        intro _Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe side
        exact checked_arm_coimg_world W hs0 hs1 he
          (ih0 (sideSOfPairs side.shallow.descendants.1 side.deep.1))
          (ih1 (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
          (ihe (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case space =>
        intro _Gamma _s hs ih side
        exact checked_arm_ty_space_world W hs
          (ih (sideSOfPairs side.shallow.descendants side.deep))
  case piTy =>
        intro _Gamma _tau0 _tau1 _k0 _k1 L ht0 ht1 ih0 ih1 side
        exact checked_arm_ty_pi_world laws W hclosed L ht0 ht1
          (ih0 (sideTOfPairs side.shallow.descendants.1 side.deep.1))
          (fun y hy => ih1 y hy
            (sideTOfPairs (side.shallow.descendants.2 y hy)
              (side.deep.2 y hy)))
  case sub_ker =>
        intro _Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe side
        exact checked_arm_sub_ker_world W hs0 hs1 he
          (ih0 (sideSOfPairs side.shallow.descendants.1 side.deep.1))
          (ih1 (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
          (ihe (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case sub_coker =>
        intro _Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe side
        exact checked_arm_sub_coker_world W hs0 hs1 he
          (ih0 (sideSOfPairs side.shallow.descendants.1 side.deep.1))
          (ih1 (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
          (ihe (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case sub_img =>
        intro _Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe side
        exact checked_arm_sub_img_world W hs0 hs1 he
          (ih0 (sideSOfPairs side.shallow.descendants.1 side.deep.1))
          (ih1 (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
          (ihe (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case sub_coimg =>
        intro _Gamma _e _s0 _s1 hs0 hs1 he ih0 ih1 ihe side
        exact checked_arm_sub_coimg_world W hs0 hs1 he
          (ih0 (sideSOfPairs side.shallow.descendants.1 side.deep.1))
          (ih1 (sideSOfPairs side.shallow.descendants.2.1 side.deep.2.1))
          (ihe (sideHOfPairs side.shallow.descendants.2.2 side.deep.2.2))
  case zero =>
        intro _Delta _Gamma _s hs ihs side
        exact checked_arm_zero_world W hs
          (ihs (sideSOfPairs side.shallow.descendants side.deepDescendants))
  case smul =>
        intro _Delta0 _Delta1 _Gamma _e0 _e1 _s
          hs hd ht0 ht1 ihs ih0 ih1 side
        exact checked_arm_smul_world W hs hd ht0 ht1
          (ihs (sideSOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (ih0 (sideHOfPairs side.shallow.descendants.2.1
            side.deepDescendants.2.1))
          (ih1 (sideHOfPairs side.shallow.descendants.2.2
            side.deepDescendants.2.2))
  case add =>
        intro _Delta _Gamma _e0 _e1 _s hs ht0 ht1 ihs ih0 ih1 side
        exact checked_arm_add_world W hs ht0 ht1
          (ihs (sideSOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (ih0 (sideHOfPairs side.shallow.descendants.2.1
            side.deepDescendants.2.1))
          (ih1 (sideHOfPairs side.shallow.descendants.2.2
            side.deepDescendants.2.2))
  case inner =>
        intro _Gamma _s hs ihs side
        exact checked_arm_inner_world W hs
          (ihs (sideSOfPairs side.shallow.descendants side.deepDescendants))
  case real_lit =>
        intro _Gamma r _side
        exact checked_arm_real_lit_world W r
  case app_linear =>
        intro _Delta0 _Delta1 _Gamma _e0 _e1 _s0 _s1
          hs0 hs1 hd ht0 ht1 ihs0 ihs1 ih0 ih1 side
        exact checked_arm_app_linear_world W hs0 hs1 hd ht0 ht1
          (ihs0 (sideSOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (ihs1 (sideSOfPairs side.shallow.descendants.2.1
            side.deepDescendants.2.1))
          (ih0 (sideHOfPairs side.shallow.descendants.2.2.1
            side.deepDescendants.2.2.1))
          (ih1 (sideHOfPairs side.shallow.descendants.2.2.2
            side.deepDescendants.2.2.2))
  case app_inner =>
        intro _Delta0 _Delta1 _Gamma _e0 _e1 _s
          hs hd ht0 ht1 ihs ih0 ih1 side
        exact checked_arm_app_inner_world W hs hd ht0 ht1
          (ihs (sideSOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (ih0 (sideHOfPairs side.shallow.descendants.2.1
            side.deepDescendants.2.1))
          (ih1 (sideHOfPairs side.shallow.descendants.2.2
            side.deepDescendants.2.2))
  case app_nonlinear =>
        intro _Gamma _e0 _e1 _tau0 _tau1 ht0 ht1 ih0 ih1 side
        exact checked_arm_app_nonlinear_world_of_tyAt_appCut happCut W ht0 ht1
          (ih0 (sideHOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (ih1 (sideHOfPairs side.shallow.descendants.2
            side.deepDescendants.2))
  case var_lin =>
        intro _Gamma _x _s
        exact vars.lin
  case var_nlin =>
        intro _Gamma _x _tau hGamma
        exact vars.nlin hGamma
  case pinv_tensor =>
        intro _Gamma _e _s0 _s1 hs0 hs1 ht ihs0 ihs1 ih side
        exact checked_arm_pinv_tensor_world W hs0 hs1 ht
          (ihs0 (sideSOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (ihs1 (sideSOfPairs side.shallow.descendants.2.1
            side.deepDescendants.2.1))
          (ih (sideHOfPairs side.shallow.descendants.2.2
            side.deepDescendants.2.2))
  case pinv_dual =>
        intro _Gamma _e _s hs ht ihs ih side
        exact checked_arm_pinv_dual_world W hs ht
          (ihs (sideSOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (ih (sideHOfPairs side.shallow.descendants.2
            side.deepDescendants.2))
  case promote =>
        intro _Delta _Gamma _e _tau lin hdDelta hdGamma hfresh ht ih side
        exact checked_arm_promote_world W lin hdDelta hdGamma hfresh ht
          (ih (sideHPromoteInner side))
  case dsumE =>
        intro _Delta _Gamma _e0 _e1 _s0 _s1
          hs0 hs1 ht0 ht1 ihs0 ihs1 ih0 ih1 side
        exact checked_arm_dsumE_world W hs0 hs1 ht0 ht1
          (ihs0 (sideSOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (ihs1 (sideSOfPairs side.shallow.descendants.2.1
            side.deepDescendants.2.1))
          (ih0 (sideHOfPairs side.shallow.descendants.2.2.1
            side.deepDescendants.2.2.1))
          (ih1 (sideHOfPairs side.shallow.descendants.2.2.2
            side.deepDescendants.2.2.2))
  case tprodE =>
        intro _Delta0 _Delta1 _Gamma _e0 _e1 _s0 _s1
          hs0 hs1 hd ht0 ht1 ihs0 ihs1 ih0 ih1 side
        exact checked_arm_tprodE_world W hs0 hs1 hd ht0 ht1
          (ihs0 (sideSOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (ihs1 (sideSOfPairs side.shallow.descendants.2.1
            side.deepDescendants.2.1))
          (ih0 (sideHOfPairs side.shallow.descendants.2.2.1
            side.deepDescendants.2.2.1))
          (ih1 (sideHOfPairs side.shallow.descendants.2.2.2
            side.deepDescendants.2.2.2))
  case llam_real =>
        intro _Delta _Gamma _s _e L hs hbody ihs ihbody side
        exact checked_arm_llam_real_world laws W hclosed L hs hbody
          (ihs (sideSOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (fun y hy => ihbody y hy
            (sideHOfPairs (side.shallow.descendants.2 y hy)
              (side.deepDescendants.2 y hy)))
  case llam_tensor =>
        intro _Delta _Gamma _s0 _s _e L hne hs0 hs hbody ihs0 ihs ihbody side
        exact checked_arm_llam_tensor_world laws W hclosed L hne hs0 hs hbody
          (ihs0 (sideSOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (ihs (sideSOfPairs side.shallow.descendants.2.1
            side.deepDescendants.2.1))
          (fun y hy => ihbody y hy
            (sideHOfPairs (side.shallow.descendants.2.2 y hy)
              (side.deepDescendants.2.2 y hy)))
  case embed =>
        intro _Gamma _s0 _s1 hsub ih side
        exact checked_arm_embed_world W hsub
          (ih (sideSubOfPairs side.shallow.descendants
            side.deepDescendants))
  case nllam =>
        intro _Gamma _tau0 _tau1 _k0 _k1 _e L ht hbody ihT ihbody side
        exact checked_arm_nllam_world laws W hclosed L ht hbody
          (ihT (sideTOfPairs side.shallow.descendants.1
            side.deepDescendants.1))
          (fun y hy => ihbody y hy
            (sideHOfPairs (side.shallow.descendants.2 y hy)
              (side.deepDescendants.2 y hy)))

/-- Root/future specialization used by the Nat-layer construction. -/
theorem checked_term_progress_depth_of_varArms
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (Psi0 : EvalCtx) (n : Nat)
    (vars : CheckedSelectedVarArms (CheckedSelectedBasisAt Psi0 n)
      Psi0 (CheckedStdFuture Psi0)) :
    CheckedTermProgressDepth Psi0 n := by
  exact checked_selected_term_progress laws happCut
    (CheckedSelectedBasisAt Psi0 n) Psi0 (CheckedStdFuture Psi0)
    (checkedStdFuture_extensionClosed Psi0) vars

/-- The source base layer is constructive: its certificate rules out every
actual variable selection. -/
theorem checked_term_progress_depth_zero
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (Psi0 : EvalCtx) : CheckedTermProgressDepth Psi0 0 := by
  exact checked_term_progress_depth_of_varArms laws happCut Psi0 0
    (checkedSelectedVarArms_zero Psi0)

/-- Successor source progress, exposing exactly the two depth-`n` services
used by its variable leaves. -/
theorem checked_term_progress_depth_succ
    (laws : CheckedRenameLaws) (happCut : CheckedTyAtAppCut)
    (Psi0 : EvalCtx) (n : Nat)
    (hrootStored : V2.StoredWF Psi0)
    (hexact : CheckedExactBasisTyProgressDepth Psi0 n)
    (htransport : CheckedBasisToStdDepth Psi0 n) :
    CheckedTermProgressDepth Psi0 (n + 1) := by
  exact checked_term_progress_depth_of_varArms laws happCut Psi0 (n + 1)
    (checkedSelectedVarArms_succ Psi0 n hrootStored hexact htransport)

end RawCertifiedSelectedProgressMaster
end GLang
