import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairDepthMonotonicity
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedFutureLookupValidity

/-!
# Re-rooting concrete pair certificates at standard futures

A pair certificate rooted at `Psi0` remains usable when the current root is
any `CheckedStdFuture` of `Psi0`.  The nontrivial point is source-side evidence:
its shallow field mentions the exact root, while its hereditary field already
covers every standard future.  The helpers below rebuild the shallow field at
the new root from that hereditary field, restrict future quantification by
transitivity, and map the selected-basis predicate.
-/

namespace GLang
namespace RawCertifiedPairFutureRebase

open OperationalStrengthening
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate
open RawCertifiedPairDepthMonotonicity

private abbrev TermProperty :=
  {Delta : LCtx} -> {Gamma : NLCtx} -> {e : Term} -> {tau : Ty} ->
    HasType Delta Gamma e tau -> Prop

private abbrev BelowS (P : TermProperty)
    {Gamma : NLCtx} {s : Space} (h : SValid Gamma s) :=
  @SValid.below
    (fun _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ he => P he)
    Gamma s h

private abbrev BelowT (P : TermProperty)
    {Gamma : NLCtx} {tau : Ty} {k : Kind} (h : TValid Gamma tau k) :=
  @TValid.below
    (fun _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ he => P he)
    Gamma tau k h

private abbrev BelowSub (P : TermProperty)
    {Gamma : NLCtx} {s0 s1 : Space} (h : SubType Gamma s0 s1) :=
  @SubType.below
    (fun _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ he => P he)
    Gamma s0 s1 h

private abbrev BelowH (P : TermProperty)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) :=
  @HasType.below
    (fun _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ he => P he)
    Delta Gamma e tau h

/-! A single structural mapper suffices both to restrict the hereditary tree
and to rebuild the exact-root shallow tree. -/

mutual

private def belowS_map
    {P Q : TermProperty}
    (mapTerm : forall {Delta Gamma e tau}
      {h : HasType Delta Gamma e tau}, P h -> Q h)
    {Gamma : NLCtx} {s : Space} {h : SValid Gamma s} :
    BelowS P h -> BelowS Q h :=
  match h with
  | .empty => fun _ => ⟨⟩
  | .real => fun _ => ⟨⟩
  | .dual _ => fun side =>
      ⟨side.1, belowS_map (P := P) (Q := Q) mapTerm side.2⟩
  | .dsum _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨side.2.1, belowS_map (P := P) (Q := Q) mapTerm side.2.2⟩⟩
  | .tprod _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨side.2.1, belowS_map (P := P) (Q := Q) mapTerm side.2.2⟩⟩
  | .ker _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1,
            belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩
  | .coker _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1,
            belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩
  | .img _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1,
            belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩
  | .coimg _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1,
            belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1,
            belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩

private def belowT_map
    {P Q : TermProperty}
    (mapTerm : forall {Delta Gamma e tau}
      {h : HasType Delta Gamma e tau}, P h -> Q h)
    {Gamma : NLCtx} {tau : Ty} {k : Kind} {h : TValid Gamma tau k} :
    BelowT P h -> BelowT Q h :=
  match h with
  | .space _ => fun side =>
      ⟨side.1, belowS_map (P := P) (Q := Q) mapTerm side.2⟩
  | .piTy _ _ _ => fun side =>
      ⟨⟨side.1.1, belowT_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        fun y hy =>
          ⟨(side.2 y hy).1, belowT_map (P := P) (Q := Q) mapTerm (side.2 y hy).2⟩⟩

private def belowSub_map
    {P Q : TermProperty}
    (mapTerm : forall {Delta Gamma e tau}
      {h : HasType Delta Gamma e tau}, P h -> Q h)
    {Gamma : NLCtx} {s0 s1 : Space} {h : SubType Gamma s0 s1} :
    BelowSub P h -> BelowSub Q h :=
  match h with
  | .sub_ker _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1,
            belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩
  | .sub_coker _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1,
            belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩
  | .sub_img _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1,
            belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩
  | .sub_coimg _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1,
            belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩

private def belowH_map
    {P Q : TermProperty}
    (mapTerm : forall {Delta Gamma e tau}
      {h : HasType Delta Gamma e tau}, P h -> Q h)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau} :
    BelowH P h -> BelowH Q h :=
  match h with
  | .zero _ => fun side =>
      ⟨side.1, belowS_map (P := P) (Q := Q) mapTerm side.2⟩
  | .smul _ _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨mapTerm side.2.1.1, belowH_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1, belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩
  | .add _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨mapTerm side.2.1.1, belowH_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1, belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩
  | .inner _ => fun side =>
      ⟨side.1, belowS_map (P := P) (Q := Q) mapTerm side.2⟩
  | .real_lit _ => fun _ => ⟨⟩
  | .app_linear _ _ _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨⟨mapTerm side.2.2.1.1,
              belowH_map (P := P) (Q := Q) mapTerm side.2.2.1.2⟩,
            ⟨mapTerm side.2.2.2.1,
              belowH_map (P := P) (Q := Q) mapTerm side.2.2.2.2⟩⟩⟩⟩
  | .app_inner _ _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨mapTerm side.2.1.1, belowH_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1, belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩
  | .app_nonlinear _ _ => fun side =>
      ⟨⟨mapTerm side.1.1, belowH_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨mapTerm side.2.1, belowH_map (P := P) (Q := Q) mapTerm side.2.2⟩⟩
  | .var_lin => fun _ => ⟨⟩
  | .var_nlin _ => fun _ => ⟨⟩
  | .pinv_tensor _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨mapTerm side.2.2.1, belowH_map (P := P) (Q := Q) mapTerm side.2.2.2⟩⟩⟩
  | .pinv_dual _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨mapTerm side.2.1, belowH_map (P := P) (Q := Q) mapTerm side.2.2⟩⟩
  | .promote _ _ _ _ _ => fun side =>
      ⟨mapTerm side.1, belowH_map (P := P) (Q := Q) mapTerm side.2⟩
  | .dsumE _ _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨⟨mapTerm side.2.2.1.1,
              belowH_map (P := P) (Q := Q) mapTerm side.2.2.1.2⟩,
            ⟨mapTerm side.2.2.2.1,
              belowH_map (P := P) (Q := Q) mapTerm side.2.2.2.2⟩⟩⟩⟩
  | .tprodE _ _ _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          ⟨⟨mapTerm side.2.2.1.1,
              belowH_map (P := P) (Q := Q) mapTerm side.2.2.1.2⟩,
            ⟨mapTerm side.2.2.2.1,
              belowH_map (P := P) (Q := Q) mapTerm side.2.2.2.2⟩⟩⟩⟩
  | .llam_real _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        fun y hy =>
          ⟨mapTerm (side.2 y hy).1,
            belowH_map (P := P) (Q := Q) mapTerm (side.2 y hy).2⟩⟩
  | .llam_tensor _ _ _ _ _ => fun side =>
      ⟨⟨side.1.1, belowS_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        ⟨⟨side.2.1.1, belowS_map (P := P) (Q := Q) mapTerm side.2.1.2⟩,
          fun y hy =>
            ⟨mapTerm (side.2.2 y hy).1,
              belowH_map (P := P) (Q := Q) mapTerm (side.2.2 y hy).2⟩⟩⟩
  | .embed _ => fun side =>
      ⟨side.1, belowSub_map (P := P) (Q := Q) mapTerm side.2⟩
  | .nllam _ _ _ => fun side =>
      ⟨⟨side.1.1, belowT_map (P := P) (Q := Q) mapTerm side.1.2⟩,
        fun y hy =>
          ⟨mapTerm (side.2 y hy).1,
            belowH_map (P := P) (Q := Q) mapTerm (side.2 y hy).2⟩⟩

end

theorem termSide_restrict
    {p q : CheckedSelectedBasisSide}
    {Psi0 Psi1 : EvalCtx} {W0 W1 : EvalCtx -> Prop}
    (hpq : SelectedLe p q)
    (hW : forall Psi, W1 Psi -> W0 Psi)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau} :
    CheckedLocalTermSideBasisWithWorld p Psi0 W0 h ->
      CheckedLocalTermSideBasisWithWorld q Psi1 W1 h := by
  apply HasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ h =>
      CheckedLocalTermSideBasisWithWorld p Psi0 W0 h ->
        CheckedLocalTermSideBasisWithWorld q Psi1 W1 h)
  case var_lin =>
    intro Gamma x s side
    simp only [CheckedLocalTermSideBasisWithWorld] at side ⊢
    intro Psi hW1
    obtain ⟨choose, hall⟩ := side Psi (hW Psi hW1)
    refine ⟨?_, hall⟩
    intro hcov
    obtain ⟨b, v, hlookup, htof, hb, hold⟩ := choose hcov
    exact ⟨b, v, hlookup, htof, hb, hpq hb hold⟩
  case var_nlin =>
    intro Gamma x tau hlookupGamma side
    simp only [CheckedLocalTermSideBasisWithWorld] at side ⊢
    intro Psi hW1
    obtain ⟨choose, hall⟩ := side Psi (hW Psi hW1)
    refine ⟨?_, hall⟩
    intro hcov
    obtain ⟨b, v, hlookup, htof, hb, hold⟩ := choose hcov
    exact ⟨b, v, hlookup, htof, hb, hpq hb hold⟩
  all_goals
    intros
    trivial

theorem termSide_toShallow
    {p : CheckedSelectedBasisSide}
    {Psi0 Psi1 : EvalCtx} {W : EvalCtx -> Prop}
    (hroot : W Psi1)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau} :
    CheckedLocalTermSideBasisWithWorld p Psi0 W h ->
      CheckedLocalTermSideBasis Psi1 h := by
  apply HasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ h =>
      CheckedLocalTermSideBasisWithWorld p Psi0 W h ->
        CheckedLocalTermSideBasis Psi1 h)
  case var_lin =>
    intro Gamma x s side
    simp only [CheckedLocalTermSideBasisWithWorld,
      CheckedLocalTermSideBasis] at side ⊢
    intro b v hlookup htof
    exact (side Psi1 hroot).2 b v hlookup htof
  case var_nlin =>
    intro Gamma x tau hlookupGamma side
    simp only [CheckedLocalTermSideBasisWithWorld,
      CheckedLocalTermSideBasis] at side ⊢
    intro b v hlookup htof
    exact (side Psi1 hroot).2 b v hlookup htof
  all_goals
    intros
    trivial

/-! ## Generic source-tree re-rooting -/

def CheckedLocalSideSWithWorld.rebase
    {p q : CheckedSelectedBasisSide}
    {Psi0 Psi1 : EvalCtx} {W0 W1 : EvalCtx -> Prop}
    (hpq : SelectedLe p q)
    (hroot : W0 Psi1)
    (hW : forall Psi, W1 Psi -> W0 Psi)
    {Gamma : NLCtx} {s : Space} {h : SValid Gamma s}
    (side : CheckedLocalSideSWithWorld p Psi0 W0 h) :
    CheckedLocalSideSWithWorld q Psi1 W1 h :=
  { shallow := ⟨belowS_map
      (P := fun {_ _ _ _} he =>
        CheckedLocalTermSideBasisWithWorld p Psi0 W0 he)
      (Q := fun {_ _ _ _} he => CheckedLocalTermSideBasis Psi1 he)
      (termSide_toShallow hroot) side.deep⟩
    deep := belowS_map
      (P := fun {_ _ _ _} he =>
        CheckedLocalTermSideBasisWithWorld p Psi0 W0 he)
      (Q := fun {_ _ _ _} he =>
        CheckedLocalTermSideBasisWithWorld q Psi1 W1 he)
      (termSide_restrict hpq hW) side.deep }

def CheckedLocalSideTWithWorld.rebase
    {p q : CheckedSelectedBasisSide}
    {Psi0 Psi1 : EvalCtx} {W0 W1 : EvalCtx -> Prop}
    (hpq : SelectedLe p q)
    (hroot : W0 Psi1)
    (hW : forall Psi, W1 Psi -> W0 Psi)
    {Gamma : NLCtx} {tau : Ty} {k : Kind} {h : TValid Gamma tau k}
    (side : CheckedLocalSideTWithWorld p Psi0 W0 h) :
    CheckedLocalSideTWithWorld q Psi1 W1 h :=
  { shallow := ⟨belowT_map
      (P := fun {_ _ _ _} he =>
        CheckedLocalTermSideBasisWithWorld p Psi0 W0 he)
      (Q := fun {_ _ _ _} he => CheckedLocalTermSideBasis Psi1 he)
      (termSide_toShallow hroot) side.deep⟩
    deep := belowT_map
      (P := fun {_ _ _ _} he =>
        CheckedLocalTermSideBasisWithWorld p Psi0 W0 he)
      (Q := fun {_ _ _ _} he =>
        CheckedLocalTermSideBasisWithWorld q Psi1 W1 he)
      (termSide_restrict hpq hW) side.deep }

def CheckedLocalSideSubWithWorld.rebase
    {p q : CheckedSelectedBasisSide}
    {Psi0 Psi1 : EvalCtx} {W0 W1 : EvalCtx -> Prop}
    (hpq : SelectedLe p q)
    (hroot : W0 Psi1)
    (hW : forall Psi, W1 Psi -> W0 Psi)
    {Gamma : NLCtx} {s0 s1 : Space} {h : SubType Gamma s0 s1}
    (side : CheckedLocalSideSubWithWorld p Psi0 W0 h) :
    CheckedLocalSideSubWithWorld q Psi1 W1 h :=
  { shallow := ⟨belowSub_map
      (P := fun {_ _ _ _} he =>
        CheckedLocalTermSideBasisWithWorld p Psi0 W0 he)
      (Q := fun {_ _ _ _} he => CheckedLocalTermSideBasis Psi1 he)
      (termSide_toShallow hroot) side.deep⟩
    deep := belowSub_map
      (P := fun {_ _ _ _} he =>
        CheckedLocalTermSideBasisWithWorld p Psi0 W0 he)
      (Q := fun {_ _ _ _} he =>
        CheckedLocalTermSideBasisWithWorld q Psi1 W1 he)
      (termSide_restrict hpq hW) side.deep }

def CheckedLocalSideBasesWithWorld.rebase
    {p q : CheckedSelectedBasisSide}
    {Psi0 Psi1 : EvalCtx} {W0 W1 : EvalCtx -> Prop}
    (hpq : SelectedLe p q)
    (hroot : W0 Psi1)
    (hW : forall Psi, W1 Psi -> W0 Psi)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau}
    (side : CheckedLocalSideBasesWithWorld p Psi0 W0 h) :
    CheckedLocalSideBasesWithWorld q Psi1 W1 h :=
  { shallow := ⟨termSide_toShallow hroot side.deepHere,
      belowH_map
        (P := fun {_ _ _ _} he =>
          CheckedLocalTermSideBasisWithWorld p Psi0 W0 he)
        (Q := fun {_ _ _ _} he => CheckedLocalTermSideBasis Psi1 he)
        (termSide_toShallow hroot) side.deepDescendants⟩
    deepHere := termSide_restrict hpq hW side.deepHere
    deepDescendants :=
      belowH_map
        (P := fun {_ _ _ _} he =>
          CheckedLocalTermSideBasisWithWorld p Psi0 W0 he)
        (Q := fun {_ _ _ _} he =>
          CheckedLocalTermSideBasisWithWorld q Psi1 W1 he)
        (termSide_restrict hpq hW) side.deepDescendants }

def CheckedLocalSideSWith.rebaseFuture
    {p q : CheckedSelectedBasisSide} {Psi0 Psi1 : EvalCtx}
    (hpq : SelectedLe p q) (hfuture : CheckedStdFuture Psi0 Psi1)
    {Gamma : NLCtx} {s : Space} {h : SValid Gamma s}
    (side : CheckedLocalSideSWith p Psi0 h) :
    CheckedLocalSideSWith q Psi1 h :=
  CheckedLocalSideSWithWorld.rebase hpq hfuture
    (fun _ h => hfuture.trans h) side

def CheckedLocalSideTWith.rebaseFuture
    {p q : CheckedSelectedBasisSide} {Psi0 Psi1 : EvalCtx}
    (hpq : SelectedLe p q) (hfuture : CheckedStdFuture Psi0 Psi1)
    {Gamma : NLCtx} {tau : Ty} {k : Kind} {h : TValid Gamma tau k}
    (side : CheckedLocalSideTWith p Psi0 h) :
    CheckedLocalSideTWith q Psi1 h :=
  CheckedLocalSideTWithWorld.rebase hpq hfuture
    (fun _ h => hfuture.trans h) side

def CheckedLocalSideSubWith.rebaseFuture
    {p q : CheckedSelectedBasisSide} {Psi0 Psi1 : EvalCtx}
    (hpq : SelectedLe p q) (hfuture : CheckedStdFuture Psi0 Psi1)
    {Gamma : NLCtx} {s0 s1 : Space} {h : SubType Gamma s0 s1}
    (side : CheckedLocalSideSubWith p Psi0 h) :
    CheckedLocalSideSubWith q Psi1 h :=
  CheckedLocalSideSubWithWorld.rebase hpq hfuture
    (fun _ h => hfuture.trans h) side

def CheckedLocalSideBasesWith.rebaseFuture
    {p q : CheckedSelectedBasisSide} {Psi0 Psi1 : EvalCtx}
    (hpq : SelectedLe p q) (hfuture : CheckedStdFuture Psi0 Psi1)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau}
    (side : CheckedLocalSideBasesWith p Psi0 h) :
    CheckedLocalSideBasesWith q Psi1 h :=
  CheckedLocalSideBasesWithWorld.rebase hpq hfuture
    (fun _ h => hfuture.trans h) side

/-! ## Re-rooting one positive basis syntax layer -/

/-- Re-root a positive syntax layer. -/
private def syntaxLayer_rebaseFuture
    {selected : EvalCtx -> CheckedSelectedBasisSide}
    {Psi0 Psi1 : EvalCtx}
    (hpq : SelectedLe (selected Psi0) (selected Psi1))
    (hfuture : CheckedStdFuture Psi0 Psi1)
    {Gamma : NLCtx} {b : Basis} :
    CheckedLocalSideBasisSyntaxLayer Psi0 selected Gamma b ->
      CheckedLocalSideBasisSyntaxLayer Psi1 selected Gamma b :=
  match b with
  | .empty => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
  | .one => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
  | .dual b => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨hb, child⟩ := side
      exact ⟨hb, syntaxLayer_rebaseFuture hpq hfuture child⟩
  | .dsum b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_rebaseFuture hpq hfuture child0⟩,
        ⟨hb1, syntaxLayer_rebaseFuture hpq hfuture child1⟩⟩
  | .tprod b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_rebaseFuture hpq hfuture child0⟩,
        ⟨hb1, syntaxLayer_rebaseFuture hpq hfuture child1⟩⟩
  | .proj (.ker s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_rebaseFuture hpq hfuture child0⟩,
        ⟨hb1, syntaxLayer_rebaseFuture hpq hfuture child1⟩,
        hsof0, hsof1, ht,
        ⟨CheckedLocalSideBasesWith.rebaseFuture hpq hfuture termSide⟩⟩
  | .proj (.coker s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_rebaseFuture hpq hfuture child0⟩,
        ⟨hb1, syntaxLayer_rebaseFuture hpq hfuture child1⟩,
        hsof0, hsof1, ht,
        ⟨CheckedLocalSideBasesWith.rebaseFuture hpq hfuture termSide⟩⟩
  | .proj (.img s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_rebaseFuture hpq hfuture child0⟩,
        ⟨hb1, syntaxLayer_rebaseFuture hpq hfuture child1⟩,
        hsof0, hsof1, ht,
        ⟨CheckedLocalSideBasesWith.rebaseFuture hpq hfuture termSide⟩⟩
  | .proj (.coimg s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_rebaseFuture hpq hfuture child0⟩,
        ⟨hb1, syntaxLayer_rebaseFuture hpq hfuture child1⟩,
        hsof0, hsof1, ht,
        ⟨CheckedLocalSideBasesWith.rebaseFuture hpq hfuture termSide⟩⟩
  | .proj .empty _ _ => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side
  | .proj .real _ _ => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side
  | .proj (.dual _) _ _ => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side
  | .proj (.dsum _ _) _ _ => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side
  | .proj (.tprod _ _) _ _ => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side
  | .image b => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨s0, s1, e, hb, hsof, child, ht, ⟨termSide⟩⟩ := side
      exact ⟨s0, s1, e, hb, hsof,
        syntaxLayer_rebaseFuture hpq hfuture child, ht,
        ⟨CheckedLocalSideBasesWith.rebaseFuture hpq hfuture termSide⟩⟩
  | .terms s es b => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb, child⟩, hsof, ⟨hs, ⟨spaceSide⟩⟩, termSides⟩ := side
      refine ⟨⟨hb, syntaxLayer_rebaseFuture hpq hfuture child⟩, hsof,
        ⟨hs, ⟨CheckedLocalSideSWith.rebaseFuture hpq hfuture spaceSide⟩⟩, ?_⟩
      intro e he
      obtain ⟨ht, ⟨termSide⟩⟩ := termSides e he
      exact ⟨ht,
        ⟨CheckedLocalSideBasesWith.rebaseFuture hpq hfuture termSide⟩⟩
  | .frame b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨k0, k1, L, hb0, hbody, domainSide, bodySides,
        ht, ⟨typeSide⟩⟩ := side
      refine ⟨k0, k1, L, hb0, hbody,
        syntaxLayer_rebaseFuture hpq hfuture domainSide, ?_, ht,
        ⟨CheckedLocalSideTWith.rebaseFuture hpq hfuture typeSide⟩⟩
      intro Psi' hfuture' y hy bArg v hbArg htof
      exact bodySides Psi' (hfuture.trans hfuture') y hy bArg v hbArg htof
termination_by Basis.size b
decreasing_by
  all_goals simp [Basis.size] <;> omega

/-! ## Whole-certificate re-rooting -/

/-- A concrete pair certificate may be re-rooted at any standard-only future
of its original evaluator.  The numeric depth and nonlinear context are
unchanged.  At a positive non-frame layer, recursive calls re-root the
strictly lower-depth selected pairs.  At a frame layer, endpoint-domain
self-pairs recurse at smaller syntax, while callback obligations merely
compose their future premise with the outer future. -/
theorem checkedPairBasisDepth_rebaseFuture
    {Psi0 Psi1 : EvalCtx} (hfuture : CheckedStdFuture Psi0 Psi1)
    {n : Nat} {Gamma : NLCtx} {source target : Basis}
    (pair : CheckedPairBasisDepth Psi0 n Gamma source target) :
    CheckedPairBasisDepth Psi1 n Gamma source target := by
  cases n with
  | zero =>
      simpa only [CheckedPairBasisDepth] using pair
  | succ d =>
      have hpq : SelectedLe
          (CheckedPairSelectedAt Psi0 d)
          (CheckedPairSelectedAt Psi1 d) := by
        intro Gamma' b hb selectedPair
        exact checkedPairBasisDepth_rebaseFuture hfuture selectedPair
      cases source <;> cases target <;>
        simp only [CheckedPairBasisDepth] at pair ⊢
      case frame.frame b10 b11 b20 b21 =>
        obtain ⟨htof0, htof1, sourceAvoid, targetAvoid,
          sourceDomainValid, targetDomainValid,
          sourceBodyValid, targetBodyValid,
          sourceDomain, targetDomain, sourceBody, targetBody, cross⟩ := pair
        refine ⟨htof0, htof1, sourceAvoid, targetAvoid,
          sourceDomainValid, targetDomainValid,
          sourceBodyValid, targetBodyValid,
          checkedPairBasisDepth_rebaseFuture hfuture sourceDomain,
          checkedPairBasisDepth_rebaseFuture hfuture targetDomain,
          ?_, ?_, ?_⟩
        · intro Psi' hfuture' y hyNames hy tauV hty
          -- The result is already rooted at the identical, possibly
          -- nonstandard, `Psi'.extend`; only the premise up to `Psi'` changes.
          exact sourceBody Psi' (hfuture.trans hfuture')
            y hyNames hy tauV hty
        · intro Psi' hfuture' y hyNames hy tauV hty
          exact targetBody Psi' (hfuture.trans hfuture')
            y hyNames hy tauV hty
        · intro Psi' hfuture' y hyNames hySource hyTarget tauV hty
          exact cross Psi' (hfuture.trans hfuture') y hyNames
            hySource hyTarget tauV hty
      all_goals
        first
        | exact pair.elim
        | obtain ⟨sourceNonFrame, targetNonFrame, htof,
            sourceSide, targetSide⟩ := pair
          exact ⟨sourceNonFrame, targetNonFrame, htof,
            syntaxLayer_rebaseFuture hpq hfuture sourceSide,
            syntaxLayer_rebaseFuture hpq hfuture targetSide⟩
termination_by (n, max (Basis.size source) (Basis.size target))
decreasing_by
  all_goals subst_vars
  all_goals
    first
    | apply Prod.Lex.left
      omega
    | apply Prod.Lex.right
      simp [Basis.size]
      omega

/-- Pointwise-finite pair evidence is likewise stable under standard
future extension. -/
theorem checkedPairBasisFinite_rebaseFuture
    {Psi0 Psi1 : EvalCtx} (hfuture : CheckedStdFuture Psi0 Psi1)
    {Gamma : NLCtx} {source target : Basis}
    (pair : CheckedPairBasisFinite Psi0 Gamma source target) :
    CheckedPairBasisFinite Psi1 Gamma source target := by
  obtain ⟨n, pair⟩ := pair
  exact ⟨n, checkedPairBasisDepth_rebaseFuture hfuture pair⟩

end RawCertifiedPairFutureRebase
end GLang
