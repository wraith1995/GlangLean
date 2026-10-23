import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairCertificate

/-!
# Numeric depth monotonicity for checked pair certificates

`CheckedPairBasisDepth` is monotone in its numeric cross-depth index.  This
module proves the one-step and arbitrary-depth lifts, transports that lift
through every selected-policy local-side tree, and packages the common-maximum
construction used to combine finitely many concrete depth witnesses.
-/

namespace GLang
namespace RawCertifiedPairDepthMonotonicity

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate

def SelectedLe (p q : CheckedSelectedBasisSide) : Prop :=
  forall {Gamma : NLCtx} {b : Basis} (hb : Basis.BasisValid Gamma b),
    p hb -> q hb

theorem termSide_mono
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {W : EvalCtx -> Prop}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau} :
    CheckedLocalTermSideBasisWithWorld p Psi W h ->
      CheckedLocalTermSideBasisWithWorld q Psi W h := by
  apply HasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ h =>
      CheckedLocalTermSideBasisWithWorld p Psi W h ->
        CheckedLocalTermSideBasisWithWorld q Psi W h)
  case var_lin =>
    intro Gamma x s side
    simp only [CheckedLocalTermSideBasisWithWorld] at side ⊢
    intro Psi' hW
    obtain ⟨choose, hall⟩ := side Psi' hW
    refine ⟨?_, hall⟩
    intro hcov
    obtain ⟨b, v, hlookup, htof, hb, hold⟩ := choose hcov
    exact ⟨b, v, hlookup, htof, hb, hpq hb hold⟩
  case var_nlin =>
    intro Gamma x tau hlookupGamma side
    simp only [CheckedLocalTermSideBasisWithWorld] at side ⊢
    intro Psi' hW
    obtain ⟨choose, hall⟩ := side Psi' hW
    refine ⟨?_, hall⟩
    intro hcov
    obtain ⟨b, v, hlookup, htof, hb, hold⟩ := choose hcov
    exact ⟨b, v, hlookup, htof, hb, hpq hb hold⟩
  all_goals
    intros
    trivial

private abbrev DeepS (p : CheckedSelectedBasisSide)
    (Psi : EvalCtx) (W : EvalCtx -> Prop)
    {Gamma : NLCtx} {s : Space} (h : SValid Gamma s) :=
  @SValid.below
    (fun _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ he => CheckedLocalTermSideBasisWithWorld p Psi W he)
    Gamma s h

private abbrev DeepT (p : CheckedSelectedBasisSide)
    (Psi : EvalCtx) (W : EvalCtx -> Prop)
    {Gamma : NLCtx} {tau : Ty} {k : Kind} (h : TValid Gamma tau k) :=
  @TValid.below
    (fun _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ he => CheckedLocalTermSideBasisWithWorld p Psi W he)
    Gamma tau k h

private abbrev DeepSub (p : CheckedSelectedBasisSide)
    (Psi : EvalCtx) (W : EvalCtx -> Prop)
    {Gamma : NLCtx} {s0 s1 : Space} (h : SubType Gamma s0 s1) :=
  @SubType.below
    (fun _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ he => CheckedLocalTermSideBasisWithWorld p Psi W he)
    Gamma s0 s1 h

private abbrev DeepH (p : CheckedSelectedBasisSide)
    (Psi : EvalCtx) (W : EvalCtx -> Prop)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) :=
  @HasType.below
    (fun _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ he => CheckedLocalTermSideBasisWithWorld p Psi W he)
    Delta Gamma e tau h

mutual

private def deepS_mono
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {W : EvalCtx -> Prop}
    {Gamma : NLCtx} {s : Space} {h : SValid Gamma s} :
    DeepS p Psi W h -> DeepS q Psi W h :=
  match h with
  | .empty => fun _ => ⟨⟩
  | .real => fun _ => ⟨⟩
  | .dual _ => fun side =>
      ⟨side.1, deepS_mono hpq side.2⟩
  | .dsum _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨side.2.1, deepS_mono hpq side.2.2⟩⟩
  | .tprod _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨side.2.1, deepS_mono hpq side.2.2⟩⟩
  | .ker _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩
  | .coker _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩
  | .img _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩
  | .coimg _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩

private def deepT_mono
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {W : EvalCtx -> Prop}
    {Gamma : NLCtx} {tau : Ty} {k : Kind} {h : TValid Gamma tau k} :
    DeepT p Psi W h -> DeepT q Psi W h :=
  match h with
  | .space _ => fun side =>
      ⟨side.1, deepS_mono hpq side.2⟩
  | .piTy _ _ _ => fun side =>
      ⟨⟨side.1.1, deepT_mono hpq side.1.2⟩,
        fun y hy =>
          ⟨(side.2 y hy).1, deepT_mono hpq (side.2 y hy).2⟩⟩

private def deepSub_mono
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {W : EvalCtx -> Prop}
    {Gamma : NLCtx} {s0 s1 : Space} {h : SubType Gamma s0 s1} :
    DeepSub p Psi W h -> DeepSub q Psi W h :=
  match h with
  | .sub_ker _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩
  | .sub_coker _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩
  | .sub_img _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩
  | .sub_coimg _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩

private def deepH_mono
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {W : EvalCtx -> Prop}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau} :
    DeepH p Psi W h -> DeepH q Psi W h :=
  match h with
  | .zero _ => fun side =>
      ⟨side.1, deepS_mono hpq side.2⟩
  | .smul _ _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨termSide_mono hpq side.2.1.1,
            deepH_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩
  | .add _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨termSide_mono hpq side.2.1.1,
            deepH_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩
  | .inner _ => fun side =>
      ⟨side.1, deepS_mono hpq side.2⟩
  | .real_lit _ => fun _ => ⟨⟩
  | .app_linear _ _ _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨⟨termSide_mono hpq side.2.2.1.1,
              deepH_mono hpq side.2.2.1.2⟩,
            ⟨termSide_mono hpq side.2.2.2.1,
              deepH_mono hpq side.2.2.2.2⟩⟩⟩⟩
  | .app_inner _ _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨termSide_mono hpq side.2.1.1,
            deepH_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩
  | .app_nonlinear _ _ => fun side =>
      ⟨⟨termSide_mono hpq side.1.1,
          deepH_mono hpq side.1.2⟩,
        ⟨termSide_mono hpq side.2.1,
          deepH_mono hpq side.2.2⟩⟩
  | .var_lin => fun _ => ⟨⟩
  | .var_nlin _ => fun _ => ⟨⟩
  | .pinv_tensor _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨termSide_mono hpq side.2.2.1,
            deepH_mono hpq side.2.2.2⟩⟩⟩
  | .pinv_dual _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨termSide_mono hpq side.2.1,
          deepH_mono hpq side.2.2⟩⟩
  | .promote _ _ _ _ _ => fun side =>
      ⟨termSide_mono hpq side.1, deepH_mono hpq side.2⟩
  | .dsumE _ _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨⟨termSide_mono hpq side.2.2.1.1,
              deepH_mono hpq side.2.2.1.2⟩,
            ⟨termSide_mono hpq side.2.2.2.1,
              deepH_mono hpq side.2.2.2.2⟩⟩⟩⟩
  | .tprodE _ _ _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          ⟨⟨termSide_mono hpq side.2.2.1.1,
              deepH_mono hpq side.2.2.1.2⟩,
            ⟨termSide_mono hpq side.2.2.2.1,
              deepH_mono hpq side.2.2.2.2⟩⟩⟩⟩
  | .llam_real _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        fun y hy =>
          ⟨termSide_mono hpq (side.2 y hy).1,
            deepH_mono hpq (side.2 y hy).2⟩⟩
  | .llam_tensor _ _ _ _ _ => fun side =>
      ⟨⟨side.1.1, deepS_mono hpq side.1.2⟩,
        ⟨⟨side.2.1.1, deepS_mono hpq side.2.1.2⟩,
          fun y hy =>
            ⟨termSide_mono hpq (side.2.2 y hy).1,
              deepH_mono hpq (side.2.2 y hy).2⟩⟩⟩
  | .embed _ => fun side =>
      ⟨side.1, deepSub_mono hpq side.2⟩
  | .nllam _ _ _ => fun side =>
      ⟨⟨side.1.1, deepT_mono hpq side.1.2⟩,
        fun y hy =>
          ⟨termSide_mono hpq (side.2 y hy).1,
            deepH_mono hpq (side.2 y hy).2⟩⟩

end

def CheckedLocalSideSWithWorld.monoSelected
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {W : EvalCtx -> Prop}
    {Gamma : NLCtx} {s : Space} {h : SValid Gamma s}
    (side : CheckedLocalSideSWithWorld p Psi W h) :
    CheckedLocalSideSWithWorld q Psi W h :=
  { shallow := side.shallow
    deep := deepS_mono hpq side.deep }

def CheckedLocalSideTWithWorld.monoSelected
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {W : EvalCtx -> Prop}
    {Gamma : NLCtx} {tau : Ty} {k : Kind} {h : TValid Gamma tau k}
    (side : CheckedLocalSideTWithWorld p Psi W h) :
    CheckedLocalSideTWithWorld q Psi W h :=
  { shallow := side.shallow
    deep := deepT_mono hpq side.deep }

def CheckedLocalSideSubWithWorld.monoSelected
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {W : EvalCtx -> Prop}
    {Gamma : NLCtx} {s0 s1 : Space} {h : SubType Gamma s0 s1}
    (side : CheckedLocalSideSubWithWorld p Psi W h) :
    CheckedLocalSideSubWithWorld q Psi W h :=
  { shallow := side.shallow
    deep := deepSub_mono hpq side.deep }

def CheckedLocalSideBasesWithWorld.monoSelected
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {W : EvalCtx -> Prop}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau}
    (side : CheckedLocalSideBasesWithWorld p Psi W h) :
    CheckedLocalSideBasesWithWorld q Psi W h :=
  { shallow := side.shallow
    deepHere := termSide_mono hpq side.deepHere
    deepDescendants := deepH_mono hpq side.deepDescendants }

def CheckedLocalSideSWith.monoSelected
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {Gamma : NLCtx} {s : Space} {h : SValid Gamma s}
    (side : CheckedLocalSideSWith p Psi h) :
    CheckedLocalSideSWith q Psi h :=
  CheckedLocalSideSWithWorld.monoSelected hpq side

def CheckedLocalSideTWith.monoSelected
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {Gamma : NLCtx} {tau : Ty} {k : Kind}
    {h : TValid Gamma tau k}
    (side : CheckedLocalSideTWith p Psi h) :
    CheckedLocalSideTWith q Psi h :=
  CheckedLocalSideTWithWorld.monoSelected hpq side

def CheckedLocalSideSubWith.monoSelected
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {Gamma : NLCtx} {s0 s1 : Space}
    {h : SubType Gamma s0 s1}
    (side : CheckedLocalSideSubWith p Psi h) :
    CheckedLocalSideSubWith q Psi h :=
  CheckedLocalSideSubWithWorld.monoSelected hpq side

def CheckedLocalSideBasesWith.monoSelected
    {p q : CheckedSelectedBasisSide} (hpq : SelectedLe p q)
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {e : Term} {tau : Ty} {h : HasType Delta Gamma e tau}
    (side : CheckedLocalSideBasesWith p Psi h) :
    CheckedLocalSideBasesWith q Psi h :=
  CheckedLocalSideBasesWithWorld.monoSelected hpq side

def WorldSelectedLe
    (p q : EvalCtx -> CheckedSelectedBasisSide) : Prop :=
  forall Psi, SelectedLe (p Psi) (q Psi)

def syntaxLayer_mono
    {p q : EvalCtx -> CheckedSelectedBasisSide}
    (hpq : WorldSelectedLe p q)
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis} :
    CheckedLocalSideBasisSyntaxLayer Psi p Gamma b ->
      CheckedLocalSideBasisSyntaxLayer Psi q Gamma b :=
  match b with
  | .empty => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
  | .one => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
  | .dual b => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨hb, child⟩ := side
      exact ⟨hb, syntaxLayer_mono hpq child⟩
  | .dsum b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_mono hpq child0⟩,
        ⟨hb1, syntaxLayer_mono hpq child1⟩⟩
  | .tprod b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_mono hpq child0⟩,
        ⟨hb1, syntaxLayer_mono hpq child1⟩⟩
  | .proj (.ker s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_mono hpq child0⟩,
        ⟨hb1, syntaxLayer_mono hpq child1⟩,
        hsof0, hsof1, ht,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .proj (.coker s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_mono hpq child0⟩,
        ⟨hb1, syntaxLayer_mono hpq child1⟩,
        hsof0, hsof1, ht,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .proj (.img s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_mono hpq child0⟩,
        ⟨hb1, syntaxLayer_mono hpq child1⟩,
        hsof0, hsof1, ht,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .proj (.coimg s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, syntaxLayer_mono hpq child0⟩,
        ⟨hb1, syntaxLayer_mono hpq child1⟩,
        hsof0, hsof1, ht,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
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
      exact ⟨s0, s1, e, hb, hsof, syntaxLayer_mono hpq child,
        ht, ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .terms s es b => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb, child⟩, hsof, ⟨hs, ⟨spaceSide⟩⟩, termSides⟩ := side
      refine ⟨⟨hb, syntaxLayer_mono hpq child⟩, hsof,
        ⟨hs, ⟨CheckedLocalSideSWith.monoSelected (hpq Psi) spaceSide⟩⟩, ?_⟩
      intro e he
      obtain ⟨ht, ⟨termSide⟩⟩ := termSides e he
      exact ⟨ht,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .frame b0 b1 => fun side => by
      simp only [CheckedLocalSideBasisSyntaxLayer] at side ⊢
      obtain ⟨k0, k1, L, hb0, hbody, domainSide, bodySides,
        ht, ⟨typeSide⟩⟩ := side
      refine ⟨k0, k1, L, hb0, hbody,
        syntaxLayer_mono hpq domainSide, ?_, ht,
        ⟨CheckedLocalSideTWith.monoSelected (hpq Psi) typeSide⟩⟩
      intro Psi' hfuture y hy bArg v hbArg htof
      obtain ⟨domainSide', bodySide'⟩ :=
        bodySides Psi' hfuture y hy bArg v hbArg htof
      exact ⟨fun hb0x => syntaxLayer_mono hpq (domainSide' hb0x),
        syntaxLayer_mono hpq bodySide'⟩
termination_by Basis.size b
decreasing_by
  all_goals simp [Basis.size, Basis.size_openVar] <;> omega

theorem CheckedLocalSideBasisZero.nonFrame
    {Gamma : NLCtx} {b : Basis} {hb : Basis.BasisValid Gamma b}
    (side : CheckedLocalSideBasisZero hb) : BasisNonFrame b := by
  induction side <;> simp [BasisNonFrame]

theorem CheckedLocalSideBasisZero.toSyntaxLayer
    {selected : EvalCtx -> CheckedSelectedBasisSide}
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma b}
    (side : CheckedLocalSideBasisZero hb) :
    CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b := by
  induction side with
  | empty => simp [CheckedLocalSideBasisSyntaxLayer]
  | one => simp [CheckedLocalSideBasisSyntaxLayer]
  | dual side ih =>
      simp only [CheckedLocalSideBasisSyntaxLayer]
      exact ⟨by assumption, ih⟩
  | dsum side0 side1 ih0 ih1 =>
      simp only [CheckedLocalSideBasisSyntaxLayer]
      exact ⟨⟨by assumption, ih0⟩, ⟨by assumption, ih1⟩⟩
  | tprod side0 side1 ih0 ih1 =>
      simp only [CheckedLocalSideBasisSyntaxLayer]
      exact ⟨⟨by assumption, ih0⟩, ⟨by assumption, ih1⟩⟩

theorem pairDepth_succ
    : forall (depth : Nat) (Psi : EvalCtx) (Gamma : NLCtx)
        (source target : Basis),
      CheckedPairBasisDepth Psi depth Gamma source target ->
      CheckedPairBasisDepth Psi (depth + 1) Gamma source target := by
  intro depth
  induction depth with
  | zero =>
      intro Psi Gamma source target pair
      simp only [CheckedPairBasisDepth] at pair
      obtain ⟨htof, ⟨hs, sourceZero⟩, ⟨ht, targetZero⟩⟩ := pair
      have result :
          BasisNonFrame source /\ BasisNonFrame target /\
          Basis.tof target = Basis.tof source /\
          CheckedLocalSideBasisSyntaxLayer Psi
            (fun Psi' {Gamma'} {b} _hb =>
              CheckedPairBasisDepth Psi' 0 Gamma' b
                (Basis.std (Basis.tof b))) Gamma source /\
          CheckedLocalSideBasisSyntaxLayer Psi
            (fun Psi' {Gamma'} {b} _hb =>
              CheckedPairBasisDepth Psi' 0 Gamma' b
                (Basis.std (Basis.tof b))) Gamma target :=
        ⟨RawCertifiedPairDepthMonotonicity.CheckedLocalSideBasisZero.nonFrame
            sourceZero,
          RawCertifiedPairDepthMonotonicity.CheckedLocalSideBasisZero.nonFrame
            targetZero,
          htof,
          RawCertifiedPairDepthMonotonicity.CheckedLocalSideBasisZero.toSyntaxLayer
            sourceZero,
          RawCertifiedPairDepthMonotonicity.CheckedLocalSideBasisZero.toSyntaxLayer
            targetZero⟩
      cases source <;> cases target <;>
        first
        | exact (by simpa only [CheckedPairBasisDepth] using result)
        | exact (by simpa [BasisNonFrame] using result.1)
        | exact (by simpa [BasisNonFrame] using result.2.1)
  | succ n ihDepth =>
      intro Psi Gamma source target pair
      suffices hraise : forall size, forall (Psi : EvalCtx) (Gamma : NLCtx)
          (source target : Basis),
          max (Basis.size source) (Basis.size target) <= size ->
          CheckedPairBasisDepth Psi (n + 1) Gamma source target ->
          CheckedPairBasisDepth Psi (n + 2) Gamma source target by
        exact hraise (max (Basis.size source) (Basis.size target))
          Psi Gamma source target (le_refl _) pair
      intro size
      induction size using Nat.strong_induction_on with
      | _ size ihSize =>
        intro Psi Gamma source target hsize pair
        cases source <;> cases target <;>
          simp only [CheckedPairBasisDepth] at pair ⊢
        case frame.frame b10 b11 b20 b21 =>
          obtain ⟨htof0, htof1, sourceAvoid, targetAvoid,
            sourceDomainValid, targetDomainValid,
            sourceBodyValid, targetBodyValid,
            sourceDomain, targetDomain, sourceBody, targetBody,
            cross⟩ := pair
          have small10 : max (Basis.size b10) (Basis.size b10) < size := by
            simp only [Basis.size] at hsize ⊢
            omega
          have small20 : max (Basis.size b20) (Basis.size b20) < size := by
            simp only [Basis.size] at hsize ⊢
            omega
          refine ⟨htof0, htof1, sourceAvoid, targetAvoid,
            sourceDomainValid, targetDomainValid,
            sourceBodyValid, targetBodyValid,
            ihSize _ small10 Psi Gamma b10 b10 (le_refl _) sourceDomain,
            ihSize _ small20 Psi Gamma b20 b20 (le_refl _) targetDomain,
            ?_, ?_, ?_⟩
          · intro Psi' hfuture y hyNames hy tauV hty
            have smallBody :
                max (Basis.size (Basis.openVar y b11))
                  (Basis.size (Basis.openVar y b11)) < size := by
              simp only [Basis.size, Basis.size_openVar] at hsize ⊢
              omega
            exact ihSize _ smallBody
              (Psi'.extend y b10 (.var y tauV))
              (Finmap.insert y (Basis.tof b10) Gamma)
              (Basis.openVar y b11) (Basis.openVar y b11)
              (le_refl _)
              (sourceBody Psi' hfuture y hyNames hy tauV hty)
          · intro Psi' hfuture y hyNames hy tauV hty
            have smallBody :
                max (Basis.size (Basis.openVar y b21))
                  (Basis.size (Basis.openVar y b21)) < size := by
              simp only [Basis.size, Basis.size_openVar] at hsize ⊢
              omega
            exact ihSize _ smallBody
              (Psi'.extend y b20 (.var y tauV))
              (Finmap.insert y (Basis.tof b20) Gamma)
              (Basis.openVar y b21) (Basis.openVar y b21)
              (le_refl _)
              (targetBody Psi' hfuture y hyNames hy tauV hty)
          · intro Psi' hfuture y hyNames hySource hyTarget tauV hty
            obtain ⟨domainCross, bodyCross⟩ :=
              cross Psi' hfuture y hyNames hySource hyTarget tauV hty
            have smallDomain :
                max (Basis.size b20) (Basis.size b10) < size := by
              simp only [Basis.size] at hsize ⊢
              omega
            have smallBody :
                max (Basis.size (Basis.openVar y b11))
                  (Basis.size (Basis.openVar y b21)) < size := by
              simp only [Basis.size, Basis.size_openVar] at hsize ⊢
              omega
            exact ⟨ihSize _ smallDomain
                (Psi'.extend y b20 (.var y tauV))
                (Finmap.insert y (Basis.tof b20) Gamma)
                b20 b10 (le_refl _) domainCross,
              ihSize _ smallBody
                (Psi'.extend y b20 (.var y tauV))
                (Finmap.insert y (Basis.tof b20) Gamma)
                (Basis.openVar y b11) (Basis.openVar y b21)
                (le_refl _) bodyCross⟩
        all_goals
          obtain ⟨sourceNonFrame, targetNonFrame, htof,
            sourceSide, targetSide⟩ := pair
          exact ⟨sourceNonFrame, targetNonFrame, htof,
            syntaxLayer_mono
              (fun Psi' {Gamma'} {b} _hb selectedPair =>
                ihDepth Psi' Gamma' b (Basis.std (Basis.tof b)) selectedPair)
              sourceSide,
            syntaxLayer_mono
              (fun Psi' {Gamma'} {b} _hb selectedPair =>
                ihDepth Psi' Gamma' b (Basis.std (Basis.tof b)) selectedPair)
              targetSide⟩

/-- A checked pair certificate can be raised to any greater numeric depth. -/
theorem pairDepth_mono
    {source target : Basis} {Gamma : NLCtx} {Psi : EvalCtx}
    {n m : Nat} (hnm : n ≤ m)
    (pair : CheckedPairBasisDepth Psi n Gamma source target) :
    CheckedPairBasisDepth Psi m Gamma source target := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hnm
  clear hnm
  induction k with
  | zero => simpa
  | succ k ih =>
      rw [Nat.add_succ]
      exact pairDepth_succ _ _ _ _ _ ih

/-- The selected-basis policy at depth `n` is pointwise contained in the
policy at every greater depth. -/
theorem checkedPairSelectedAt_mono
    {Psi : EvalCtx} {n m : Nat} (hnm : n ≤ m) :
    SelectedLe (CheckedPairSelectedAt Psi n)
      (CheckedPairSelectedAt Psi m) := by
  intro Gamma b hb pair
  exact pairDepth_mono hnm pair

/-- Raise the selected-pair depth throughout a checked local space tree. -/
def checkedPairLocalSideS_monoDepth
    {Psi : EvalCtx} {n m : Nat} (hnm : n ≤ m)
    {Gamma : NLCtx} {s : Space} {hs : SValid Gamma s}
    (side : CheckedPairLocalSideS Psi n hs) :
    CheckedPairLocalSideS Psi m hs :=
  CheckedLocalSideSWith.monoSelected
    (checkedPairSelectedAt_mono hnm) side

/-- Raise the selected-pair depth throughout a checked local type tree. -/
def checkedPairLocalSideT_monoDepth
    {Psi : EvalCtx} {n m : Nat} (hnm : n ≤ m)
    {Gamma : NLCtx} {tau : Ty} {k : Kind} {ht : TValid Gamma tau k}
    (side : CheckedPairLocalSideT Psi n ht) :
    CheckedPairLocalSideT Psi m ht :=
  CheckedLocalSideTWith.monoSelected
    (checkedPairSelectedAt_mono hnm) side

/-- Raise the selected-pair depth throughout a checked local subtype tree. -/
def checkedPairLocalSideSub_monoDepth
    {Psi : EvalCtx} {n m : Nat} (hnm : n ≤ m)
    {Gamma : NLCtx} {s0 s1 : Space} {hs : SubType Gamma s0 s1}
    (side : CheckedPairLocalSideSub Psi n hs) :
    CheckedPairLocalSideSub Psi m hs :=
  CheckedLocalSideSubWith.monoSelected
    (checkedPairSelectedAt_mono hnm) side

/-- Raise the selected-pair depth throughout a checked local term tree. -/
def checkedPairLocalSideBases_monoDepth
    {Psi : EvalCtx} {n m : Nat} (hnm : n ≤ m)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {ht : HasType Delta Gamma e tau}
    (side : CheckedPairLocalSideBases Psi n ht) :
    CheckedPairLocalSideBases Psi m ht :=
  CheckedLocalSideBasesWith.monoSelected
    (checkedPairSelectedAt_mono hnm) side

/-- Two individually finite pair certificates have one common numeric
depth.  This is the finite-depth combination principle used by callers. -/
theorem pairFinite_commonDepth
    {Psi : EvalCtx} {Gamma : NLCtx}
    {source0 target0 source1 target1 : Basis}
    (pair0 : CheckedPairBasisFinite Psi Gamma source0 target0)
    (pair1 : CheckedPairBasisFinite Psi Gamma source1 target1) :
    exists depth,
      CheckedPairBasisDepth Psi depth Gamma source0 target0 /\
      CheckedPairBasisDepth Psi depth Gamma source1 target1 := by
  obtain ⟨n, pair0⟩ := pair0
  obtain ⟨m, pair1⟩ := pair1
  exact ⟨max n m,
    pairDepth_mono (Nat.le_max_left n m) pair0,
    pairDepth_mono (Nat.le_max_right n m) pair1⟩

end RawCertifiedPairDepthMonotonicity
end GLang
