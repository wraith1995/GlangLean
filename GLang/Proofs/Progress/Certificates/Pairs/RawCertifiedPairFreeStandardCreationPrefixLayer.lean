import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardCreationPrefixStore
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardConstruction
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairControlledSourceFreeStandard
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairCreationDepth

/-!
# Structural free-standard creation-prefix layer

The free-standard variable case removes the false requirement that an
ordinary source binder's standard basis carry an independently bounded pair.
What remains is a genuine structural recursion on basis syntax.  A dependent
frame consumes one numeric layer to install each of its two literal endpoint
bases; the deliberately additive `basisHeight` is a conservative bound for
that recursion.

The internal selected service is packaged as a depth family.  This is needed
below nested frames: the outer endpoint must be reconstructible one layer
lower when it becomes a variable of the inner frame body.  At the creation
root the family comes for free by raising the uniform finite prefix store.
-/

namespace GLang
namespace RawCertifiedPairFreeStandardCreationPrefixLayer

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate
open RawCertifiedConsistentPairStore
open RawCertifiedPairFreeStandardCertificate
open RawCertifiedPairFreeStandardStore
open RawCertifiedPairFreeStandardConstruction
open RawCertifiedPairFreeStandardExecutableSyntax
open RawCertifiedPairFreeStandardCreationPrefixStore
open RawCertifiedPairControlledSourceFreeStandard
open RawCertifiedPairCreationDepth
open RawCertifiedPairFutureRebase
open RawCertifiedPairHybridFuture

/-- A controlled source-variable resolver available uniformly at every depth
above `baseDepth`.  Only actual creation-prefix keys and explicitly installed
frame endpoints use the pair branch; ordinary source binders are introduced
by the traversal through the standard branch. -/
def CheckedRelaxedControlledSelectedFamily
    (Psi : EvalCtx) (reserved : NLCtx) (baseDepth : Nat)
    (DeltaCtrl : LCtx) (GammaCtrl GammaTarget : NLCtx) : Prop :=
  forall depth, baseDepth <= depth ->
    CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      DeltaCtrl GammaCtrl GammaTarget

/-- Initialize a depth family from one uniform creation-prefix store and
re-root it at an arbitrary fresh future/target context. -/
theorem CheckedRelaxedControlledSelectedFamily.of_storeAtFresh
    {Psi0 Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {DeltaCtrl : LCtx} {baseDepth : Nat}
    (hlink : V2.TypingImplyEval DeltaCtrl GammaCtrl Psi0)
    (store : CheckedFreeStdFreshDepthQuadSelectedStoreAt
      Psi0 GammaCtrl baseDepth)
    (hfuture : CheckedFreshFuture Psi0 Psi)
    (hGamma : NLCtxIncl GammaCtrl GammaTarget) :
    CheckedRelaxedControlledSelectedFamily Psi (∅ : NLCtx) baseDepth
      DeltaCtrl GammaCtrl GammaTarget := by
  intro depth hle
  exact CheckedRelaxedControlledContextSelectedAt.of_storeAtFresh hlink
    (store.monoDepth hle) hfuture hGamma

/-- Discard the root linear context when entering a `BasisValid` source
judgment. -/
theorem CheckedRelaxedControlledSelectedFamily.restrictLinearEmpty
    {Psi : EvalCtx} {reserved : NLCtx} {baseDepth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget : NLCtx}
    (family : CheckedRelaxedControlledSelectedFamily Psi reserved baseDepth
      DeltaCtrl GammaCtrl GammaTarget) :
    CheckedRelaxedControlledSelectedFamily Psi reserved baseDepth
      (∅ : LCtx) GammaCtrl GammaTarget := by
  intro depth hle
  apply (family depth hle).restrictLinear
  intro x s hlookup
  cases hlookup

/-- Re-root a complete family through hybrid evaluator growth and nonlinear
target-context growth. -/
theorem CheckedRelaxedControlledSelectedFamily.rebase
    {Psi Psi' : EvalCtx} {reserved : NLCtx} {baseDepth : Nat}
    {DeltaCtrl : LCtx} {GammaCtrl GammaTarget GammaTarget' : NLCtx}
    (family : CheckedRelaxedControlledSelectedFamily Psi reserved baseDepth
      DeltaCtrl GammaCtrl GammaTarget)
    (hfuture : CheckedHybridFuture Psi Psi' reserved)
    (hGamma : NLCtxIncl GammaTarget GammaTarget') :
    CheckedRelaxedControlledSelectedFamily Psi' reserved baseDepth
      DeltaCtrl GammaCtrl GammaTarget' := by
  intro depth hle
  exact (family depth hle).rebase hfuture hGamma

/-! ## Promotion-free hygienic source witnesses -/

private structure FreeHygienicS (A : Finset Name)
    (Gamma : NLCtx) (s : Space) : Type where
  validity : SValid Gamma s
  promotionFree : Graded.SPromotionFree validity
  binderHygiene : Adequacy.CofiniteFreshen.SBinderHygiene A validity

/-- Normalize all embedded term witnesses of a space and enlarge every
cofinite avoid set, without changing the space judgment. -/
private noncomputable def normalizeS
    (A : Finset Name) {Gamma : NLCtx} {s : Space}
    (h : SValid Gamma s) : FreeHygienicS A Gamma s := by
  let h0 : SValid Gamma s :=
    Graded.svalidBwd (Graded.svalidBridge h) (fun _ _ hx => hx)
  let h0Free : Graded.SPromotionFree h0 :=
    Graded.svalidBwd_promotionFree (Graded.svalidBridge h)
      (fun _ _ hx => hx)
  let h1 := Adequacy.CofiniteFreshen.svalid A h0
  exact {
    validity := h1
    promotionFree := Adequacy.CofiniteFreshen.svalid_promotionFree A h0 h0Free
    binderHygiene := Adequacy.CofiniteFreshen.svalid_binderHygiene A h0 }

/-! ## Standard-space syntax under the relaxed selected policy -/

/-- The syntax layer of a standard space basis is the source-side tree of
the corresponding space-validity derivation. -/
theorem checkedFreeStdSpaceSyntaxLayer
    {Psi : EvalCtx} {depth : Nat} {Gamma : NLCtx} {s : Space}
    {hs : SValid Gamma s}
    (hfree : Graded.SPromotionFree hs)
    (side : CheckedLocalSideSWith (CheckedFreeStdSelectedAt Psi depth)
      Psi hs) :
    CheckedFreeStdExecutableBasisSyntaxLayer Psi
      (fun Psi' => CheckedFreeStdSelectedAt Psi' depth)
      Gamma (Basis.stdSpace s) := by
  cases hs with
  | empty =>
      simp [CheckedFreeStdExecutableBasisSyntaxLayer, Basis.stdSpace]
  | real =>
      simp [CheckedFreeStdExecutableBasisSyntaxLayer, Basis.stdSpace]
  | @dual Gamma s hs =>
      have side0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants side.deep
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer, Basis.stdSpace]
      exact ⟨Basis.stdSpace_valid s hs,
        checkedFreeStdSpaceSyntaxLayer hfree side0⟩
  | @dsum Gamma s0 s1 hs0 hs1 =>
      have side0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2 side.deep.2
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer, Basis.stdSpace]
      exact ⟨⟨Basis.stdSpace_valid s0 hs0,
          checkedFreeStdSpaceSyntaxLayer hfree.1 side0⟩,
        ⟨Basis.stdSpace_valid s1 hs1,
          checkedFreeStdSpaceSyntaxLayer hfree.2 side1⟩⟩
  | @tprod Gamma s0 s1 hs0 hs1 =>
      have side0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2 side.deep.2
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer, Basis.stdSpace]
      exact ⟨⟨Basis.stdSpace_valid s0 hs0,
          checkedFreeStdSpaceSyntaxLayer hfree.1 side0⟩,
        ⟨Basis.stdSpace_valid s1 hs1,
          checkedFreeStdSpaceSyntaxLayer hfree.2 side1⟩⟩
  | @ker Gamma e s0 s1 hs0 hs1 ht =>
      have side0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2.1 side.deep.2.1
      have sideTerm : CheckedLocalSideBasesWith
          (CheckedFreeStdSelectedAt Psi depth) Psi ht :=
        CheckedLocalSideBasesWith.ofBelowPair
          side.shallow.descendants.2.2 side.deep.2.2
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer, Basis.stdSpace]
      exact ⟨⟨Basis.stdSpace_valid s0 hs0,
          checkedFreeStdSpaceSyntaxLayer hfree.1 side0⟩,
        ⟨Basis.stdSpace_valid s1 hs1,
          checkedFreeStdSpaceSyntaxLayer hfree.2.1 side1⟩,
        Basis.sof_stdSpace s0, Basis.sof_stdSpace s1,
        ht, hfree.2.2, ⟨sideTerm⟩⟩
  | @coker Gamma e s0 s1 hs0 hs1 ht =>
      have side0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2.1 side.deep.2.1
      have sideTerm : CheckedLocalSideBasesWith
          (CheckedFreeStdSelectedAt Psi depth) Psi ht :=
        CheckedLocalSideBasesWith.ofBelowPair
          side.shallow.descendants.2.2 side.deep.2.2
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer, Basis.stdSpace]
      exact ⟨⟨Basis.stdSpace_valid s0 hs0,
          checkedFreeStdSpaceSyntaxLayer hfree.1 side0⟩,
        ⟨Basis.stdSpace_valid s1 hs1,
          checkedFreeStdSpaceSyntaxLayer hfree.2.1 side1⟩,
        Basis.sof_stdSpace s0, Basis.sof_stdSpace s1,
        ht, hfree.2.2, ⟨sideTerm⟩⟩
  | @img Gamma e s0 s1 hs0 hs1 ht =>
      have side0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2.1 side.deep.2.1
      have sideTerm : CheckedLocalSideBasesWith
          (CheckedFreeStdSelectedAt Psi depth) Psi ht :=
        CheckedLocalSideBasesWith.ofBelowPair
          side.shallow.descendants.2.2 side.deep.2.2
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer, Basis.stdSpace]
      exact ⟨⟨Basis.stdSpace_valid s0 hs0,
          checkedFreeStdSpaceSyntaxLayer hfree.1 side0⟩,
        ⟨Basis.stdSpace_valid s1 hs1,
          checkedFreeStdSpaceSyntaxLayer hfree.2.1 side1⟩,
        Basis.sof_stdSpace s0, Basis.sof_stdSpace s1,
        ht, hfree.2.2, ⟨sideTerm⟩⟩
  | @coimg Gamma e s0 s1 hs0 hs1 ht =>
      have side0 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSWith
          (CheckedFreeStdSelectedAt Psi depth) Psi hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2.1 side.deep.2.1
      have sideTerm : CheckedLocalSideBasesWith
          (CheckedFreeStdSelectedAt Psi depth) Psi ht :=
        CheckedLocalSideBasesWith.ofBelowPair
          side.shallow.descendants.2.2 side.deep.2.2
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer, Basis.stdSpace]
      exact ⟨⟨Basis.stdSpace_valid s0 hs0,
          checkedFreeStdSpaceSyntaxLayer hfree.1 side0⟩,
        ⟨Basis.stdSpace_valid s1 hs1,
          checkedFreeStdSpaceSyntaxLayer hfree.2.1 side1⟩,
        Basis.sof_stdSpace s0, Basis.sof_stdSpace s1,
        ht, hfree.2.2, ⟨sideTerm⟩⟩
termination_by Space.size s
decreasing_by
  all_goals (simp_all only [Space.size]; omega)

/-! ## Non-frame basis syntax -/

private theorem nonFrame_of_tof_space {b : Basis} {s : Space}
    (h : Basis.tof b = .space s) : BasisNonFrame b := by
  cases b <;> simp only [BasisNonFrame]
  case frame b0 b1 =>
    simp only [Basis.tof] at h
    contradiction

private theorem nonFrame_of_sof_coker
    {b : Basis} {s0 s1 : Space} {e : Term}
    (h : Basis.sof b = .coker s0 s1 e) : BasisNonFrame b := by
  cases b <;> simp only [BasisNonFrame]
  case frame b0 b1 =>
    simp only [Basis.sof] at h
    contradiction

private theorem nonFrame_stdSpace : forall s : Space,
    BasisNonFrame (Basis.stdSpace s) := by
  intro s
  cases s <;> simp [Basis.stdSpace, BasisNonFrame]

private theorem tof_eq_space_sof_of_nonFrame {b : Basis}
    (h : BasisNonFrame b) : Basis.tof b = .space (Basis.sof b) := by
  cases b <;> try rfl
  exact False.elim h

private theorem std_tof_eq_stdSpace_sof_of_nonFrame {b : Basis}
    (h : BasisNonFrame b) :
    Basis.std (Basis.tof b) = Basis.stdSpace (Basis.sof b) := by
  rw [tof_eq_space_sof_of_nonFrame h]
  rfl

/-- A positive relaxed quad exposes its source syntax layer at the preceding
selected depth. -/
private theorem sourceSyntax_of_quad
    {Psi : EvalCtx} {Gamma : NLCtx} {depth : Nat} {b : Basis}
    (q : CheckedFreeStdPairDepthQuad Psi (depth + 1) Gamma b)
    (h : BasisNonFrame b) :
    CheckedFreeStdExecutableBasisSyntaxLayer Psi
      (fun Psi' => CheckedFreeStdSelectedAt Psi' depth) Gamma b := by
  have pair := q.self
  cases b <;> simp only [CheckedFreeStdPairBasisDepth] at pair
  all_goals try exact pair.2.2.2.1
  case frame b0 b1 => exact False.elim h

/-- The finite source judgments stored immediately in one non-frame basis
constructor, already replayed in the target nonlinear context. -/
def CheckedFreeStdBasisImmediateSides
    (Psi : EvalCtx) (depth : Nat) (GammaTarget : NLCtx) :
    Basis -> Prop
  | .proj (.ker s0 s1 e) _ _ |
    .proj (.coker s0 s1 e) _ _ |
    .proj (.img s0 s1 e) _ _ |
    .proj (.coimg s0 s1 e) _ _ =>
      CheckedFreeStdExecutableTermWitness
        (CheckedFreeStdSelectedAt Psi depth) Psi
        (∅ : LCtx) GammaTarget e (.space (.tprod (.dual s0) s1))
  | .proj _ _ _ => False
  | .image b =>
      exists s0 s1 e,
        Basis.sof b = .coker s0 s1 e /\
        CheckedFreeStdExecutableTermWitness
          (CheckedFreeStdSelectedAt Psi depth) Psi
          (∅ : LCtx) GammaTarget e (.space (.tprod (.dual s0) s1))
  | .terms s es _ =>
      CheckedFreeStdExecutableSpaceWitness
        (CheckedFreeStdSelectedAt Psi depth) Psi GammaTarget s /\
      forall e, e ∈ es ->
        CheckedFreeStdExecutableTermWitness
          (CheckedFreeStdSelectedAt Psi depth) Psi
          (∅ : LCtx) GammaTarget e (.space s)
  | .frame _ _ => False
  | _ => True

/-- Assemble the source syntax of a non-frame basis from strict structural
children and its finite immediate source judgments. -/
theorem checkedFreeStdSourceSyntax_nonFrame_of_builders
    {Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {depth : Nat} {b : Basis}
    (hGamma : NLCtxIncl GammaCtrl GammaTarget)
    (hb : Basis.BasisValid GammaCtrl b)
    (hNonFrame : BasisNonFrame b)
    (buildChild : forall {b' : Basis},
      Basis.BasisValid GammaCtrl b' ->
      basisHeight b' < basisHeight b ->
      CheckedFreeStdPairDepthQuad Psi (depth + 1) GammaTarget b')
    (sourceSides : CheckedFreeStdBasisImmediateSides Psi depth
      GammaTarget b) :
    CheckedFreeStdExecutableBasisSyntaxLayer Psi
      (fun Psi' => CheckedFreeStdSelectedAt Psi' depth)
      GammaTarget b := by
  induction hb with
  | empty =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
  | one =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
  | @dual Gamma b hb htof ih =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      have hlt : basisHeight b < basisHeight (.dual b) := by
        simp only [basisHeight]
        omega
      exact ⟨raw_basisValid_mono hb hGamma,
        sourceSyntax_of_quad (buildChild hb hlt)
          (nonFrame_of_tof_space htof)⟩
  | @dsum Gamma b0 b1 hb0 hb1 htof0 htof1 ih0 ih1 =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      have hlt0 : basisHeight b0 < basisHeight (.dsum b0 b1) := by
        simp only [basisHeight]
        omega
      have hlt1 : basisHeight b1 < basisHeight (.dsum b0 b1) := by
        simp only [basisHeight]
        omega
      exact ⟨
        ⟨raw_basisValid_mono hb0 hGamma,
          sourceSyntax_of_quad (buildChild hb0 hlt0)
            (nonFrame_of_tof_space htof0)⟩,
        ⟨raw_basisValid_mono hb1 hGamma,
          sourceSyntax_of_quad (buildChild hb1 hlt1)
            (nonFrame_of_tof_space htof1)⟩⟩
  | @tprod Gamma b0 b1 hb0 hb1 htof0 htof1 ih0 ih1 =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      have hlt0 : basisHeight b0 < basisHeight (.tprod b0 b1) := by
        simp only [basisHeight]
        omega
      have hlt1 : basisHeight b1 < basisHeight (.tprod b0 b1) := by
        simp only [basisHeight]
        omega
      exact ⟨
        ⟨raw_basisValid_mono hb0 hGamma,
          sourceSyntax_of_quad (buildChild hb0 hlt0)
            (nonFrame_of_tof_space htof0)⟩,
        ⟨raw_basisValid_mono hb1 hGamma,
          sourceSyntax_of_quad (buildChild hb1 hlt1)
            (nonFrame_of_tof_space htof1)⟩⟩
  | @proj_ker Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 ht ih0 ih1 =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      have hlt0 : basisHeight b0 <
          basisHeight (.proj (.ker s0 s1 e) b0 b1) := by
        simp only [basisHeight]
        omega
      have hlt1 : basisHeight b1 <
          basisHeight (.proj (.ker s0 s1 e) b0 b1) := by
        simp only [basisHeight]
        omega
      obtain ⟨ht0, hfree0, ⟨side⟩⟩ := sourceSides
      exact ⟨
        ⟨raw_basisValid_mono hb0 hGamma,
          sourceSyntax_of_quad (buildChild hb0 hlt0)
            (nonFrame_of_tof_space htof0)⟩,
        ⟨raw_basisValid_mono hb1 hGamma,
          sourceSyntax_of_quad (buildChild hb1 hlt1)
            (nonFrame_of_tof_space htof1)⟩,
        Basis.sof_eq_of_tof_eq_space htof0,
        Basis.sof_eq_of_tof_eq_space htof1, ht0, hfree0, ⟨side⟩⟩
  | @proj_coker Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 ht ih0 ih1 =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      have hlt0 : basisHeight b0 <
          basisHeight (.proj (.coker s0 s1 e) b0 b1) := by
        simp only [basisHeight]
        omega
      have hlt1 : basisHeight b1 <
          basisHeight (.proj (.coker s0 s1 e) b0 b1) := by
        simp only [basisHeight]
        omega
      obtain ⟨ht0, hfree0, ⟨side⟩⟩ := sourceSides
      exact ⟨
        ⟨raw_basisValid_mono hb0 hGamma,
          sourceSyntax_of_quad (buildChild hb0 hlt0)
            (nonFrame_of_tof_space htof0)⟩,
        ⟨raw_basisValid_mono hb1 hGamma,
          sourceSyntax_of_quad (buildChild hb1 hlt1)
            (nonFrame_of_tof_space htof1)⟩,
        Basis.sof_eq_of_tof_eq_space htof0,
        Basis.sof_eq_of_tof_eq_space htof1, ht0, hfree0, ⟨side⟩⟩
  | @proj_img Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 ht ih0 ih1 =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      have hlt0 : basisHeight b0 <
          basisHeight (.proj (.img s0 s1 e) b0 b1) := by
        simp only [basisHeight]
        omega
      have hlt1 : basisHeight b1 <
          basisHeight (.proj (.img s0 s1 e) b0 b1) := by
        simp only [basisHeight]
        omega
      obtain ⟨ht0, hfree0, ⟨side⟩⟩ := sourceSides
      exact ⟨
        ⟨raw_basisValid_mono hb0 hGamma,
          sourceSyntax_of_quad (buildChild hb0 hlt0)
            (nonFrame_of_tof_space htof0)⟩,
        ⟨raw_basisValid_mono hb1 hGamma,
          sourceSyntax_of_quad (buildChild hb1 hlt1)
            (nonFrame_of_tof_space htof1)⟩,
        Basis.sof_eq_of_tof_eq_space htof0,
        Basis.sof_eq_of_tof_eq_space htof1, ht0, hfree0, ⟨side⟩⟩
  | @proj_coimg Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 ht ih0 ih1 =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      have hlt0 : basisHeight b0 <
          basisHeight (.proj (.coimg s0 s1 e) b0 b1) := by
        simp only [basisHeight]
        omega
      have hlt1 : basisHeight b1 <
          basisHeight (.proj (.coimg s0 s1 e) b0 b1) := by
        simp only [basisHeight]
        omega
      obtain ⟨ht0, hfree0, ⟨side⟩⟩ := sourceSides
      exact ⟨
        ⟨raw_basisValid_mono hb0 hGamma,
          sourceSyntax_of_quad (buildChild hb0 hlt0)
            (nonFrame_of_tof_space htof0)⟩,
        ⟨raw_basisValid_mono hb1 hGamma,
          sourceSyntax_of_quad (buildChild hb1 hlt1)
            (nonFrame_of_tof_space htof1)⟩,
        Basis.sof_eq_of_tof_eq_space htof0,
        Basis.sof_eq_of_tof_eq_space htof1, ht0, hfree0, ⟨side⟩⟩
  | @image Gamma b s0 s1 e hb hsof ht ih =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      have hlt : basisHeight b < basisHeight (.image b) := by
        simp only [basisHeight]
        omega
      obtain ⟨s0', s1', e', hsof', ht0, hfree0, ⟨side⟩⟩ := sourceSides
      have hcomponents :
          Space.coker s0 s1 e = Space.coker s0' s1' e' :=
        hsof.symm.trans hsof'
      injection hcomponents with hs0 hs1 he
      subst s0'
      subst s1'
      subst e'
      exact ⟨s0, s1, e, raw_basisValid_mono hb hGamma, hsof,
        sourceSyntax_of_quad (buildChild hb hlt)
          (nonFrame_of_sof_coker hsof), ht0, hfree0, ⟨side⟩⟩
  | @terms Gamma s es b hb htof hs hts hne ih =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      have hlt : basisHeight b < basisHeight (.terms s es b) := by
        simp only [basisHeight]
        omega
      obtain ⟨⟨hs0, hspaceFree, ⟨spaceSide⟩⟩, termSides⟩ := sourceSides
      refine ⟨
        ⟨raw_basisValid_mono hb hGamma,
          sourceSyntax_of_quad (buildChild hb hlt)
            (nonFrame_of_tof_space htof)⟩,
        Basis.sof_eq_of_tof_eq_space htof,
        ⟨hs0, hspaceFree, ⟨spaceSide⟩⟩, ?_⟩
      intro e he
      exact termSides e he
  | @frame Gamma b0 b1 L hb0 hbody ih0 ihbody =>
      exact False.elim hNonFrame

/-- Complete all four relaxed orientations for a non-frame basis. -/
theorem checkedFreeStdPairDepthQuad_nonFrame_of_builders
    {Psi : EvalCtx} {GammaCtrl GammaTarget : NLCtx}
    {depth : Nat} {b : Basis}
    (hGamma : NLCtxIncl GammaCtrl GammaTarget)
    (hb : Basis.BasisValid GammaCtrl b)
    (hNonFrame : BasisNonFrame b)
    (buildChild : forall {b' : Basis},
      Basis.BasisValid GammaCtrl b' ->
      basisHeight b' < basisHeight b ->
      CheckedFreeStdPairDepthQuad Psi (depth + 1) GammaTarget b')
    (sourceSides : CheckedFreeStdBasisImmediateSides Psi depth
      GammaTarget b)
    (sofSide : CheckedFreeStdExecutableSpaceWitness
      (CheckedFreeStdSelectedAt Psi depth) Psi GammaTarget (Basis.sof b)) :
    CheckedFreeStdPairDepthQuad Psi (depth + 1) GammaTarget b := by
  let sourceSide := checkedFreeStdSourceSyntax_nonFrame_of_builders
    hGamma hb hNonFrame buildChild sourceSides
  obtain ⟨hs, hspaceFree, ⟨spaceSide⟩⟩ := sofSide
  have targetSide : CheckedFreeStdExecutableBasisSyntaxLayer Psi
      (fun Psi' => CheckedFreeStdSelectedAt Psi' depth) GammaTarget
      (Basis.std (Basis.tof b)) := by
    rw [std_tof_eq_stdSpace_sof_of_nonFrame hNonFrame]
    exact checkedFreeStdSpaceSyntaxLayer hspaceFree spaceSide
  apply checkedFreeStdPairDepthQuad_nonFrame_of_syntax hNonFrame
  · rw [std_tof_eq_stdSpace_sof_of_nonFrame hNonFrame]
    exact nonFrame_stdSpace _
  · exact sourceSide
  · exact targetSide

/-! ## Discharging immediate source judgments -/

private noncomputable def traversalAmbient (Psi : EvalCtx) (reserved : NLCtx)
    (GammaCtrl GammaTarget : NLCtx) : Finset Name :=
  Psi.names ∪ reserved.keys ∪ GammaCtrl.keys ∪ GammaTarget.keys

/-- Normalize and replay every source judgment stored immediately in a
non-frame validity constructor. -/
private noncomputable def immediateSides_of_valid
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {GammaCtrl GammaTarget : NLCtx} {b : Basis}
    (hb : Basis.BasisValid GammaCtrl b)
    (hNonFrame : BasisNonFrame b)
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      (∅ : LCtx) GammaCtrl GammaTarget)
    (hGamma : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget) :
    CheckedFreeStdBasisImmediateSides Psi depth GammaTarget b := by
  let A := traversalAmbient Psi reserved GammaCtrl GammaTarget
  cases hb with
  | empty => exact True.intro
  | one => exact True.intro
  | dual hb htof => exact True.intro
  | dsum hb0 hb1 htof0 htof1 => exact True.intro
  | tprod hb0 hb1 htof0 htof1 => exact True.intro
  | proj_ker hb0 hb1 htof0 htof1 ht =>
      obtain ⟨ht⟩ := ht
      let normalized := normalizedTypingAvoidingFreeHygienic A
        (Graded.CtxDisj.empty GammaCtrl) ht
      let result := RawCertifiedPairControlledSourceFreeStandard.ofH
        normalized.typing selected hGamma hwf normalized.promotionFree
          normalized.binderHygiene
      exact ⟨result.target, result.promotionFree, ⟨result.side⟩⟩
  | proj_coker hb0 hb1 htof0 htof1 ht =>
      obtain ⟨ht⟩ := ht
      let normalized := normalizedTypingAvoidingFreeHygienic A
        (Graded.CtxDisj.empty GammaCtrl) ht
      let result := RawCertifiedPairControlledSourceFreeStandard.ofH
        normalized.typing selected hGamma hwf normalized.promotionFree
          normalized.binderHygiene
      exact ⟨result.target, result.promotionFree, ⟨result.side⟩⟩
  | proj_img hb0 hb1 htof0 htof1 ht =>
      obtain ⟨ht⟩ := ht
      let normalized := normalizedTypingAvoidingFreeHygienic A
        (Graded.CtxDisj.empty GammaCtrl) ht
      let result := RawCertifiedPairControlledSourceFreeStandard.ofH
        normalized.typing selected hGamma hwf normalized.promotionFree
          normalized.binderHygiene
      exact ⟨result.target, result.promotionFree, ⟨result.side⟩⟩
  | proj_coimg hb0 hb1 htof0 htof1 ht =>
      obtain ⟨ht⟩ := ht
      let normalized := normalizedTypingAvoidingFreeHygienic A
        (Graded.CtxDisj.empty GammaCtrl) ht
      let result := RawCertifiedPairControlledSourceFreeStandard.ofH
        normalized.typing selected hGamma hwf normalized.promotionFree
          normalized.binderHygiene
      exact ⟨result.target, result.promotionFree, ⟨result.side⟩⟩
  | @image _ b s0 s1 e hb hsof ht =>
      obtain ⟨ht⟩ := ht
      let normalized := normalizedTypingAvoidingFreeHygienic A
        (Graded.CtxDisj.empty GammaCtrl) ht
      let result := RawCertifiedPairControlledSourceFreeStandard.ofH
        normalized.typing selected hGamma hwf normalized.promotionFree
          normalized.binderHygiene
      exact ⟨s0, s1, e, hsof, result.target,
        result.promotionFree, ⟨result.side⟩⟩
  | @terms _ s es b hb htof hs hts hne =>
      obtain ⟨hs⟩ := hs
      let normalizedSpace := normalizeS A hs
      let spaceResult := RawCertifiedPairControlledSourceFreeStandard.ofS
        normalizedSpace.validity selected hGamma hwf
          normalizedSpace.promotionFree normalizedSpace.binderHygiene
      refine ⟨⟨spaceResult.target, spaceResult.promotionFree,
        ⟨spaceResult.side⟩⟩, ?_⟩
      intro e he
      obtain ⟨ht⟩ := hts e he
      let normalized := normalizedTypingAvoidingFreeHygienic A
        (Graded.CtxDisj.empty GammaCtrl) ht
      let result := RawCertifiedPairControlledSourceFreeStandard.ofH
        normalized.typing selected hGamma hwf normalized.promotionFree
          normalized.binderHygiene
      exact ⟨result.target, result.promotionFree, ⟨result.side⟩⟩
  | frame L hb0 hbody =>
      exact False.elim hNonFrame

/-- Normalize and replay the exposed space of a valid basis. -/
private noncomputable def sofSide_of_valid
    {Psi : EvalCtx} {reserved : NLCtx} {depth : Nat}
    {GammaCtrl GammaTarget : NLCtx} {b : Basis}
    (hb : Basis.BasisValid GammaCtrl b)
    (selected : CheckedRelaxedControlledContextSelectedAt Psi reserved depth
      (∅ : LCtx) GammaCtrl GammaTarget)
    (hGamma : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget) :
    CheckedFreeStdExecutableSpaceWitness
      (CheckedFreeStdSelectedAt Psi depth) Psi GammaTarget (Basis.sof b) := by
  obtain ⟨hs⟩ := hb.sof_valid
  let A := traversalAmbient Psi reserved GammaCtrl GammaTarget
  let normalized := normalizeS A hs
  let result := RawCertifiedPairControlledSourceFreeStandard.ofS
    normalized.validity selected hGamma hwf normalized.promotionFree
      normalized.binderHygiene
  exact ⟨result.target, result.promotionFree, ⟨result.side⟩⟩

/-! ## Environment-threaded strong basis recursion -/

private theorem basisHeight_pos (b : Basis) : 0 < basisHeight b := by
  cases b <;> simp [basisHeight]

private theorem not_mem_source_of_incl_target
    {GammaCtrl GammaTarget : NLCtx} {y : VName}
    (hGamma : NLCtxIncl GammaCtrl GammaTarget)
    (hyTarget : y ∉ GammaTarget) : y ∉ GammaCtrl := by
  intro hyCtrl
  obtain ⟨tau, hlookup⟩ := Finmap.mem_iff.mp hyCtrl
  exact hyTarget (Finmap.mem_of_lookup_eq_some (hGamma y tau hlookup))

/-- Structural construction at any output depth meeting the additive budget.

The selected family is rooted at the exact current evaluator.  Frame-domain
calls merely rebase it, while frame-body calls install the literal endpoint
as pair-backed provenance.  Ordinary binders encountered by source traversal
remain internal standard-provenance slots and therefore do not consume this
basis budget. -/
theorem checkedFreeStdPairDepthQuad_of_family
    {baseDepth : Nat} {Psi : EvalCtx}
    {GammaCtrl GammaTarget : NLCtx} {b : Basis} {outDepth : Nat}
    (family : CheckedRelaxedControlledSelectedFamily Psi (∅ : NLCtx)
      baseDepth (∅ : LCtx) GammaCtrl GammaTarget)
    (hGamma : NLCtxIncl GammaCtrl GammaTarget)
    (hwf : V2.CtxWF' (∅ : LCtx) GammaTarget)
    (hb : Basis.BasisValid GammaCtrl b)
    (hbudget : baseDepth + basisHeight b <= outDepth) :
    CheckedFreeStdPairDepthQuad Psi outDepth GammaTarget b := by
  suffices build : forall height,
      forall {baseDepth : Nat} {Psi : EvalCtx}
        {GammaCtrl GammaTarget : NLCtx}
        {b : Basis} {outDepth : Nat},
      basisHeight b = height ->
      CheckedRelaxedControlledSelectedFamily Psi (∅ : NLCtx)
        baseDepth (∅ : LCtx) GammaCtrl GammaTarget ->
      NLCtxIncl GammaCtrl GammaTarget ->
      V2.CtxWF' (∅ : LCtx) GammaTarget ->
      Basis.BasisValid GammaCtrl b ->
      baseDepth + basisHeight b <= outDepth ->
        CheckedFreeStdPairDepthQuad Psi outDepth GammaTarget b by
    exact build (basisHeight b) rfl family hGamma hwf hb hbudget
  intro height
  induction height using Nat.strong_induction_on with
  | h height ih =>
      intro baseDepth Psi GammaCtrl GammaTarget b outDepth hheight family
        hGamma hwf hb hbudget
      cases outDepth with
      | zero =>
          have hpos := basisHeight_pos b
          omega
      | succ selectedDepth =>
          have hbase : baseDepth <= selectedDepth := by
            have hpos := basisHeight_pos b
            omega
          by_cases hNonFrame : BasisNonFrame b
          · let selected := family selectedDepth hbase
            let buildChild : forall {b' : Basis},
                Basis.BasisValid GammaCtrl b' ->
                basisHeight b' < basisHeight b ->
                CheckedFreeStdPairDepthQuad Psi (selectedDepth + 1)
                  GammaTarget b' := by
              intro b' hb' hlt
              apply ih (basisHeight b')
              · omega
              · rfl
              · exact family
              · exact hGamma
              · exact hwf
              · exact hb'
              · omega
            exact checkedFreeStdPairDepthQuad_nonFrame_of_builders
              hGamma hb hNonFrame buildChild
              (immediateSides_of_valid hb hNonFrame selected hGamma hwf)
              (sofSide_of_valid hb selected hGamma hwf)
          · obtain ⟨b0, b1, rfl⟩ : exists b0 b1, b = .frame b0 b1 := by
              cases b <;> simp_all [BasisNonFrame]
            cases hb with
            | @frame _ _ _ L hb0 hbody =>
                have hheight0 : basisHeight b0 < height := by
                  rw [← hheight]
                  exact basisHeight_frame_domain_lt b0 b1
                have hstd0 : Basis.BasisValid GammaCtrl
                    (Basis.std (Basis.tof b0)) := by
                  obtain ⟨kind0, ⟨ht0⟩⟩ := hb0.tof_tvalid
                  exact Basis.std_valid _ ht0
                have hb0Target : Basis.BasisValid GammaTarget b0 :=
                  raw_basisValid_mono hb0 hGamma
                have hbodyTarget : forall y, y ∉ L ->
                    Basis.BasisValid
                      (Finmap.insert y (Basis.tof b0) GammaTarget)
                      (Basis.openVar y b1) := by
                  intro y hy
                  exact raw_basisValid_mono (hbody y hy)
                    (NLCtxIncl.insert_same hGamma y (Basis.tof b0))
                have domainQuad : CheckedFreeStdPairDepthQuad Psi
                    (selectedDepth + 1) GammaTarget b0 := by
                  apply ih (basisHeight b0) hheight0 rfl family hGamma hwf hb0
                  omega
                apply checkedFreeStdPairDepthQuad_frame_of_builders
                  hb0Target hbodyTarget domainQuad
                · intro Psi' hfuture y hyPsi hyAvoid bArg v hbArg htof
                    hEndpoint
                  have hyTarget : y ∉ GammaTarget := by
                    intro hy
                    exact hyAvoid
                      (Finset.mem_union_right _ (Finmap.mem_keys.mpr hy))
                  have hyCtrl : y ∉ GammaCtrl :=
                    not_mem_source_of_incl_target hGamma hyTarget
                  have hTarget : NLCtxIncl GammaTarget
                      (Finmap.insert y (Basis.tof b0) GammaTarget) :=
                    (NLCtxIncl.refl GammaTarget).insert_right
                      hyTarget (Basis.tof b0)
                  have hframeFuture : CheckedHybridFuture Psi
                      (Psi'.extend y bArg v) (∅ : NLCtx) :=
                    (CheckedHybridFuture.ofStandard hfuture).extend hyPsi
                      (Finmap.notMem_empty : y ∉ (∅ : NLCtx)) bArg v
                  have familyX := family.rebase hframeFuture hTarget
                  have hwfX : V2.CtxWF' (∅ : LCtx)
                      (Finmap.insert y (Basis.tof b0) GammaTarget) :=
                    RawLocalCtxWFInsertionScratch.ctxWF_insert_nl hwf
                      Finmap.notMem_empty hyTarget hb0Target
                  apply ih (basisHeight b0) hheight0 rfl familyX
                    (hGamma.trans hTarget) hwfX hb0
                  omega
                · intro Psi' hfuture y hyPsi hyAvoid bArg v hbArg htof
                    hEndpoint
                  have hyL : y ∉ L := by
                    intro hy
                    exact hyAvoid (Finset.mem_union_left _ hy)
                  have hyTarget : y ∉ GammaTarget := by
                    intro hy
                    exact hyAvoid
                      (Finset.mem_union_right _ (Finmap.mem_keys.mpr hy))
                  have hyCtrl : y ∉ GammaCtrl :=
                    not_mem_source_of_incl_target hGamma hyTarget
                  have hbodyHeight :
                      basisHeight (Basis.openVar y b1) < height := by
                    rw [← hheight]
                    exact basisHeight_frame_body_open_lt y b0 b1
                  let bodyBase := baseDepth + basisHeight b0
                  have bodyFamily : CheckedRelaxedControlledSelectedFamily
                      (Psi'.extend y bArg v) (∅ : NLCtx) bodyBase
                      (∅ : LCtx)
                      (Finmap.insert y (Basis.tof b0) GammaCtrl)
                      (Finmap.insert y (Basis.tof b0) GammaTarget) := by
                    intro currentDepth hcurrent
                    have hbaseCurrent : baseDepth <= currentDepth := by
                      omega
                    let parentAt := family currentDepth hbaseCurrent
                    have parentAtPsi' := parentAt.rebase
                      (CheckedHybridFuture.ofStandard hfuture)
                      (NLCtxIncl.refl GammaTarget)
                    have endpointCtrl : Basis.BasisValid GammaCtrl bArg := by
                      rcases hEndpoint with rfl | rfl
                      · exact hb0
                      · exact hstd0
                    have endpointHeight : basisHeight bArg <= basisHeight b0 := by
                      rcases hEndpoint with rfl | rfl
                      · exact le_rfl
                      · exact basisHeight_std_tof_le b0
                    have endpointPackage : CheckedFreeStdHybridSelectedAt
                        Psi' GammaTarget (∅ : NLCtx) currentDepth bArg := by
                      refine {
                        valid := hbArg
                        quad := ?_ }
                      intro Psi'' Gamma'' hhybrid hGamma' hwf'
                      have family'' := family.rebase
                        ((CheckedHybridFuture.ofStandard hfuture).trans hhybrid)
                        hGamma'
                      apply ih (basisHeight bArg)
                      · omega
                      · rfl
                      · exact family''
                      · exact hGamma.trans hGamma'
                      · exact hwf'
                      · exact endpointCtrl
                      · omega
                    exact parentAtPsi'.extendFrameNonlinear hyPsi
                      (Finmap.notMem_empty : y ∉ (∅ : NLCtx))
                      (Finmap.notMem_empty : y ∉ (∅ : LCtx)) hyCtrl hyTarget
                      htof endpointPackage
                  have hincBody : NLCtxIncl
                      (Finmap.insert y (Basis.tof b0) GammaCtrl)
                      (Finmap.insert y (Basis.tof b0) GammaTarget) :=
                    NLCtxIncl.insert_same hGamma y (Basis.tof b0)
                  have hwfBody : V2.CtxWF' (∅ : LCtx)
                      (Finmap.insert y (Basis.tof b0) GammaTarget) :=
                    RawLocalCtxWFInsertionScratch.ctxWF_insert_nl hwf
                      Finmap.notMem_empty hyTarget hb0Target
                  apply ih (basisHeight (Basis.openVar y b1)) hbodyHeight
                    rfl bodyFamily hincBody hwfBody (hbody y hyL)
                  simp only [bodyBase, basisHeight, basisHeight_openVar]
                    at hbudget ⊢
                  omega

/-! ## Closing the creation-prefix seam -/

/-- The structural layer required by raw creation-prefix induction is fully
constructive.  For a prefix store at `baseDepth`, a new basis receives the
single conservative depth `baseDepth + basisHeight b`. -/
theorem checkedFreeStdCreationPrefixLayerBuilder :
    CheckedFreeStdCreationPrefixLayerBuilder := by
  intro Delta Gamma Psi b hwf hlink uniform hb
  obtain ⟨baseDepth, store⟩ := uniform
  refine ⟨baseDepth + basisHeight b, ?_⟩
  intro Psi' Gamma' hfuture hGamma hwf'
  let familyAll := CheckedRelaxedControlledSelectedFamily.of_storeAtFresh
    hlink store hfuture hGamma
  let family := familyAll.restrictLinearEmpty
  exact checkedFreeStdPairDepthQuad_of_family family hGamma hwf' hb le_rfl

end RawCertifiedPairFreeStandardCreationPrefixLayer
end GLang
