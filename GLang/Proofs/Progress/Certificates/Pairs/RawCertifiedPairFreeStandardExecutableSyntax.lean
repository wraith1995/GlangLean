import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairDepthMonotonicity

/-!
# Proof-relevant executable syntax for free-standard pairs

`CheckedLocalSideBasisSyntaxLayer` records the exact `HasType` witnesses used
by embedded source terms, but not the corresponding promotion-freedom proofs.
Those witnesses live in `Type`, so replacing them by a separately normalized
derivation would lose the proof index of their local-side tree.

This module supplies the smallest free-standard-only replacement: the basis
syntax is unchanged, while every embedded source witness is paired with its
promotion-freedom proof and its local-side tree in one dependent package.
The public typing judgments and the original pair certificate are untouched.
-/

namespace GLang
namespace RawCertifiedPairFreeStandardExecutableSyntax

open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairDepthMonotonicity

/-- One executable embedded term witness.  All three fields refer to the
same proof-relevant `HasType` object. -/
def CheckedFreeStdExecutableTermWitness
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    (Delta : LCtx) (Gamma : NLCtx) (e : Term) (tau : Ty) : Prop :=
  exists typing : HasType Delta Gamma e tau,
    Graded.PromotionFree typing /\
    Nonempty (CheckedLocalSideBasesWith selected Psi typing)

/-- Space-validity companion used by `.terms`. -/
def CheckedFreeStdExecutableSpaceWitness
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    (Gamma : NLCtx) (s : Space) : Prop :=
  exists validity : SValid Gamma s,
    Graded.SPromotionFree validity /\
    Nonempty (CheckedLocalSideSWith selected Psi validity)

/-- Type-validity companion used by dependent frame syntax. -/
def CheckedFreeStdExecutableTypeWitness
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    (Gamma : NLCtx) (tau : Ty) (kind : Kind) : Prop :=
  exists validity : TValid Gamma tau kind,
    Graded.TPromotionFree validity /\
    Nonempty (CheckedLocalSideTWith selected Psi validity)

/-- Positive free-standard basis syntax with proof-relevant executable source
payloads.  This mirrors `CheckedLocalSideBasisSyntaxLayer`; only the three
embedded witness fields are strengthened. -/
def CheckedFreeStdExecutableBasisSyntaxLayer
    (Psi : EvalCtx) (selected : EvalCtx → CheckedSelectedBasisSide)
    (Gamma : NLCtx) : Basis → Prop
  | .empty => True
  | .one => True
  | .dual b =>
      exists hb : Basis.BasisValid Gamma b,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b
  | .dsum b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b0) ∧
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b1)
  | .tprod b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b0) ∧
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b1)
  | .proj (.ker s0 s1 e) b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b0) ∧
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b1) ∧
      Basis.sof b0 = s0 ∧ Basis.sof b1 = s1 ∧
      CheckedFreeStdExecutableTermWitness (selected Psi) Psi
        (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))
  | .proj (.coker s0 s1 e) b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b0) ∧
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b1) ∧
      Basis.sof b0 = s0 ∧ Basis.sof b1 = s1 ∧
      CheckedFreeStdExecutableTermWitness (selected Psi) Psi
        (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))
  | .proj (.img s0 s1 e) b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b0) ∧
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b1) ∧
      Basis.sof b0 = s0 ∧ Basis.sof b1 = s1 ∧
      CheckedFreeStdExecutableTermWitness (selected Psi) Psi
        (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))
  | .proj (.coimg s0 s1 e) b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b0) ∧
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b1) ∧
      Basis.sof b0 = s0 ∧ Basis.sof b1 = s1 ∧
      CheckedFreeStdExecutableTermWitness (selected Psi) Psi
        (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))
  | .proj _ _ _ => False
  | .image b =>
      exists s0 s1 e, exists hb : Basis.BasisValid Gamma b,
        Basis.sof b = .coker s0 s1 e ∧
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b ∧
        CheckedFreeStdExecutableTermWitness (selected Psi) Psi
          (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))
  | .terms s es b =>
      (exists hb : Basis.BasisValid Gamma b,
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b) ∧
      Basis.sof b = s ∧
      CheckedFreeStdExecutableSpaceWitness (selected Psi) Psi Gamma s ∧
      forall e, e ∈ es →
        CheckedFreeStdExecutableTermWitness (selected Psi) Psi
          (∅ : LCtx) Gamma e (.space s)
  | .frame b0 b1 =>
      exists k0 k1, exists L : Finset Name,
        exists hb0 : Basis.BasisValid Gamma b0,
        exists hbody : forall y, y ∉ L →
          Basis.BasisValid (Finmap.insert y (Basis.tof b0) Gamma)
            (Basis.openVar y b1),
        CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b0 ∧
        (forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' →
          forall y (hy : y ∉ L) (bArg : Basis) (v : ValExpr),
          Basis.BasisValid Gamma bArg → Basis.tof bArg = Basis.tof b0 →
          (forall _hb0x : Basis.BasisValid
              (Finmap.insert y (Basis.tof b0) Gamma) b0,
            CheckedFreeStdExecutableBasisSyntaxLayer
              (Psi'.extend y bArg v) selected
              (Finmap.insert y (Basis.tof b0) Gamma) b0) ∧
            CheckedFreeStdExecutableBasisSyntaxLayer
              (Psi'.extend y bArg v) selected
              (Finmap.insert y (Basis.tof b0) Gamma) (Basis.openVar y b1)) ∧
        CheckedFreeStdExecutableTypeWitness (selected Psi) Psi Gamma
          (.piTy (Basis.tof b0) (Basis.tof b1)) (.arrow k0 k1)
termination_by b => Basis.size b
decreasing_by
  all_goals simp [Basis.size, Basis.size_openVar] <;> omega

/-! ## Representative proof-relevant inversions -/

/-- A projection exposes one exact embedded typing witness and its matching
promotion-freedom/local-side evidence, with no derivation cast. -/
theorem projKer_exactTermWitness
    {Psi : EvalCtx} {selected : EvalCtx → CheckedSelectedBasisSide}
    {Gamma : NLCtx} {s0 s1 : Space} {e : Term} {b0 b1 : Basis}
    (side : CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma
      (.proj (.ker s0 s1 e) b0 b1)) :
    CheckedFreeStdExecutableTermWitness (selected Psi) Psi
      (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1)) := by
  simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side
  exact side.2.2.2.2

/-- A `terms` entry exposes the exact list-member typing witness together
with its matching promotion-freedom/local-side evidence. -/
theorem terms_exactTermWitness
    {Psi : EvalCtx} {selected : EvalCtx → CheckedSelectedBasisSide}
    {Gamma : NLCtx} {s : Space} {es : List Term} {b : Basis}
    (side : CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma
      (.terms s es b)) {e : Term} (he : e ∈ es) :
    CheckedFreeStdExecutableTermWitness (selected Psi) Psi
      (∅ : LCtx) Gamma e (.space s) := by
  simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side
  exact side.2.2.2 e he

/-- The `terms` space witness is correlated in the same way. -/
theorem terms_exactSpaceWitness
    {Psi : EvalCtx} {selected : EvalCtx → CheckedSelectedBasisSide}
    {Gamma : NLCtx} {s : Space} {es : List Term} {b : Basis}
    (side : CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma
      (.terms s es b)) :
    CheckedFreeStdExecutableSpaceWitness (selected Psi) Psi Gamma s := by
  simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side
  exact side.2.2.1

/-! ## Structural transport -/

/-- Executable syntax is monotone in its selected-leaf policy.  The exact
typing/validity witnesses and their promotion-freedom proofs are preserved;
only the matching local-side trees are mapped. -/
def executableSyntaxLayer_mono
    {p q : EvalCtx → CheckedSelectedBasisSide}
    (hpq : WorldSelectedLe p q)
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis} :
    CheckedFreeStdExecutableBasisSyntaxLayer Psi p Gamma b →
      CheckedFreeStdExecutableBasisSyntaxLayer Psi q Gamma b :=
  match b with
  | .empty => fun side => by
      simpa only [CheckedFreeStdExecutableBasisSyntaxLayer] using side
  | .one => fun side => by
      simpa only [CheckedFreeStdExecutableBasisSyntaxLayer] using side
  | .dual b => fun side => by
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side ⊢
      obtain ⟨hb, child⟩ := side
      exact ⟨hb, executableSyntaxLayer_mono hpq child⟩
  | .dsum b0 b1 => fun side => by
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩⟩ := side
      exact ⟨⟨hb0, executableSyntaxLayer_mono hpq child0⟩,
        ⟨hb1, executableSyntaxLayer_mono hpq child1⟩⟩
  | .tprod b0 b1 => fun side => by
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩⟩ := side
      exact ⟨⟨hb0, executableSyntaxLayer_mono hpq child0⟩,
        ⟨hb1, executableSyntaxLayer_mono hpq child1⟩⟩
  | .proj (.ker s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, hfree, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, executableSyntaxLayer_mono hpq child0⟩,
        ⟨hb1, executableSyntaxLayer_mono hpq child1⟩,
        hsof0, hsof1, ht, hfree,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .proj (.coker s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, hfree, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, executableSyntaxLayer_mono hpq child0⟩,
        ⟨hb1, executableSyntaxLayer_mono hpq child1⟩,
        hsof0, hsof1, ht, hfree,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .proj (.img s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, hfree, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, executableSyntaxLayer_mono hpq child0⟩,
        ⟨hb1, executableSyntaxLayer_mono hpq child1⟩,
        hsof0, hsof1, ht, hfree,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .proj (.coimg s0 s1 e) b0 b1 => fun side => by
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb0, child0⟩, ⟨hb1, child1⟩,
        hsof0, hsof1, ht, hfree, ⟨termSide⟩⟩ := side
      exact ⟨⟨hb0, executableSyntaxLayer_mono hpq child0⟩,
        ⟨hb1, executableSyntaxLayer_mono hpq child1⟩,
        hsof0, hsof1, ht, hfree,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .proj .empty _ _ => fun side => by
      simpa only [CheckedFreeStdExecutableBasisSyntaxLayer] using side
  | .proj .real _ _ => fun side => by
      simpa only [CheckedFreeStdExecutableBasisSyntaxLayer] using side
  | .proj (.dual _) _ _ => fun side => by
      simpa only [CheckedFreeStdExecutableBasisSyntaxLayer] using side
  | .proj (.dsum _ _) _ _ => fun side => by
      simpa only [CheckedFreeStdExecutableBasisSyntaxLayer] using side
  | .proj (.tprod _ _) _ _ => fun side => by
      simpa only [CheckedFreeStdExecutableBasisSyntaxLayer] using side
  | .image b => fun side => by
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side ⊢
      obtain ⟨s0, s1, e, hb, hsof, child, ht, hfree, ⟨termSide⟩⟩ := side
      exact ⟨s0, s1, e, hb, hsof,
        executableSyntaxLayer_mono hpq child,
        ht, hfree,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .terms s es b => fun side => by
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side ⊢
      obtain ⟨⟨hb, child⟩, hsof,
        ⟨hs, hspaceFree, ⟨spaceSide⟩⟩, termSides⟩ := side
      refine ⟨⟨hb, executableSyntaxLayer_mono hpq child⟩, hsof,
        ⟨hs, hspaceFree,
          ⟨CheckedLocalSideSWith.monoSelected (hpq Psi) spaceSide⟩⟩, ?_⟩
      intro e he
      obtain ⟨ht, htermFree, ⟨termSide⟩⟩ := termSides e he
      exact ⟨ht, htermFree,
        ⟨CheckedLocalSideBasesWith.monoSelected (hpq Psi) termSide⟩⟩
  | .frame b0 b1 => fun side => by
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer] at side ⊢
      obtain ⟨k0, k1, L, hb0, hbody, domainSide, bodySides,
        ht, htypeFree, ⟨typeSide⟩⟩ := side
      refine ⟨k0, k1, L, hb0, hbody,
        executableSyntaxLayer_mono hpq domainSide, ?_,
        ht, htypeFree,
        ⟨CheckedLocalSideTWith.monoSelected (hpq Psi) typeSide⟩⟩
      intro Psi' hfuture y hy bArg v hbArg htof
      obtain ⟨domainSide', bodySide'⟩ :=
        bodySides Psi' hfuture y hy bArg v hbArg htof
      exact ⟨fun hb0x => executableSyntaxLayer_mono hpq (domainSide' hb0x),
        executableSyntaxLayer_mono hpq bodySide'⟩
termination_by Basis.size b
decreasing_by
  all_goals simp [Basis.size, Basis.size_openVar] <;> omega

/-- A depth-zero local basis has no embedded source programs, hence it
constructs executable syntax for every selected policy without additional
normalization evidence. -/
theorem CheckedLocalSideBasisZero.toExecutableSyntaxLayer
    {selected : EvalCtx → CheckedSelectedBasisSide}
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma b}
    (side : CheckedLocalSideBasisZero hb) :
    CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma b := by
  induction side with
  | empty => simp [CheckedFreeStdExecutableBasisSyntaxLayer]
  | one => simp [CheckedFreeStdExecutableBasisSyntaxLayer]
  | dual side ih =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      exact ⟨by assumption, ih⟩
  | dsum side0 side1 ih0 ih1 =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      exact ⟨⟨by assumption, ih0⟩, ⟨by assumption, ih1⟩⟩
  | tprod side0 side1 ih0 ih1 =>
      simp only [CheckedFreeStdExecutableBasisSyntaxLayer]
      exact ⟨⟨by assumption, ih0⟩, ⟨by assumption, ih1⟩⟩

end RawCertifiedPairFreeStandardExecutableSyntax
end GLang
