import GLang.Proofs.Progress.MutualCertificates

/-!
# Depth certificates for standard bases

Standard bases are not generally term-free: an FFS standard basis is a
projection carrying the original witness term, and a dependent standard
basis is a frame.  These lemmas show the correct statement: a source-side
certificate at depth `n` builds the corresponding standard-basis certificate
at depth `n + 1`.
-/

namespace GLang
namespace RawCertifiedDepthStdSideSpike

open RawCertifiedCobProgressMutualSpike

/-- A certified valid space supplies a certified standard space basis one
cross-edge later. -/
theorem checkedStdSpaceSide
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s : Space}
    {hs : SValid Gamma s}
    (side : CheckedLocalSideSDepth Psi0 n hs) :
    CheckedLocalSideBasisDepth Psi0 (n + 1)
      (Basis.stdSpace_valid s hs) := by
  cases hs with
  | empty =>
      simp [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer, Basis.stdSpace]
  | real =>
      simp [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer, Basis.stdSpace]
  | @dual Gamma s hs =>
      have side0 : CheckedLocalSideSDepth Psi0 n hs :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants side.deep
      simp only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer, Basis.stdSpace]
      refine ⟨Basis.stdSpace_valid s hs, ?_⟩
      simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        Basis.stdSpace] using checkedStdSpaceSide side0
  | @dsum Gamma s0 s1 hs0 hs1 =>
      have side0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2 side.deep.2
      simp only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer, Basis.stdSpace]
      constructor
      · refine ⟨Basis.stdSpace_valid s0 hs0, ?_⟩
        simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side0
      · refine ⟨Basis.stdSpace_valid s1 hs1, ?_⟩
        simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side1
  | @tprod Gamma s0 s1 hs0 hs1 =>
      have side0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2 side.deep.2
      simp only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer, Basis.stdSpace]
      constructor
      · refine ⟨Basis.stdSpace_valid s0 hs0, ?_⟩
        simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side0
      · refine ⟨Basis.stdSpace_valid s1 hs1, ?_⟩
        simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side1
  | @ker Gamma e s0 s1 hs0 hs1 ht =>
      have side0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2.1 side.deep.2.1
      have sideTerm : CheckedLocalSideBasesDepth Psi0 n ht :=
        CheckedLocalSideBasesWith.ofBelowPair
          side.shallow.descendants.2.2 side.deep.2.2
      simp only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer, Basis.stdSpace]
      refine ⟨⟨Basis.stdSpace_valid s0 hs0, ?_⟩,
        ⟨Basis.stdSpace_valid s1 hs1, ?_⟩,
        Basis.sof_stdSpace s0, Basis.sof_stdSpace s1, ht, ⟨sideTerm⟩⟩
      · simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side0
      · simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side1
  | @coker Gamma e s0 s1 hs0 hs1 ht =>
      have side0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2.1 side.deep.2.1
      have sideTerm : CheckedLocalSideBasesDepth Psi0 n ht :=
        CheckedLocalSideBasesWith.ofBelowPair
          side.shallow.descendants.2.2 side.deep.2.2
      simp only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer, Basis.stdSpace]
      refine ⟨⟨Basis.stdSpace_valid s0 hs0, ?_⟩,
        ⟨Basis.stdSpace_valid s1 hs1, ?_⟩,
        Basis.sof_stdSpace s0, Basis.sof_stdSpace s1, ht, ⟨sideTerm⟩⟩
      · simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side0
      · simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side1
  | @img Gamma e s0 s1 hs0 hs1 ht =>
      have side0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2.1 side.deep.2.1
      have sideTerm : CheckedLocalSideBasesDepth Psi0 n ht :=
        CheckedLocalSideBasesWith.ofBelowPair
          side.shallow.descendants.2.2 side.deep.2.2
      simp only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer, Basis.stdSpace]
      refine ⟨⟨Basis.stdSpace_valid s0 hs0, ?_⟩,
        ⟨Basis.stdSpace_valid s1 hs1, ?_⟩,
        Basis.sof_stdSpace s0, Basis.sof_stdSpace s1, ht, ⟨sideTerm⟩⟩
      · simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side0
      · simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side1
  | @coimg Gamma e s0 s1 hs0 hs1 ht =>
      have side0 : CheckedLocalSideSDepth Psi0 n hs0 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.1 side.deep.1
      have side1 : CheckedLocalSideSDepth Psi0 n hs1 :=
        CheckedLocalSideSWith.ofBelowPair
          side.shallow.descendants.2.1 side.deep.2.1
      have sideTerm : CheckedLocalSideBasesDepth Psi0 n ht :=
        CheckedLocalSideBasesWith.ofBelowPair
          side.shallow.descendants.2.2 side.deep.2.2
      simp only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer, Basis.stdSpace]
      refine ⟨⟨Basis.stdSpace_valid s0 hs0, ?_⟩,
        ⟨Basis.stdSpace_valid s1 hs1, ?_⟩,
        Basis.sof_stdSpace s0, Basis.sof_stdSpace s1, ht, ⟨sideTerm⟩⟩
      · simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side0
      · simpa only [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
          Basis.stdSpace] using checkedStdSpaceSide side1
termination_by Space.size s
decreasing_by
  all_goals simp_all only [Space.size] <;> omega

/-! ## Recovering a source-space side tree from a certified space basis -/

private def sideEmpty {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} :
    CheckedLocalSideSDepth Psi0 n
      (SValid.empty : SValid Gamma .empty) := by
  apply CheckedLocalSideSWith.ofBelowPair
  · exact ⟨trivial, PUnit.unit⟩
  · exact ⟨trivial, PUnit.unit⟩

private def sideReal {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} :
    CheckedLocalSideSDepth Psi0 n
      (SValid.real : SValid Gamma .real) := by
  apply CheckedLocalSideSWith.ofBelowPair
  · exact ⟨trivial, PUnit.unit⟩
  · exact ⟨trivial, PUnit.unit⟩

private def sideDual
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s : Space}
    {hs : SValid Gamma s} (side : CheckedLocalSideSDepth Psi0 n hs) :
    CheckedLocalSideSDepth Psi0 n (.dual hs) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨trivial, side.shallow.descendants⟩⟩
    ⟨trivial, ⟨trivial, side.deep⟩⟩

private def sideDsum
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1) :
    CheckedLocalSideSDepth Psi0 n (.dsum hs0 hs1) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨trivial, side1.shallow.descendants⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩, ⟨trivial, side1.deep⟩⟩⟩

private def sideTprod
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1) :
    CheckedLocalSideSDepth Psi0 n (.tprod hs0 hs1) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨trivial, side1.shallow.descendants⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩, ⟨trivial, side1.deep⟩⟩⟩

private def sideKer
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1)
    (sideT : CheckedLocalSideBasesDepth Psi0 n ht) :
    CheckedLocalSideSDepth Psi0 n (.ker hs0 hs1 ht) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def sideCoker
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1)
    (sideT : CheckedLocalSideBasesDepth Psi0 n ht) :
    CheckedLocalSideSDepth Psi0 n (.coker hs0 hs1 ht) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def sideImg
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1)
    (sideT : CheckedLocalSideBasesDepth Psi0 n ht) :
    CheckedLocalSideSDepth Psi0 n (.img hs0 hs1 ht) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

private def sideCoimg
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {e : Term} {hs0 : SValid Gamma s0} {hs1 : SValid Gamma s1}
    {ht : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))}
    (side0 : CheckedLocalSideSDepth Psi0 n hs0)
    (side1 : CheckedLocalSideSDepth Psi0 n hs1)
    (sideT : CheckedLocalSideBasesDepth Psi0 n ht) :
    CheckedLocalSideSDepth Psi0 n (.coimg hs0 hs1 ht) :=
  CheckedLocalSideSWith.ofBelowPair
    ⟨trivial, ⟨⟨trivial, side0.shallow.descendants⟩,
      ⟨⟨trivial, side1.shallow.descendants⟩,
        ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
    ⟨trivial, ⟨⟨trivial, side0.deep⟩,
      ⟨⟨trivial, side1.deep⟩,
        ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

/-- A space-basis certificate one layer above source depth `n` contains
enough information to recover the side tree of its source space at depth
`n`.  This is the key local replacement for a globally quantified side
supply in the six COB arms. -/
theorem checkedSofSideDepth
    {Psi0 : EvalCtx} {n : Nat} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma b}
    (side : CheckedLocalSideBasisDepth Psi0 (n + 1) hb)
    (hsb : Basis.IsSpaceBasis b) :
    exists hs : SValid Gamma (Basis.sof b),
      Nonempty (CheckedLocalSideSDepth Psi0 n hs) := by
  revert side hsb
  induction hb with
  | empty =>
      intro _side _hsb
      exact ⟨.empty, ⟨sideEmpty⟩⟩
  | one =>
      intro _side _hsb
      exact ⟨.real, ⟨sideReal⟩⟩
  | @dual Gamma b hb _htof ih =>
      intro side hsb
      obtain ⟨hb', side0⟩ := side.dual_child
      obtain ⟨hs, ⟨sideS⟩⟩ := ih side0 hsb
      exact ⟨.dual hs, ⟨sideDual sideS⟩⟩
  | @dsum Gamma b0 b1 hb0 hb1 _htof0 _htof1 ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩⟩ := side.dsum_children
      obtain ⟨hs0, ⟨sideS0⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1, ⟨sideS1⟩⟩ := ih1 side1 hsb.2
      exact ⟨.dsum hs0 hs1, ⟨sideDsum sideS0 sideS1⟩⟩
  | @tprod Gamma b0 b1 hb0 hb1 _htof0 _htof1 ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩⟩ := side.tprod_children
      obtain ⟨hs0, ⟨sideS0⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1, ⟨sideS1⟩⟩ := ih1 side1 hsb.2
      exact ⟨.tprod hs0 hs1, ⟨sideTprod sideS0 sideS1⟩⟩
  | @proj_ker Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, ht, ⟨sideT⟩⟩ :=
        side.proj_ker_parts
      obtain ⟨hs0', ⟨sideS0'⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1', ⟨sideS1'⟩⟩ := ih1 side1 hsb.2
      have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
      have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
      have p0 : exists hs0 : SValid Gamma s0,
          Nonempty (CheckedLocalSideSDepth Psi0 n hs0) := by
        rw [← hsof0]
        exact ⟨hs0', ⟨sideS0'⟩⟩
      have p1 : exists hs1 : SValid Gamma s1,
          Nonempty (CheckedLocalSideSDepth Psi0 n hs1) := by
        rw [← hsof1]
        exact ⟨hs1', ⟨sideS1'⟩⟩
      obtain ⟨hs0, ⟨sideS0⟩⟩ := p0
      obtain ⟨hs1, ⟨sideS1⟩⟩ := p1
      simpa only [Basis.sof] using
        ⟨SValid.ker hs0 hs1 ht, ⟨sideKer sideS0 sideS1 sideT⟩⟩
  | @proj_coker Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, ht, ⟨sideT⟩⟩ :=
        side.proj_coker_parts
      obtain ⟨hs0', ⟨sideS0'⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1', ⟨sideS1'⟩⟩ := ih1 side1 hsb.2
      have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
      have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
      have p0 : exists hs0 : SValid Gamma s0,
          Nonempty (CheckedLocalSideSDepth Psi0 n hs0) := by
        rw [← hsof0]
        exact ⟨hs0', ⟨sideS0'⟩⟩
      have p1 : exists hs1 : SValid Gamma s1,
          Nonempty (CheckedLocalSideSDepth Psi0 n hs1) := by
        rw [← hsof1]
        exact ⟨hs1', ⟨sideS1'⟩⟩
      obtain ⟨hs0, ⟨sideS0⟩⟩ := p0
      obtain ⟨hs1, ⟨sideS1⟩⟩ := p1
      simpa only [Basis.sof] using
        ⟨SValid.coker hs0 hs1 ht, ⟨sideCoker sideS0 sideS1 sideT⟩⟩
  | @proj_img Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, ht, ⟨sideT⟩⟩ :=
        side.proj_img_parts
      obtain ⟨hs0', ⟨sideS0'⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1', ⟨sideS1'⟩⟩ := ih1 side1 hsb.2
      have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
      have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
      have p0 : exists hs0 : SValid Gamma s0,
          Nonempty (CheckedLocalSideSDepth Psi0 n hs0) := by
        rw [← hsof0]
        exact ⟨hs0', ⟨sideS0'⟩⟩
      have p1 : exists hs1 : SValid Gamma s1,
          Nonempty (CheckedLocalSideSDepth Psi0 n hs1) := by
        rw [← hsof1]
        exact ⟨hs1', ⟨sideS1'⟩⟩
      obtain ⟨hs0, ⟨sideS0⟩⟩ := p0
      obtain ⟨hs1, ⟨sideS1⟩⟩ := p1
      simpa only [Basis.sof] using
        ⟨SValid.img hs0 hs1 ht, ⟨sideImg sideS0 sideS1 sideT⟩⟩
  | @proj_coimg Gamma s0 s1 e b0 b1 hb0 hb1 htof0 htof1 hw ih0 ih1 =>
      intro side hsb
      obtain ⟨⟨hb0', side0⟩, ⟨hb1', side1⟩, _, _, ht, ⟨sideT⟩⟩ :=
        side.proj_coimg_parts
      obtain ⟨hs0', ⟨sideS0'⟩⟩ := ih0 side0 hsb.1
      obtain ⟨hs1', ⟨sideS1'⟩⟩ := ih1 side1 hsb.2
      have hsof0 := Basis.sof_eq_of_tof_eq_space htof0
      have hsof1 := Basis.sof_eq_of_tof_eq_space htof1
      have p0 : exists hs0 : SValid Gamma s0,
          Nonempty (CheckedLocalSideSDepth Psi0 n hs0) := by
        rw [← hsof0]
        exact ⟨hs0', ⟨sideS0'⟩⟩
      have p1 : exists hs1 : SValid Gamma s1,
          Nonempty (CheckedLocalSideSDepth Psi0 n hs1) := by
        rw [← hsof1]
        exact ⟨hs1', ⟨sideS1'⟩⟩
      obtain ⟨hs0, ⟨sideS0⟩⟩ := p0
      obtain ⟨hs1, ⟨sideS1⟩⟩ := p1
      simpa only [Basis.sof] using
        ⟨SValid.coimg hs0 hs1 ht, ⟨sideCoimg sideS0 sideS1 sideT⟩⟩
  | @image Gamma b s0 s1 e hb hsof hw ih =>
      intro side hsb
      obtain ⟨_, _, _, hb', hsof', side0, ht, ⟨sideT⟩⟩ := side.image_parts
      obtain ⟨hs, ⟨sideS⟩⟩ := ih side0 hsb
      have p : exists hc : SValid Gamma (.coker s0 s1 e),
          Nonempty (CheckedLocalSideSDepth Psi0 n hc) := by
        rw [← hsof]
        exact ⟨hs, ⟨sideS⟩⟩
      obtain ⟨hc, ⟨sideC⟩⟩ := p
      cases hc with
      | coker hs0 hs1 ht0 =>
          have sideS0 : CheckedLocalSideSDepth Psi0 n hs0 :=
            CheckedLocalSideSWith.ofBelowPair
              sideC.shallow.descendants.1 sideC.deep.1
          have sideS1 : CheckedLocalSideSDepth Psi0 n hs1 :=
            CheckedLocalSideSWith.ofBelowPair
              sideC.shallow.descendants.2.1 sideC.deep.2.1
          have sideT0 : CheckedLocalSideBasesDepth Psi0 n ht0 :=
            CheckedLocalSideBasesWith.ofBelowPair
              sideC.shallow.descendants.2.2 sideC.deep.2.2
          rw [Basis.sof, hsof]
          exact
            ⟨SValid.img hs0 hs1 ht0, ⟨sideImg sideS0 sideS1 sideT0⟩⟩
  | @terms Gamma s es b hb htof hsv hall _hne ih =>
      intro side hsb
      obtain ⟨_, _, ⟨hs, ⟨sideS⟩⟩, _⟩ := side.terms_parts
      have hsof := Basis.sof_eq_of_tof_eq_space htof
      rw [Basis.sof, hsof]
      exact ⟨hs, ⟨sideS⟩⟩
  | frame L hb0 hbody ih0 ihbody =>
      intro _side hsb
      exact False.elim hsb

end RawCertifiedDepthStdSideSpike
end GLang
