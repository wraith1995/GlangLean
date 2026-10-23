import GLang.Proofs.Progress.StandardBasisDepth
import GLang.Proofs.Adequacy.Raw.Context.RawConsistent

/-!
# Same-depth certificates for standard type bases

The source/COB depth mutual needs to transport a checked term from the
literal standard basis to the evaluator-selected basis (or conversely).
For that transport both endpoints must carry a certificate at the same
cross-edge depth.  This file constructs the standard endpoint from the
certificate rooted at the one requested basis in the call.  It is local: it
does not quantify over unrelated source types or arbitrary root bases.  The
frame case faithfully preserves the input certificate's hereditary callback
over admissible futures and same-domain-type argument bases.
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 6000

namespace GLang
namespace RawCertifiedDepthStdTySide

open RawCertifiedCobProgressMutualSpike
open RawCertifiedDepthStdSideSpike
open RawCertifiedHereditaryStore

private theorem checkedBasisZero_space_canonical
    {Gamma : NLCtx} {b : Basis} {hb : Basis.BasisValid Gamma b}
    (side : CheckedLocalSideBasisZero hb) :
    Basis.IsSpaceBasis b /\ Basis.stdSpace (Basis.sof b) = b := by
  induction side with
  | empty => exact ⟨trivial, rfl⟩
  | one => exact ⟨trivial, rfl⟩
  | dual side ih =>
      exact ⟨ih.1, by simp only [Basis.sof, Basis.stdSpace, ih.2]⟩
  | dsum side0 side1 ih0 ih1 =>
      exact ⟨⟨ih0.1, ih1.1⟩, by
        simp only [Basis.sof, Basis.stdSpace, ih0.2, ih1.2]⟩
  | tprod side0 side1 ih0 ih1 =>
      exact ⟨⟨ih0.1, ih1.1⟩, by
        simp only [Basis.sof, Basis.stdSpace, ih0.2, ih1.2]⟩

private theorem checkedStdTySideDepth_zero
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma b}
    (side : CheckedLocalSideBasisDepth Psi 0 hb) :
    exists hstd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)),
      CheckedLocalSideBasisDepth Psi 0 hstd := by
  have side0 : CheckedLocalSideBasisZero hb := by
    simpa only [CheckedLocalSideBasisDepth] using side
  obtain ⟨hspace, hcanonical⟩ := checkedBasisZero_space_canonical side0
  have heq : Basis.std (Basis.tof b) = b :=
    hspace.std_tof_eq.trans hcanonical
  rw [heq]
  exact ⟨hb, side⟩

/-- The literal standard basis of the type of one locally certified type
basis has a certificate at exactly the same cross-edge depth. -/
private def CheckedStdTySideN (size : Nat) : Prop :=
  forall {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma b},
    CheckedLocalSideBasisDepth Psi n hb ->
    Basis.IsTyBasis b -> Ty.size (Basis.tof b) <= size ->
    exists hstd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)),
      CheckedLocalSideBasisDepth Psi n hstd

private theorem checkedStdTySideN : forall size, CheckedStdTySideN size := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
    intro Psi n Gamma b hb side hi hsize
    cases n with
    | zero => exact checkedStdTySideDepth_zero side
    | succ d =>
      cases htof : Basis.tof b with
      | space s =>
          have hspace : Basis.IsSpaceBasis b :=
            hi.toIsSpaceBasis (Basis.ne_frame_of_tof_space htof)
          obtain ⟨hs, ⟨sideS⟩⟩ :=
            checkedSofSideDepth side hspace
          have hspaceTof := hspace.tof_eq
          have hseq : s = Basis.sof b := by
            rw [htof] at hspaceTof
            injection hspaceTof
          subst s
          simpa only [Basis.std] using
            ⟨Basis.stdSpace_valid _ hs, checkedStdSpaceSide sideS⟩
      | piTy tau0 tau1 =>
          obtain ⟨b0, b1, rfl, htof0, htof1⟩ :=
            Basis.tof_piTy_inv htof
          subst tau0
          subst tau1
          rw [htof] at hsize
          simp only [Ty.size] at hsize
          have hsmall0 : Ty.size (Basis.tof b0) < size := by omega
          have hsmall1 : Ty.size (Basis.tof b1) < size := by omega
          obtain ⟨k0, k1, Lb, hb0, hbody, side0, sideBody,
            htPi, ⟨sidePi⟩⟩ := side.frame_parts
          obtain ⟨hi0, hi1⟩ := hi
          obtain ⟨hbStd0, sideStd0⟩ :=
            ih _ hsmall0 side0 hi0 le_rfl
          have hstd : Basis.BasisValid Gamma
              (.frame (Basis.std (Basis.tof b0))
                (Basis.std (Basis.tof b1))) := by
            simpa only [Basis.tof_std] using Basis.std_valid _ htPi
          obtain ⟨_hbStd0', ⟨Lstd, hbodyStd0⟩, _kStd0, _kStd1,
            _htStd⟩ := hstd.frame_inv
          let L : Finset Name := Lb ∪ Lstd ∪ Gamma.keys
          have hbodyStd : forall y, y ∉ L ->
              Basis.BasisValid
                (Finmap.insert y (Basis.tof b0) Gamma)
                (Basis.openVar y (Basis.std (Basis.tof b1))) := by
            intro y hy
            have hy' := hy
            simp only [L, Finset.mem_union, not_or] at hy'
            simpa only [Basis.tof_std] using hbodyStd0 y hy'.1.2
          have sideBodyStd :
              forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
              forall y (hy : y ∉ L) (bArg : Basis) (v : ValExpr),
                Basis.BasisValid Gamma bArg ->
                Basis.tof bArg = Basis.tof b0 ->
                (forall hbStd0x : Basis.BasisValid
                    (Finmap.insert y (Basis.tof b0) Gamma)
                    (Basis.std (Basis.tof b0)),
                  CheckedLocalSideBasisDepth (Psi'.extend y bArg v)
                    (d + 1) hbStd0x) /\
                CheckedLocalSideBasisDepth (Psi'.extend y bArg v)
                  (d + 1) (hbodyStd y hy) := by
            intro Psi' hfuture y hy bArg v hbArg hArg
            have hy' := hy
            simp only [L, Finset.mem_union, not_or] at hy'
            obtain ⟨side0At, side1⟩ :=
              sideBody Psi' hfuture y hy'.1.1 bArg v hbArg hArg
            have hyGamma : y ∉ Gamma := by
              intro hm
              exact hy'.2 (Finmap.mem_keys.mpr hm)
            have hinc : NLCtxIncl Gamma
                (Finmap.insert y (Basis.tof b0) Gamma) :=
              (NLCtxIncl.refl Gamma).insert_right hyGamma _
            have hb0x : Basis.BasisValid
                (Finmap.insert y (Basis.tof b0) Gamma) b0 :=
              raw_basisValid_mono hb0 hinc
            constructor
            · intro hbStd0x
              obtain ⟨hbStd0x', sideStd0x⟩ :=
                ih _ hsmall0 (side0At hb0x) hi0 le_rfl
              have hp : hbStd0x' = hbStd0x := Subsingleton.elim _ _
              cases hp
              exact sideStd0x
            · have hsmallBody :
                  Ty.size (Basis.tof (Basis.openVar y b1)) < size := by
                simp only [Basis.openVar, Basis.tof_openRec,
                  Ty.size_openVar]
                exact hsmall1
              obtain ⟨hbStd1x, sideStd1x⟩ :=
                ih _ hsmallBody side1
                  (Basis.IsTyBasis.openRec (.var y) 0 hi1) le_rfl
              have hbasis :
                  Basis.std (Basis.tof (Basis.openVar y b1)) =
                    Basis.openVar y (Basis.std (Basis.tof b1)) := by
                simp only [Basis.openVar, Basis.tof_openRec]
                exact Basis.std_openVar y (Basis.tof b1)
              have hbStd1x' : Basis.BasisValid
                  (Finmap.insert y (Basis.tof b0) Gamma)
                  (Basis.openVar y (Basis.std (Basis.tof b1))) := by
                rw [← hbasis]
                exact hbStd1x
              have sideStd1x' : CheckedLocalSideBasisDepth
                  (Psi'.extend y bArg v) (d + 1) hbStd1x' := by
                simpa only [hbasis] using sideStd1x
              have hp : hbStd1x' = hbodyStd y hy := Subsingleton.elim _ _
              cases hp
              exact sideStd1x'
          change exists hstd : Basis.BasisValid Gamma
              (.frame (Basis.std (Basis.tof b0))
                (Basis.std (Basis.tof b1))),
            CheckedLocalSideBasisDepth Psi (d + 1) hstd
          refine ⟨hstd, ?_⟩
          cases d with
          | zero =>
              simp only [CheckedLocalSideBasisDepth,
                CheckedLocalSideBasisLayer,
                CheckedLocalSideBasisSyntaxLayer]
              refine ⟨k0, k1, L, hbStd0, ?_, ?_, ?_, ?_⟩
              · intro y hy
                simpa only [Basis.tof_std] using hbodyStd y hy
              · simpa only [CheckedLocalSideBasisDepth,
                  CheckedLocalSideBasisLayer] using sideStd0
              · simpa only [Basis.tof_std, CheckedLocalSideBasisDepth,
                  CheckedLocalSideBasisLayer] using sideBodyStd
              · rw [Basis.tof_std, Basis.tof_std]
                exact ⟨htPi, ⟨sidePi⟩⟩
          | succ d =>
              simp only [CheckedLocalSideBasisDepth,
                CheckedLocalSideBasisLayer,
                CheckedLocalSideBasisSyntaxLayer]
              refine ⟨k0, k1, L, hbStd0, ?_, ?_, ?_, ?_⟩
              · intro y hy
                simpa only [Basis.tof_std] using hbodyStd y hy
              · simpa only [CheckedLocalSideBasisDepth,
                  CheckedLocalSideBasisLayer] using sideStd0
              · simpa only [Basis.tof_std, CheckedLocalSideBasisDepth,
                  CheckedLocalSideBasisLayer] using sideBodyStd
              · rw [Basis.tof_std, Basis.tof_std]
                exact ⟨htPi, ⟨sidePi⟩⟩

/-- The literal standard basis of the type of one locally certified type
basis has a certificate at exactly the same cross-edge depth. -/
theorem checkedStdTySideDepth
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma b}
    (side : CheckedLocalSideBasisDepth Psi n hb)
    (hi : Basis.IsTyBasis b) :
    exists hstd : Basis.BasisValid Gamma (Basis.std (Basis.tof b)),
      CheckedLocalSideBasisDepth Psi n hstd :=
  checkedStdTySideN (Ty.size (Basis.tof b)) side hi le_rfl

end RawCertifiedDepthStdTySide
end GLang
