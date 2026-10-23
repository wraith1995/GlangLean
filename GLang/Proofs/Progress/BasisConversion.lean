import GLang.Proofs.Progress.Certificates.RawCertifiedProgressArms

namespace GLang
namespace RawCertifiedProgressScratch

open RawCertifiedOperational

/-- Exact inverse-erasure law missing from the current COB development.

The contexts and hereditary hypotheses are the same currency consumed by
ordinary `V2.progress_cob_master`.  Crucially, the conclusion retains its
input `env`; weakening this to `exists env'` would not be a literal completion
of the erased derivation. -/
def LiteralCheckedCobCompletion : Prop :=
  forall (Gamma : NLCtx) (Psi : EvalCtx) (b : Basis) (env : ValExpr),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.StoredWF Psi ->
    Basis.BasisValid Gamma b -> Basis.IsSpaceBasis b ->
    Basis.EvalBB Psi b env (Basis.std (Basis.tof b)) ->
    C.Cob Gamma Psi b env (Basis.std (Basis.tof b))

/-- Direct checked counterpart of `V2.progress_cob_master`. -/
def CheckedCobToStd : Prop :=
  forall (Gamma : NLCtx) (Psi : EvalCtx) (b : Basis),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.StoredWF Psi ->
    Basis.BasisValid Gamma b -> Basis.IsSpaceBasis b ->
    exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))

/-! The purely structural beginning of checked COB progress is already
constructible directly.  These lemmas make clear that the gap is not identity,
duality, or composition. -/

theorem checkedCob_empty_toStd (Gamma : NLCtx) (Psi : EvalCtx) :
    exists env, C.Cob Gamma Psi .empty env (Basis.std (Basis.tof .empty)) := by
  exact ⟨_, .refl .empty rfl .empty⟩

theorem checkedCob_one_toStd (Gamma : NLCtx) (Psi : EvalCtx) :
    exists env, C.Cob Gamma Psi .one env (Basis.std (Basis.tof .one)) := by
  exact ⟨_, .refl .one rfl .real⟩

theorem checkedCob_dual_toStd
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    (hb : Basis.BasisValid Gamma (.dual b))
    (hs : Basis.IsSpaceBasis b)
    (hchild : exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) :
    exists env,
      C.Cob Gamma Psi (.dual b) env (Basis.std (Basis.tof (.dual b))) := by
  obtain ⟨env, hcob⟩ := hchild
  obtain ⟨kind, ⟨htvalid⟩⟩ := hb.tof_tvalid
  exact ⟨_, .dual_std hs.tof_eq hb (Basis.std_valid _ htvalid) hcob⟩

/-- Ordinary COB progress plus literal inverse-erasure is exactly enough to
obtain checked COB progress. -/
theorem checkedCobToStd_of_literalCompletion
    (hcomplete : LiteralCheckedCobCompletion) : CheckedCobToStd := by
  intro Gamma Psi b hP hcov hstored hb hspace
  obtain ⟨env, henv⟩ := V2.progress_cob_master hP hcov hb hspace
  exact ⟨env, hcomplete Gamma Psi b env hP hcov hstored hb hspace henv⟩

/-- Two checked conversions to the common standard basis compose to a checked
conversion between arbitrary bases of the same source type. -/
theorem checkedCobBetween_of_toStd
    (hprogress : CheckedCobToStd)
    {Gamma : NLCtx} {Psi : EvalCtx} {b1 b2 : Basis} {sv : ValSpace}
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hb1 : Basis.BasisValid Gamma b1) (hs1 : Basis.IsSpaceBasis b1)
    (hb2 : Basis.BasisValid Gamma b2) (hs2 : Basis.IsSpaceBasis b2)
    (htof : Basis.tof b2 = Basis.tof b1)
    (hsv : C.Space Gamma Psi (Basis.sof b1) sv) :
    exists env, C.Cob Gamma Psi b1 env b2 := by
  obtain ⟨env1, hcob1⟩ := hprogress Gamma Psi b1 hP hcov hstored hb1 hs1
  obtain ⟨env2, hcob2⟩ := hprogress Gamma Psi b2 hP hcov hstored hb2 hs2
  rw [htof] at hcob2
  obtain ⟨kind, ⟨htvalid⟩⟩ := hb1.tof_tvalid
  have hstdValid : Basis.BasisValid Gamma (Basis.std (Basis.tof b1)) :=
    Basis.std_valid _ htvalid
  exact ⟨_, .trans hb1 hb2 hcob1 (.inverse hstdValid hb2 hcob2) hsv⟩

/-- Space-typed checked transport, with the newly constructed ordinary value
spelled out literally. -/
theorem checkedSpaceTermTransport_of_toStd
    (hprogress : CheckedCobToStd)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {e : Term}
    {b1 b2 : Basis} {v1 : ValExpr} {sv : ValSpace}
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hb1 : Basis.BasisValid Gamma b1) (hs1 : Basis.IsSpaceBasis b1)
    (hb2 : Basis.BasisValid Gamma b2) (hs2 : Basis.IsSpaceBasis b2)
    (htof : Basis.tof b2 = Basis.tof b1)
    (hterm : C.Term Delta Gamma Psi e b1 v1 (.space sv)) :
    exists env,
      C.Cob Gamma Psi b1 env b2 /\
      C.Term Delta Gamma Psi e b2
        (.ttv sv (ValExpr.reshapBase env (.tprod sv sv))
          (ValExpr.reshapBase v1 sv)) (.space sv) := by
  have hspace1 : C.Space Gamma Psi (Basis.sof b1) sv := by
    obtain ⟨sv', heq, hspace⟩ :=
      checkedTyAt_space_inv_full hs1.tof_eq hterm.tyAt
    injection heq with heq'
    subst sv'
    exact hspace
  have hsof : Basis.sof b2 = Basis.sof b1 :=
    V2.sof_of_tof_eq_space (htof.trans hs1.tof_eq)
  have hspace2 : C.Space Gamma Psi (Basis.sof b2) sv := by
    rw [hsof]
    exact hspace1
  obtain ⟨env, hcob⟩ := checkedCobBetween_of_toStd hprogress hP hcov hstored
    hb1 hs1 hb2 hs2 htof hspace1
  have htyped2 : Nonempty (HasType Delta Gamma e (Basis.tof b2)) := by
    rw [htof]
    exact hterm.hasType
  have htype2 : C.TyAt Gamma Psi b2 (.space sv) :=
    .space hs2.tof_eq hb2 hspace2
  exact ⟨env, hcob,
    .cob hs2.tof_eq hs1.tof_eq htyped2 hb2 htype2 hterm hcob hspace2⟩

/-- The residual higher-order obligation.  It is intentionally stated at the
same arbitrary linear context as `CheckedBasisTransport`: a proof must either
derive `Delta = ∅` from Pi typing (including through promotion), or explain
how the `C.Term.frame_eta`/`appN_val` construction is generalized. -/
def CheckedPiBasisTransport : Prop :=
  forall (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx) (e : Term)
    (tau0 tau1 : Ty) (b1 b2 : Basis) (v1 : ValExpr) (tauv1 : ValTy),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.StoredWF Psi ->
    Basis.BasisValid Gamma b1 -> Basis.IsTyBasis b1 ->
    Basis.BasisValid Gamma b2 -> Basis.IsTyBasis b2 ->
    Basis.tof b1 = .piTy tau0 tau1 ->
    Basis.tof b2 = Basis.tof b1 ->
    C.Term Delta Gamma Psi e b1 v1 tauv1 ->
    exists v2 tauv2, C.Term Delta Gamma Psi e b2 v2 tauv2

/-- A `C.TyAt` whose source type is a space cannot be a frame certificate. -/
theorem checkedTyAt_space_inv
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {s : Space} {tauv : ValTy}
    (htof : Basis.tof b = .space s) (hty : C.TyAt Gamma Psi b tauv) :
    exists sv, tauv = .space sv /\ C.Space Gamma Psi (Basis.sof b) sv := by
  exact checkedTyAt_space_inv_full htof hty

/-- The full checked transport interface factors into the checked space-COB
law above and the genuinely higher-order Pi transport. -/
theorem checkedBasisTransport_of_toStd_and_pi
    (hcob : CheckedCobToStd) (hpi : CheckedPiBasisTransport) :
    CheckedBasisTransport := by
  intro Delta Gamma Psi e b1 b2 v1 tauv1 hP hcov hstored
    hb1 hty1 hb2 hty2 htof hterm
  cases hsource : Basis.tof b1 with
  | space s =>
      have hs1 : Basis.IsSpaceBasis b1 :=
        hty1.toIsSpaceBasis (Basis.ne_frame_of_tof_space hsource)
      have hs2 : Basis.IsSpaceBasis b2 :=
        hty2.toIsSpaceBasis
          (Basis.ne_frame_of_tof_space (htof.trans hsource))
      obtain ⟨sv, htauv, _⟩ := checkedTyAt_space_inv hsource hterm.tyAt
      subst tauv1
      obtain ⟨env, _, htarget⟩ := checkedSpaceTermTransport_of_toStd hcob
        hP hcov hstored hb1 hs1 hb2 hs2 htof hterm
      exact ⟨_, _, htarget⟩
  | piTy tau0 tau1 =>
      exact hpi Delta Gamma Psi e tau0 tau1 b1 b2 v1 tauv1
        hP hcov hstored hb1 hty1 hb2 hty2 hsource htof hterm

end RawCertifiedProgressScratch
end GLang
