import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardStore

/-!
# Structural constructors for free-standard pair quads

These are the relaxed-certificate counterparts of the existing concrete-pair
constructors.  Nonstandard domain/body transport is unchanged.  Only the
selected predicate inside non-frame source syntax admits the terminal
standard equality.
-/

namespace GLang
namespace RawCertifiedPairFreeStandardConstruction

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate
open RawCertifiedPairFreeStandardCertificate
open RawCertifiedPairFreeStandardExecutableSyntax

/-- Assemble one positive non-frame relaxed pair from its two syntax layers. -/
theorem checkedFreeStdPairBasisDepth_nonFrame_of_syntax
    {depth : Nat} {Psi : EvalCtx} {Gamma : NLCtx}
    {source target : Basis}
    (hsource : BasisNonFrame source) (htarget : BasisNonFrame target)
    (htof : Basis.tof target = Basis.tof source)
    (sourceSide : CheckedFreeStdExecutableBasisSyntaxLayer Psi
      (fun Psi' => CheckedFreeStdSelectedAt Psi' depth) Gamma source)
    (targetSide : CheckedFreeStdExecutableBasisSyntaxLayer Psi
      (fun Psi' => CheckedFreeStdSelectedAt Psi' depth) Gamma target) :
    CheckedFreeStdPairBasisDepth Psi (depth + 1) Gamma source target := by
  have sourceSide' : CheckedFreeStdExecutableBasisSyntaxLayer Psi
      (fun Psi' {Gamma'} {b} _hb =>
        b = Basis.std (Basis.tof b) ∨
          CheckedFreeStdPairBasisDepth Psi' depth Gamma' b
            (Basis.std (Basis.tof b))) Gamma source := by
    simpa only [CheckedFreeStdSelectedAt] using sourceSide
  have targetSide' : CheckedFreeStdExecutableBasisSyntaxLayer Psi
      (fun Psi' {Gamma'} {b} _hb =>
        b = Basis.std (Basis.tof b) ∨
          CheckedFreeStdPairBasisDepth Psi' depth Gamma' b
            (Basis.std (Basis.tof b))) Gamma target := by
    simpa only [CheckedFreeStdSelectedAt] using targetSide
  cases source <;> cases target <;>
    simp_all only [BasisNonFrame, CheckedFreeStdPairBasisDepth]
  all_goals
    exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩

/-- Assemble all four non-frame orientations. -/
theorem checkedFreeStdPairDepthQuad_nonFrame_of_syntax
    {depth : Nat} {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis}
    (hsource : BasisNonFrame b)
    (htarget : BasisNonFrame (Basis.std (Basis.tof b)))
    (sourceSide : CheckedFreeStdExecutableBasisSyntaxLayer Psi
      (fun Psi' => CheckedFreeStdSelectedAt Psi' depth) Gamma b)
    (targetSide : CheckedFreeStdExecutableBasisSyntaxLayer Psi
      (fun Psi' => CheckedFreeStdSelectedAt Psi' depth) Gamma
        (Basis.std (Basis.tof b))) :
    CheckedFreeStdPairDepthQuad Psi (depth + 1) Gamma b where
  self := checkedFreeStdPairBasisDepth_nonFrame_of_syntax
    hsource hsource rfl sourceSide sourceSide
  toStd := checkedFreeStdPairBasisDepth_nonFrame_of_syntax
    hsource htarget (Basis.tof_std _) sourceSide targetSide
  fromStd := checkedFreeStdPairBasisDepth_nonFrame_of_syntax
    htarget hsource (Basis.tof_std _).symm targetSide sourceSide
  stdSelf := checkedFreeStdPairBasisDepth_nonFrame_of_syntax
    htarget htarget rfl targetSide targetSide

/-- Direct dependent-frame assembly.  The callbacks see only the two literal
endpoint domains used by the concrete frame certificate. -/
theorem checkedFreeStdPairDepthQuad_frame_of_builders
    {depth : Nat} {Psi : EvalCtx} {Gamma : NLCtx}
    {b0 b1 : Basis} {L : Finset Name}
    (hb0 : Basis.BasisValid Gamma b0)
    (hbody : forall y, y ∉ L ->
      Basis.BasisValid (Finmap.insert y (Basis.tof b0) Gamma)
        (Basis.openVar y b1))
    (domainQuad : CheckedFreeStdPairDepthQuad Psi (depth + 1) Gamma b0)
    (buildDomain : forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
      forall (y : Name), y ∉ Psi'.names -> y ∉ L ∪ Gamma.keys ->
      forall (bArg : Basis) (v : ValExpr),
      Basis.BasisValid Gamma bArg -> Basis.tof bArg = Basis.tof b0 ->
      (bArg = b0 ∨ bArg = Basis.std (Basis.tof b0)) ->
      CheckedFreeStdPairDepthQuad (Psi'.extend y bArg v) (depth + 1)
        (Finmap.insert y (Basis.tof b0) Gamma) b0)
    (buildBody : forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
      forall (y : Name), y ∉ Psi'.names -> y ∉ L ∪ Gamma.keys ->
      forall (bArg : Basis) (v : ValExpr),
      Basis.BasisValid Gamma bArg -> Basis.tof bArg = Basis.tof b0 ->
      (bArg = b0 ∨ bArg = Basis.std (Basis.tof b0)) ->
      CheckedFreeStdPairDepthQuad (Psi'.extend y bArg v) (depth + 1)
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Basis.openVar y b1)) :
    CheckedFreeStdPairDepthQuad Psi (depth + 1) Gamma (.frame b0 b1) := by
  let avoid : Finset Name := L ∪ Gamma.keys
  obtain ⟨domainKind, ⟨hdomainTy⟩⟩ := hb0.tof_tvalid
  have hstd0 : Basis.BasisValid Gamma (Basis.std (Basis.tof b0)) :=
    Basis.std_valid _ hdomainTy
  have hstdBody : forall y, y ∉ avoid ->
      Basis.BasisValid
        (Finmap.insert y (Basis.tof (Basis.std (Basis.tof b0))) Gamma)
        (Basis.openVar y (Basis.std (Basis.tof b1))) := by
    intro y hy
    have hySource : y ∉ L := by
      exact fun hmem => hy (Finset.mem_union_left _ hmem)
    have hbodyY := hbody y hySource
    obtain ⟨bodyKind, ⟨hbodyTy⟩⟩ := hbodyY.tof_tvalid
    have hstdY := Basis.std_valid _ hbodyTy
    simpa only [Basis.tof_std, Basis.tof_openRec,
      Basis.std_openVar] using hstdY
  let sourceSelf : CheckedFreeStdPairBasisDepth Psi (depth + 1) Gamma
      (.frame b0 b1) (.frame b0 b1) := by
    unfold CheckedFreeStdPairBasisDepth
    refine ⟨rfl, rfl, avoid, avoid, hb0, hb0,
      (fun y hy => hbody y (fun hm =>
        hy (Finset.mem_union_left _ hm))),
      (fun y hy => hbody y (fun hm =>
        hy (Finset.mem_union_left _ hm))),
      domainQuad.self, domainQuad.self, ?_, ?_, ?_⟩
    · intro Psi' hfuture y hyPsi hyAvoid tauV hTyAt
      exact (buildBody Psi' hfuture y hyPsi hyAvoid b0
        (.var y tauV) hb0 rfl (Or.inl rfl)).self
    · intro Psi' hfuture y hyPsi hyAvoid tauV hTyAt
      exact (buildBody Psi' hfuture y hyPsi hyAvoid b0
        (.var y tauV) hb0 rfl (Or.inl rfl)).self
    · intro Psi' hfuture y hyPsi hySource hyTarget tauV hTyAt
      let qd := buildDomain Psi' hfuture y hyPsi hySource b0
        (.var y tauV) hb0 rfl (Or.inl rfl)
      let qb := buildBody Psi' hfuture y hyPsi hySource b0
        (.var y tauV) hb0 rfl (Or.inl rfl)
      exact ⟨qd.self, qb.self⟩
  let forward : CheckedFreeStdPairBasisDepth Psi (depth + 1) Gamma
      (.frame b0 b1)
      (.frame (Basis.std (Basis.tof b0))
        (Basis.std (Basis.tof b1))) := by
    unfold CheckedFreeStdPairBasisDepth
    refine ⟨by simp only [Basis.tof_std],
      by simp only [Basis.tof_std],
      avoid, avoid, hb0, hstd0,
      (fun y hy => hbody y (fun hm =>
        hy (Finset.mem_union_left _ hm))), hstdBody,
      domainQuad.self, domainQuad.stdSelf, ?_, ?_, ?_⟩
    · intro Psi' hfuture y hyPsi hyAvoid tauV hTyAt
      exact (buildBody Psi' hfuture y hyPsi hyAvoid b0
        (.var y tauV) hb0 rfl (Or.inl rfl)).self
    · intro Psi' hfuture y hyPsi hyAvoid tauV hTyAt
      simpa only [Basis.tof_std, Basis.tof_openRec,
          Basis.std_openVar] using
        (buildBody Psi' hfuture y hyPsi hyAvoid
          (Basis.std (Basis.tof b0)) (.var y tauV) hstd0
          (Basis.tof_std _) (Or.inr rfl)).stdSelf
    · intro Psi' hfuture y hyPsi hySource hyTarget tauV hTyAt
      have qd := buildDomain Psi' hfuture y hyPsi hySource
        (Basis.std (Basis.tof b0)) (.var y tauV) hstd0
        (Basis.tof_std _) (Or.inr rfl)
      have qb := buildBody Psi' hfuture y hyPsi hySource
        (Basis.std (Basis.tof b0)) (.var y tauV) hstd0
        (Basis.tof_std _) (Or.inr rfl)
      exact ⟨by simpa only [Basis.tof_std] using qd.fromStd,
        by simpa only [Basis.tof_std, Basis.tof_openRec,
            Basis.std_openVar] using qb.toStd⟩
  let backward : CheckedFreeStdPairBasisDepth Psi (depth + 1) Gamma
      (.frame (Basis.std (Basis.tof b0))
        (Basis.std (Basis.tof b1)))
      (.frame b0 b1) := by
    unfold CheckedFreeStdPairBasisDepth
    refine ⟨by simp only [Basis.tof_std],
      by simp only [Basis.tof_std],
      avoid, avoid, hstd0, hb0, hstdBody,
      (fun y hy => hbody y (fun hm =>
        hy (Finset.mem_union_left _ hm))),
      domainQuad.stdSelf, domainQuad.self, ?_, ?_, ?_⟩
    · intro Psi' hfuture y hyPsi hyAvoid tauV hTyAt
      simpa only [Basis.tof_std, Basis.tof_openRec,
          Basis.std_openVar] using
        (buildBody Psi' hfuture y hyPsi hyAvoid
          (Basis.std (Basis.tof b0)) (.var y tauV) hstd0
          (Basis.tof_std _) (Or.inr rfl)).stdSelf
    · intro Psi' hfuture y hyPsi hyAvoid tauV hTyAt
      exact (buildBody Psi' hfuture y hyPsi hyAvoid b0
        (.var y tauV) hb0 rfl (Or.inl rfl)).self
    · intro Psi' hfuture y hyPsi hySource hyTarget tauV hTyAt
      have qd := buildDomain Psi' hfuture y hyPsi hySource b0
        (.var y tauV) hb0 rfl (Or.inl rfl)
      have qb := buildBody Psi' hfuture y hyPsi hySource b0
        (.var y tauV) hb0 rfl (Or.inl rfl)
      exact ⟨by simpa only [Basis.tof_std] using qd.toStd,
        by simpa only [Basis.tof_std, Basis.tof_openRec,
            Basis.std_openVar] using qb.fromStd⟩
  let standardSelf : CheckedFreeStdPairBasisDepth Psi (depth + 1) Gamma
      (.frame (Basis.std (Basis.tof b0))
        (Basis.std (Basis.tof b1)))
      (.frame (Basis.std (Basis.tof b0))
        (Basis.std (Basis.tof b1))) := by
    unfold CheckedFreeStdPairBasisDepth
    refine ⟨rfl, rfl, avoid, avoid, hstd0, hstd0,
      hstdBody, hstdBody, domainQuad.stdSelf,
      domainQuad.stdSelf, ?_, ?_, ?_⟩
    · intro Psi' hfuture y hyPsi hyAvoid tauV hTyAt
      simpa only [Basis.tof_std, Basis.tof_openRec,
          Basis.std_openVar] using
        (buildBody Psi' hfuture y hyPsi hyAvoid
          (Basis.std (Basis.tof b0)) (.var y tauV) hstd0
          (Basis.tof_std _) (Or.inr rfl)).stdSelf
    · intro Psi' hfuture y hyPsi hyAvoid tauV hTyAt
      simpa only [Basis.tof_std, Basis.tof_openRec,
          Basis.std_openVar] using
        (buildBody Psi' hfuture y hyPsi hyAvoid
          (Basis.std (Basis.tof b0)) (.var y tauV) hstd0
          (Basis.tof_std _) (Or.inr rfl)).stdSelf
    · intro Psi' hfuture y hyPsi hySource hyTarget tauV hTyAt
      have qd := buildDomain Psi' hfuture y hyPsi hySource
        (Basis.std (Basis.tof b0)) (.var y tauV) hstd0
        (Basis.tof_std _) (Or.inr rfl)
      have qb := buildBody Psi' hfuture y hyPsi hySource
        (Basis.std (Basis.tof b0)) (.var y tauV) hstd0
        (Basis.tof_std _) (Or.inr rfl)
      exact ⟨by simpa only [Basis.tof_std] using qd.stdSelf,
        by simpa only [Basis.tof_std, Basis.tof_openRec,
            Basis.std_openVar] using qb.stdSelf⟩
  exact ⟨sourceSelf, forward, backward, standardSelf⟩

end RawCertifiedPairFreeStandardConstruction
end GLang
