import GLang.Proofs.Progress.BasisConversion

/-!
# Direct checked change-of-basis progress

This file reconstructs the ordinary `V2.progress_cob_master` induction with
`RawCertifiedOperational.C` witnesses.  The structural basis cases are fully
direct.  The only semantic re-entry used by the non-structural cases is
`CheckedClosedStdProgress`: checked standard-basis progress for closed-linear
typed terms.  This is deliberately narrower than the complete four-way
checked progress master and follows from `CheckedProgressOpenArms`.

The dependency is important: arbitrary source terms stored in a valid
projected/image/terms basis can contain nonlinear variables, so COB progress
cannot manufacture their checked standard evaluations merely from the erased
`PCarrier`.  Conversely, the checked variable arms are expected to use this
COB theorem to move a stored nonstandard realization to the standard basis.
The final declarations below expose that single mutual-induction seam rather
than postulating inverse erasure.
-/

namespace GLang
namespace RawCertifiedProgressScratch

open RawCertifiedOperational

/-- The exact standard-progress fragment consumed by checked COB progress.
All helper terms in the COB proof have empty linear context. -/
def CheckedClosedStdProgress : Prop :=
  forall (Gamma : NLCtx) (Psi : EvalCtx) (e : Term) (tau : Ty),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    Nonempty (HasType (∅ : LCtx) Gamma e tau) ->
    exists v tauv, C.Term (∅ : LCtx) Gamma Psi e (Basis.std tau) v tauv

/-- The already-developed 26 concrete checked arms, plus the eight explicit
open arms, provide the closed fragment needed here. -/
theorem checkedClosedStdProgress_of_openArms
    (gaps : CheckedProgressOpenArms) : CheckedClosedStdProgress := by
  intro Gamma Psi e tau hP hcov ht
  obtain ⟨ht⟩ := ht
  exact checked_term_progress_of gaps ht Psi hP hcov

/-- Checked space realization follows from the single term re-entry by
evaluating a zero literal and projecting its exact `TyAt` certificate. -/
theorem checkedSpace_of_closedStdProgress
    (hprogress : CheckedClosedStdProgress)
    {Gamma : NLCtx} {Psi : EvalCtx} {s : Space}
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hs : SValid Gamma s) :
    exists sv, C.Space Gamma Psi s sv := by
  obtain ⟨v, tauv, hv⟩ := hprogress Gamma Psi (.zero s) (.space s)
    hP hcov ⟨.zero hs⟩
  have htof : Basis.tof (Basis.std (.space s)) = .space s := Basis.tof_std _
  obtain ⟨sv, _, hsv⟩ := checkedTyAt_space_inv htof hv.tyAt
  exact ⟨sv, by simpa only [Basis.std, Basis.sof_stdSpace] using hsv⟩

/-- Re-target an induction hypothesis from `std (tof b)` to the compositional
`stdSpace (sof b)` form. -/
theorem checkedCob_stdSpace_of_stdTof
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {env : ValExpr}
    (hspace : Basis.IsSpaceBasis b)
    (h : C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) :
    C.Cob Gamma Psi b env (Basis.stdSpace (Basis.sof b)) := by
  rw [← Basis.std_tof_eq_stdSpace hspace.tof_eq]
  exact h

/-- Re-target the compositional form to the public checked-COB target. -/
theorem checkedCob_stdTof_of_stdSpace
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {env : ValExpr}
    (hspace : Basis.IsSpaceBasis b)
    (h : C.Cob Gamma Psi b env (Basis.stdSpace (Basis.sof b))) :
    C.Cob Gamma Psi b env (Basis.std (Basis.tof b)) := by
  rw [Basis.std_tof_eq_stdSpace hspace.tof_eq]
  exact h

/-- Component conversions assemble across a tensor. -/
theorem checkedCob_tprod_toStdSpace
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {env0 env1 : ValExpr}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (hs0 : Basis.IsSpaceBasis b0) (hs1 : Basis.IsSpaceBasis b1)
    (h0 : C.Cob Gamma Psi b0 env0 (Basis.stdSpace (Basis.sof b0)))
    (h1 : C.Cob Gamma Psi b1 env1 (Basis.stdSpace (Basis.sof b1))) :
    C.Cob Gamma Psi (.tprod b0 b1) (.vkrn env0 env1)
      (Basis.stdSpace (Basis.sof (.tprod b0 b1))) := by
  have hsvalid0 := Classical.choice hb0.sof_valid
  have hsvalid1 := Classical.choice hb1.sof_valid
  have htgt : Basis.BasisValid Gamma
      (.tprod (Basis.stdSpace (Basis.sof b0))
        (Basis.stdSpace (Basis.sof b1))) :=
    .tprod (Basis.stdSpace_valid _ hsvalid0)
      (Basis.stdSpace_valid _ hsvalid1)
      (Basis.htof_stdSpace _) (Basis.htof_stdSpace _)
  simpa only [Basis.stdSpace, Basis.sof] using
    C.Cob.tprod (.tprod hb0 hb1 hs0.tof_eq hs1.tof_eq) htgt h0 h1

/-- Component conversions assemble across a direct sum. -/
theorem checkedCob_dsum_toStdSpace
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {env0 env1 : ValExpr}
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (hs0 : Basis.IsSpaceBasis b0) (hs1 : Basis.IsSpaceBasis b1)
    (h0 : C.Cob Gamma Psi b0 env0 (Basis.stdSpace (Basis.sof b0)))
    (h1 : C.Cob Gamma Psi b1 env1 (Basis.stdSpace (Basis.sof b1))) :
    C.Cob Gamma Psi (.dsum b0 b1) (.vblk env0 env1)
      (Basis.stdSpace (Basis.sof (.dsum b0 b1))) := by
  have hsvalid0 := Classical.choice hb0.sof_valid
  have hsvalid1 := Classical.choice hb1.sof_valid
  have htgt : Basis.BasisValid Gamma
      (.dsum (Basis.stdSpace (Basis.sof b0))
        (Basis.stdSpace (Basis.sof b1))) :=
    .dsum (Basis.stdSpace_valid _ hsvalid0)
      (Basis.stdSpace_valid _ hsvalid1)
      (Basis.htof_stdSpace _) (Basis.htof_stdSpace _)
  simpa only [Basis.stdSpace, Basis.sof] using
    C.Cob.dsum (.dsum hb0 hb1 hs0.tof_eq hs1.tof_eq) htgt h0 h1

/-- A checked dual conversion to standard coordinates. -/
theorem checkedCob_dual_toStdSpace
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {env : ValExpr}
    (hb : Basis.BasisValid Gamma b) (hs : Basis.IsSpaceBasis b)
    (h : C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) :
    C.Cob Gamma Psi (.dual b) (.vtrans (.inv env))
      (.dual (Basis.stdSpace (Basis.sof b))) := by
  have htarget : Basis.BasisValid Gamma
      (Basis.std (Basis.tof (.dual b))) := by
    obtain ⟨k, ⟨ht⟩⟩ := (Basis.BasisValid.dual hb hs.tof_eq).tof_tvalid
    exact Basis.std_valid _ ht
  simpa only [Basis.std, Basis.tof, Basis.sof] using
    C.Cob.dual_std hs.tof_eq (.dual hb hs.tof_eq) htarget h

/-- Tensor conversion for the ubiquitous linear-map basis `a* tensor c`. -/
theorem checkedCob_tprod_dual
    {Gamma : NLCtx} {Psi : EvalCtx} {a c : Basis}
    {sa sc : Space} {enva envc : ValExpr}
    (ha : Basis.BasisValid Gamma a) (hc : Basis.BasisValid Gamma c)
    (hsa : Basis.IsSpaceBasis a) (hsc : Basis.IsSpaceBasis c)
    (hsofa : Basis.sof a = sa) (hsofc : Basis.sof c = sc)
    (hca : C.Cob Gamma Psi a enva (Basis.stdSpace sa))
    (hcc : C.Cob Gamma Psi c envc (Basis.stdSpace sc)) :
    exists env, C.Cob Gamma Psi (.tprod (.dual a) c) env
      (.tprod (.dual (Basis.stdSpace sa)) (Basis.stdSpace sc)) := by
  subst sa
  subst sc
  have hca' : C.Cob Gamma Psi a enva (Basis.std (Basis.tof a)) :=
    checkedCob_stdTof_of_stdSpace hsa hca
  have hd := checkedCob_dual_toStdSpace ha hsa hca'
  have hstdA : Basis.BasisValid Gamma (Basis.stdSpace (Basis.sof a)) :=
    Basis.stdSpace_valid _ (Classical.choice ha.sof_valid)
  have hstdC : Basis.BasisValid Gamma (Basis.stdSpace (Basis.sof c)) :=
    Basis.stdSpace_valid _ (Classical.choice hc.sof_valid)
  exact ⟨_, C.Cob.tprod
    (.tprod (.dual ha hsa.tof_eq) hc rfl hsc.tof_eq)
    (.tprod (.dual hstdA (Basis.htof_stdSpace _)) hstdC
      rfl (Basis.htof_stdSpace _)) hd hcc⟩

/-- Move a checked standard evaluation to an arbitrary space basis using a
checked conversion.  The result is a literal `C.Term.cob` node. -/
theorem checkedTerm_at_spaceBasis
    (hprogress : CheckedClosedStdProgress)
    {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {s : Space}
    {b : Basis} {envc : ValExpr} {sv : ValSpace}
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (ht : Nonempty (HasType (∅ : LCtx) Gamma e (.space s)))
    (hb : Basis.BasisValid Gamma b) (hsb : Basis.IsSpaceBasis b)
    (hsof : Basis.sof b = s)
    (hconv : C.Cob Gamma Psi b envc (Basis.stdSpace s))
    (hsv : C.Space Gamma Psi s sv) :
    exists v, C.Term (∅ : LCtx) Gamma Psi e b v (.space sv) := by
  obtain ⟨v, tauv, hv⟩ := hprogress Gamma Psi e (.space s) hP hcov ht
  have hstdValid : Basis.BasisValid Gamma (Basis.stdSpace s) := by
    have hs : SValid Gamma s := hsof ▸ Classical.choice hb.sof_valid
    exact Basis.stdSpace_valid s hs
  have hspaceB : C.Space Gamma Psi (Basis.sof b) sv := hsof.symm ▸ hsv
  have htyB : C.TyAt Gamma Psi b (.space sv) :=
    .space hsb.tof_eq hb hspaceB
  have htb : Nonempty (HasType (∅ : LCtx) Gamma e (Basis.tof b)) := by
    rw [hsb.tof_eq, hsof]
    exact ht
  have hinv : C.Cob Gamma Psi (Basis.stdSpace s) (.inv envc) b :=
    .inverse hstdValid hb hconv
  exact ⟨_, .cob hsb.tof_eq (Basis.htof_stdSpace s) htb hb htyB
    (by simpa only [Basis.std] using hv) hinv hspaceB⟩

theorem basisValid_dsumChain
    (hb : Basis.BasisValid Gamma b) (hsb : Basis.IsSpaceBasis b) :
    forall n, Basis.BasisValid Gamma (Basis.dsumChain b n)
  | 0 => hb
  | n + 1 => .dsum (basisValid_dsumChain hb hsb n) hb
      (Basis.IsSpaceBasis.dsumChain hsb n).tof_eq hsb.tof_eq

def sValid_dsumChain
    (hs : SValid Gamma s) : forall n, SValid Gamma (Space.dsumChain s n)
  | 0 => hs
  | n + 1 => .dsum (sValid_dsumChain hs n) hs

/-- Checked counterpart of the ordinary chain-conversion helper used by the
`terms` basis arm. -/
theorem checkedCob_dsumChain_toStdSpace
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {env : ValExpr}
    (hb : Basis.BasisValid Gamma b) (hsb : Basis.IsSpaceBasis b)
    (hconv : C.Cob Gamma Psi b env (Basis.stdSpace (Basis.sof b))) :
    forall n, exists env', C.Cob Gamma Psi (Basis.dsumChain b n) env'
      (Basis.stdSpace (Basis.sof (Basis.dsumChain b n)))
  | 0 => ⟨env, hconv⟩
  | n + 1 => by
      obtain ⟨env', ih⟩ := checkedCob_dsumChain_toStdSpace hb hsb hconv n
      exact ⟨_, checkedCob_dsum_toStdSpace
        (basisValid_dsumChain hb hsb n) hb
        (Basis.IsSpaceBasis.dsumChain hsb n) hsb ih hconv⟩

/-- The complete checked `terms`-basis constructor, conditional only on the
single closed standard-progress re-entry. -/
theorem checkedCob_terms_arm
    (hprogress : CheckedClosedStdProgress)
    {Gamma : NLCtx} {Psi : EvalCtx} {s : Space}
    {es : List Term} {b : Basis}
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (_hstored : V2.StoredWF Psi)
    (hb : Basis.BasisValid Gamma b) (hsof : Basis.sof b = s)
    (hsv : Nonempty (SValid Gamma s))
    (hall : forall e, e ∈ es -> Nonempty (HasType (∅ : LCtx) Gamma e (.space s)))
    (hne : es ≠ []) (hsb : Basis.IsSpaceBasis b)
    (ih : exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) :
    exists env, C.Cob Gamma Psi (.terms s es b) env
      (Basis.std (Basis.tof (.terms s es b))) := by
  obtain ⟨e0, es', rfl⟩ := List.exists_cons_of_ne_nil hne
  subst s
  obtain ⟨envc, hc0⟩ := ih
  have hc : C.Cob Gamma Psi b envc (Basis.stdSpace (Basis.sof b)) :=
    checkedCob_stdSpace_of_stdTof hsb hc0
  obtain ⟨sv, hspace⟩ := checkedSpace_of_closedStdProgress hprogress hP hcov
    (Classical.choice hsv)
  obtain ⟨envChain, hchainConv0⟩ :=
    checkedCob_dsumChain_toStdSpace hb hsb hc es'.length
  have hchainConv : C.Cob Gamma Psi (Basis.dsumChain b es'.length) envChain
      (Basis.stdSpace (Space.dsumChain (Basis.sof b) es'.length)) := by
    simpa only [Basis.sof_dsumChain] using hchainConv0
  have hchainValid := basisValid_dsumChain hb hsb es'.length
  have hchainSpace := Basis.IsSpaceBasis.dsumChain hsb es'.length
  have hchainSValid := sValid_dsumChain (Classical.choice hsv) es'.length
  obtain ⟨svChain, hsvChain⟩ := checkedSpace_of_closedStdProgress
    hprogress hP hcov hchainSValid
  have hchainSof : Basis.sof (Basis.dsumChain b es'.length) =
      Space.dsumChain (Basis.sof b) es'.length := by
    rw [Basis.sof_dsumChain]
  obtain ⟨chainValue, hchain⟩ := checkedTerm_at_spaceBasis hprogress hP hcov
    (V2.hasType_dsumChain hsv hall) hchainValid hchainSpace hchainSof
    hchainConv hsvChain
  have hstdValid : Basis.BasisValid Gamma (Basis.stdSpace (Basis.sof b)) :=
    Basis.stdSpace_valid _ (Classical.choice hsv)
  have hwhole : Basis.BasisValid Gamma (.terms (Basis.sof b) (e0 :: es') b) :=
    .terms hb hsb.tof_eq hsv hall (by simp)
  have hinv : C.Cob Gamma Psi (Basis.stdSpace (Basis.sof b)) (.inv envc) b :=
    .inverse hstdValid hb hc
  have hspaceStd : C.Space Gamma Psi
      (Basis.sof (Basis.stdSpace (Basis.sof b))) sv := by
    simpa only [Basis.sof_stdSpace] using hspace
  have hforward : C.Cob Gamma Psi (Basis.stdSpace (Basis.sof b))
      (ValExpr.reshapBase
        (.rrefRep chainValue
          (ValExpr.reshapBase (.inv envc) (.tprod sv sv)))
        (.tprod sv sv))
      (.terms (Basis.sof b) (e0 :: es') b) :=
    C.Cob.terms_rref hstdValid hwhole hinv hchain hspaceStd
  have hresult : C.Cob Gamma Psi (.terms (Basis.sof b) (e0 :: es') b)
      (.inv (ValExpr.reshapBase
        (.rrefRep chainValue
          (ValExpr.reshapBase (.inv envc) (.tprod sv sv)))
        (.tprod sv sv)))
      (Basis.stdSpace (Basis.sof b)) := .inverse hwhole hstdValid hforward
  exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hne, hsb⟩ (by
    simpa only [Basis.sof] using hresult)⟩

/-- The checked `image` arm: lift the component conversion through `image`,
then cross from the all-standard cokernel projection to the all-standard
image projection with the literal checked `image_svds` constructor. -/
theorem checkedCob_image_arm
    (hprogress : CheckedClosedStdProgress)
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    {s0 s1 : Space} {e : Term}
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (_hstored : V2.StoredWF Psi)
    (hb : Basis.BasisValid Gamma b) (hsof : Basis.sof b = .coker s0 s1 e)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (hsb : Basis.IsSpaceBasis b)
    (ih : exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) :
    exists env, C.Cob Gamma Psi (.image b) env
      (Basis.std (Basis.tof (.image b))) := by
  obtain ⟨hsourceSpace⟩ := hb.sof_valid
  rw [hsof] at hsourceSpace
  cases hsourceSpace with
  | coker hs0 hs1 hw' =>
      obtain ⟨hwt⟩ := hw
      obtain ⟨sv0, hsv0⟩ := checkedSpace_of_closedStdProgress
        hprogress hP hcov hs0
      obtain ⟨sv1, hsv1⟩ := checkedSpace_of_closedStdProgress
        hprogress hP hcov hs1
      obtain ⟨v, tauv, hev0⟩ := hprogress Gamma Psi e
        (.space (.tprod (.dual s0) s1)) hP hcov ⟨hwt⟩
      obtain ⟨v', hsvb, hev⟩ := checked_ffs_witness
        hs0 hs1 hsv0 hsv1 hev0
      let svc : ValSpace :=
        .ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v' (.tprod sv0 sv1))
      let svi : ValSpace :=
        .ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v' (.tprod sv0 sv1))
      have hcokerSpace : C.Space Gamma Psi (.coker s0 s1 e) svc :=
        .coker ⟨.coker hs0 hs1 hwt⟩ (Basis.sof_stdSpace _)
          ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
          hsvb hev
      have himgSpace : C.Space Gamma Psi (.img s0 s1 e) svi :=
        .img ⟨.img hs0 hs1 hwt⟩ (Basis.sof_stdSpace _)
          ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
          hsvb hev
      obtain ⟨envc, hc0⟩ := ih
      have hc : C.Cob Gamma Psi b envc
          (Basis.stdSpace (.coker s0 s1 e)) := by
        have hc' := checkedCob_stdSpace_of_stdTof hsb hc0
        simpa only [hsof] using hc'
      have hstd0 : Basis.BasisValid Gamma (Basis.stdSpace s0) :=
        Basis.stdSpace_valid s0 hs0
      have hstd1 : Basis.BasisValid Gamma (Basis.stdSpace s1) :=
        Basis.stdSpace_valid s1 hs1
      have hstdCoker : Basis.BasisValid Gamma
          (Basis.stdSpace (.coker s0 s1 e)) :=
        Basis.stdSpace_valid _ (.coker hs0 hs1 hwt)
      have hsource : Basis.BasisValid Gamma (.image b) :=
        .image hb hsof ⟨hwt⟩
      have hmid : Basis.BasisValid Gamma
          (.image (Basis.stdSpace (.coker s0 s1 e))) :=
        .image hstdCoker (Basis.sof_stdSpace _) ⟨hwt⟩
      have htarget : Basis.BasisValid Gamma
          (.proj (.img s0 s1 e) (Basis.stdSpace s0) (Basis.stdSpace s1)) :=
        .proj_img hstd0 hstd1 (Basis.tof_stdSpace s0)
          (Basis.tof_stdSpace s1) ⟨hwt⟩
      have hstep1 : C.Cob Gamma Psi (.image b) envc
          (.image (Basis.stdSpace (.coker s0 s1 e))) :=
        .image hsource hmid ⟨s0, s1, e, hsof⟩ hc
      have hstep2 : C.Cob Gamma Psi
          (.image (Basis.stdSpace (.coker s0 s1 e)))
          (ValExpr.reshap (.imageCoords (.tprod sv0 sv1) v')
            (.space (.tprod svc svi))
            (.space (ValExpr.inferSpaceCtx [] (.imageCoords (.tprod sv0 sv1) v'))))
          (.proj (.img s0 s1 e) (Basis.stdSpace s0) (Basis.stdSpace s1)) := by
        simpa only [Basis.stdSpace, Basis.sof_stdSpace, svc, svi] using
          C.Cob.image_svds hmid htarget
            (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
            (Basis.isStd_stdSpace s0) (Basis.isStd_stdSpace s1) hsvb hev
      have hsourceRealized : C.Space Gamma Psi (Basis.sof (.image b)) svi := by
        simpa only [Basis.sof, hsof] using himgSpace
      have htrans := C.Cob.trans hsource htarget hstep1 hstep2 hsourceRealized
      have hex : exists env, C.Cob Gamma Psi (.image b) env
          (Basis.stdSpace (Basis.sof (.image b))) := by
        exact ⟨_, by
          simpa only [Basis.stdSpace, Basis.sof, hsof] using htrans⟩
      obtain ⟨out, hout⟩ := hex
      exact ⟨out, checkedCob_stdTof_of_stdSpace hsb hout⟩

/-! ## Checked projection kit -/

/-- Evaluate the inner product at an arbitrary component basis, using only
the component's checked conversion to standard coordinates. -/
theorem checkedInner_at_spaceBasis
    (hprogress : CheckedClosedStdProgress)
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {s : Space}
    {envc : ValExpr} {sv : ValSpace}
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hb : Basis.BasisValid Gamma b) (hsb : Basis.IsSpaceBasis b)
    (hsof : Basis.sof b = s)
    (hconv : C.Cob Gamma Psi b envc (Basis.stdSpace s))
    (hs : SValid Gamma s) (hsv : C.Space Gamma Psi s sv) :
    exists v, C.Term (∅ : LCtx) Gamma Psi (.inner s)
      (.tprod (.dual b) (.dual b)) v (.space (.tprod sv sv)) := by
  have hconvTof : C.Cob Gamma Psi b envc (Basis.std (Basis.tof b)) := by
    apply checkedCob_stdTof_of_stdSpace hsb
    simpa only [hsof] using hconv
  have hdual := checkedCob_dual_toStdSpace hb hsb hconvTof
  have hstd : Basis.BasisValid Gamma (Basis.stdSpace s) :=
    Basis.stdSpace_valid s hs
  have hsource : Basis.BasisValid Gamma (.tprod (.dual b) (.dual b)) :=
    .tprod (.dual hb hsb.tof_eq) (.dual hb hsb.tof_eq) rfl rfl
  have htarget : Basis.BasisValid Gamma
      (.tprod (.dual (Basis.stdSpace s)) (.dual (Basis.stdSpace s))) :=
    .tprod (.dual hstd (Basis.htof_stdSpace s))
      (.dual hstd (Basis.htof_stdSpace s)) rfl rfl
  have hdual' : C.Cob Gamma Psi (.dual b) (.vtrans (.inv envc))
      (.dual (Basis.stdSpace s)) := by
    simpa only [hsof] using hdual
  have htp0 := C.Cob.tprod hsource htarget hdual' hdual'
  have htp : C.Cob Gamma Psi (.tprod (.dual b) (.dual b))
      (.vkrn (.vtrans (.inv envc)) (.vtrans (.inv envc)))
      (Basis.stdSpace (.tprod (.dual s) (.dual s))) := by
    simpa only [Basis.stdSpace, Basis.sof, hsof] using htp0
  have hsvOut : C.Space Gamma Psi (.tprod (.dual s) (.dual s))
      (.tprod sv sv) :=
    .tprod ⟨.tprod (.dual hs) (.dual hs)⟩
      (.dual ⟨.dual hs⟩ hsv) (.dual ⟨.dual hs⟩ hsv)
  have htype : Nonempty (HasType (∅ : LCtx) Gamma (.inner s)
      (.space (.tprod (.dual s) (.dual s)))) := ⟨.inner hs⟩
  have hsofOut : Basis.sof (.tprod (.dual b) (.dual b)) =
      .tprod (.dual s) (.dual s) := by
    simp only [Basis.sof, hsof]
  exact checkedTerm_at_spaceBasis hprogress hP hcov htype hsource
    ⟨hsb, hsb⟩ hsofOut htp hsvOut

theorem checkedMapTerm_at_bases
    (hprogress : CheckedClosedStdProgress)
    {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {s0 s1 : Space}
    {c0 c1 : Basis} {env0 env1 : ValExpr} {sv0 sv1 : ValSpace}
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (ht : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (hc0 : Basis.BasisValid Gamma c0) (hc1 : Basis.BasisValid Gamma c1)
    (hsb0 : Basis.IsSpaceBasis c0) (hsb1 : Basis.IsSpaceBasis c1)
    (hsof0 : Basis.sof c0 = s0) (hsof1 : Basis.sof c1 = s1)
    (hconv0 : C.Cob Gamma Psi c0 env0 (Basis.stdSpace s0))
    (hconv1 : C.Cob Gamma Psi c1 env1 (Basis.stdSpace s1))
    (hsv0 : C.Space Gamma Psi s0 sv0) (hsv1 : C.Space Gamma Psi s1 sv1) :
    exists v, C.Term (∅ : LCtx) Gamma Psi e (.tprod (.dual c0) c1) v
      (.space (.tprod sv0 sv1)) := by
  obtain ⟨env, hmapConv0⟩ := checkedCob_tprod_dual hc0 hc1 hsb0 hsb1
    hsof0 hsof1 hconv0 hconv1
  have hmapConv : C.Cob Gamma Psi (.tprod (.dual c0) c1) env
      (Basis.stdSpace (.tprod (.dual s0) s1)) := by
    simpa only [Basis.stdSpace] using hmapConv0
  have hsource : Basis.BasisValid Gamma (.tprod (.dual c0) c1) :=
    .tprod (.dual hc0 hsb0.tof_eq) hc1 rfl hsb1.tof_eq
  have hs0 : SValid Gamma s0 := hsof0 ▸ Classical.choice hc0.sof_valid
  have hs1 : SValid Gamma s1 := hsof1 ▸ Classical.choice hc1.sof_valid
  have hsvMap : C.Space Gamma Psi (.tprod (.dual s0) s1)
      (.tprod sv0 sv1) :=
    .tprod ⟨.tprod (.dual hs0) hs1⟩
      (.dual ⟨.dual hs0⟩ hsv0) hsv1
  have hsofMap : Basis.sof (.tprod (.dual c0) c1) =
      .tprod (.dual s0) s1 := by simp only [Basis.sof, hsof0, hsof1]
  exact checkedTerm_at_spaceBasis hprogress hP hcov ht hsource
    ⟨hsb0, hsb1⟩ hsofMap hmapConv hsvMap

/-- Direct checked embedding dispatcher for kernel/cokernel projected bases.
The resulting FFS realization is tied to the exact witness evaluation `he`. -/
theorem checkedEmbed_domside
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term} {s : Space}
    {c0 c1 : Basis} {v vi0 vi1 : ValExpr} {sv0 sv1 : ValSpace}
    (hsOr : s = .ker s0 s1 e ∨ s = .coker s0 s1 e)
    (hc0 : Basis.BasisValid Gamma c0) (hc1 : Basis.BasisValid Gamma c1)
    (hsof0 : Basis.sof c0 = s0) (hsof1 : Basis.sof c1 = s1)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (hwt : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1)))
    (hsv0 : C.Space Gamma Psi s0 sv0) (hsv1 : C.Space Gamma Psi s1 sv1)
    (hi0 : C.Term (∅ : LCtx) Gamma Psi (.inner s0)
      (.tprod (.dual c0) (.dual c0)) vi0 (.space (.tprod sv0 sv0)))
    (hi1 : C.Term (∅ : LCtx) Gamma Psi (.inner s1)
      (.tprod (.dual c1) (.dual c1)) vi1 (.space (.tprod sv1 sv1)))
    (he : C.Term (∅ : LCtx) Gamma Psi e (.tprod (.dual c0) c1) v
      (.space (.tprod sv0 sv1))) :
    exists svS w,
      C.Space Gamma Psi s svS ∧
      C.Term (∅ : LCtx) Gamma Psi (Term.lembd s)
        (.tprod (.dual (.proj s c0 c1)) c0) w
        (.space (.tprod svS sv0)) := by
  have hsb0 : Basis.IsSpaceBasis c0 :=
    (show Basis.IsSpaceBasis (.tprod (.dual c0) (.dual c0)) from
      hi0.tyAt.isTyBasis).1
  have hsb1 : Basis.IsSpaceBasis c1 :=
    (show Basis.IsSpaceBasis (.tprod (.dual c1) (.dual c1)) from
      hi1.tyAt.isTyBasis).1
  have htof0 : Basis.tof c0 = .space s0 :=
    hsb0.tof_eq.trans (congrArg Ty.space hsof0)
  have htof1 : Basis.tof c1 = .space s1 :=
    hsb1.tof_eq.trans (congrArg Ty.space hsof1)
  have hsvMap : C.Space Gamma Psi (Basis.sof (.tprod (.dual c0) c1))
      (.tprod sv0 sv1) := by
    simpa only [Basis.sof, hsof0, hsof1] using
      (C.Space.tprod ⟨SValid.tprod (.dual hs0) hs1⟩
        (C.Space.dual ⟨.dual hs0⟩ hsv0) hsv1)
  rcases hsOr with rfl | rfl
  · let svS : ValSpace := .ffs .kernel (.tprod sv0 sv1)
      (ValExpr.reshapBase v (.tprod sv0 sv1))
    have hS : C.Space Gamma Psi (.ker s0 s1 e) svS :=
      .ker ⟨.ker hs0 hs1 hwt⟩
        (by simp only [Basis.sof, hsof0, hsof1])
        ⟨c0, c1, rfl⟩ hsvMap he
    have hproj : Basis.BasisValid Gamma (.proj (.ker s0 s1 e) c0 c1) :=
      .proj_ker hc0 hc1 htof0 htof1 ⟨hwt⟩
    have hbOut : Basis.BasisValid Gamma
        (.tprod (.dual (.proj (.ker s0 s1 e) c0 c1)) c0) :=
      .tprod (.dual hproj rfl) hc0 rfl hsb0.tof_eq
    have hsvOut : C.Space Gamma Psi
        (.tprod (.dual (.ker s0 s1 e)) s0) (.tprod svS sv0) :=
      .tprod ⟨.tprod (.dual (.ker hs0 hs1 hwt)) hs0⟩
        (.dual ⟨.dual (.ker hs0 hs1 hwt)⟩ hS) hsv0
    have htyOut : C.TyAt Gamma Psi
        (.tprod (.dual (.proj (.ker s0 s1 e) c0 c1)) c0)
        (.space (.tprod svS sv0)) :=
      .space rfl hbOut (by
        simpa only [Basis.sof, hsof0] using hsvOut)
    have htOut : Nonempty (HasType (∅ : LCtx) Gamma
        (Term.lembd (.ker s0 s1 e))
        (Basis.tof (.tprod (.dual (.proj (.ker s0 s1 e) c0 c1)) c0))) := by
      simpa only [Basis.tof, Basis.sof, hsof0] using
        (show Nonempty (HasType (∅ : LCtx) Gamma
          (Term.lembd (.ker s0 s1 e))
          (.space (.tprod (.dual (.ker s0 s1 e)) s0))) from
          ⟨HasType.lembd (.sub_ker hs0 hs1 hwt)⟩)
    exact ⟨svS, _, hS,
      C.Term.embed_ker hsof0 hsof1 htOut hbOut htyOut hi0 hi1 he⟩
  · let svS : ValSpace := .ffs .cokernel (.tprod sv0 sv1)
      (ValExpr.reshapBase v (.tprod sv0 sv1))
    have hS : C.Space Gamma Psi (.coker s0 s1 e) svS :=
      .coker ⟨.coker hs0 hs1 hwt⟩
        (by simp only [Basis.sof, hsof0, hsof1])
        ⟨c0, c1, rfl⟩ hsvMap he
    have hproj : Basis.BasisValid Gamma (.proj (.coker s0 s1 e) c0 c1) :=
      .proj_coker hc0 hc1 htof0 htof1 ⟨hwt⟩
    have hbOut : Basis.BasisValid Gamma
        (.tprod (.dual (.proj (.coker s0 s1 e) c0 c1)) c0) :=
      .tprod (.dual hproj rfl) hc0 rfl hsb0.tof_eq
    have hsvOut : C.Space Gamma Psi
        (.tprod (.dual (.coker s0 s1 e)) s0) (.tprod svS sv0) :=
      .tprod ⟨.tprod (.dual (.coker hs0 hs1 hwt)) hs0⟩
        (.dual ⟨.dual (.coker hs0 hs1 hwt)⟩ hS) hsv0
    have htyOut : C.TyAt Gamma Psi
        (.tprod (.dual (.proj (.coker s0 s1 e) c0 c1)) c0)
        (.space (.tprod svS sv0)) :=
      .space rfl hbOut (by
        simpa only [Basis.sof, hsof0] using hsvOut)
    have htOut : Nonempty (HasType (∅ : LCtx) Gamma
        (Term.lembd (.coker s0 s1 e))
        (Basis.tof (.tprod (.dual (.proj (.coker s0 s1 e) c0 c1)) c0))) := by
      simpa only [Basis.tof, Basis.sof, hsof0] using
        (show Nonempty (HasType (∅ : LCtx) Gamma
          (Term.lembd (.coker s0 s1 e))
          (.space (.tprod (.dual (.coker s0 s1 e)) s0))) from
          ⟨HasType.lembd (.sub_coker hs0 hs1 hwt)⟩)
    exact ⟨svS, _, hS,
      C.Term.embed_coker hsof0 hsof1 htOut hbOut htyOut hi0 hi1 he⟩

/-- Direct checked embedding dispatcher for image/coimage projected bases. -/
theorem checkedEmbed_codside
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term} {s : Space}
    {c0 c1 : Basis} {v vi0 vi1 : ValExpr} {sv0 sv1 : ValSpace}
    (hsOr : s = .img s0 s1 e ∨ s = .coimg s0 s1 e)
    (hc0 : Basis.BasisValid Gamma c0) (hc1 : Basis.BasisValid Gamma c1)
    (hsof0 : Basis.sof c0 = s0) (hsof1 : Basis.sof c1 = s1)
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (hwt : HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1)))
    (hsv0 : C.Space Gamma Psi s0 sv0) (hsv1 : C.Space Gamma Psi s1 sv1)
    (hi0 : C.Term (∅ : LCtx) Gamma Psi (.inner s0)
      (.tprod (.dual c0) (.dual c0)) vi0 (.space (.tprod sv0 sv0)))
    (hi1 : C.Term (∅ : LCtx) Gamma Psi (.inner s1)
      (.tprod (.dual c1) (.dual c1)) vi1 (.space (.tprod sv1 sv1)))
    (he : C.Term (∅ : LCtx) Gamma Psi e (.tprod (.dual c0) c1) v
      (.space (.tprod sv0 sv1))) :
    exists svS w,
      C.Space Gamma Psi s svS ∧
      C.Term (∅ : LCtx) Gamma Psi (Term.lembd s)
        (.tprod (.dual (.proj s c0 c1)) c1) w
        (.space (.tprod svS sv1)) := by
  have hsb0 : Basis.IsSpaceBasis c0 :=
    (show Basis.IsSpaceBasis (.tprod (.dual c0) (.dual c0)) from
      hi0.tyAt.isTyBasis).1
  have hsb1 : Basis.IsSpaceBasis c1 :=
    (show Basis.IsSpaceBasis (.tprod (.dual c1) (.dual c1)) from
      hi1.tyAt.isTyBasis).1
  have htof0 : Basis.tof c0 = .space s0 :=
    hsb0.tof_eq.trans (congrArg Ty.space hsof0)
  have htof1 : Basis.tof c1 = .space s1 :=
    hsb1.tof_eq.trans (congrArg Ty.space hsof1)
  have hsvMap : C.Space Gamma Psi (Basis.sof (.tprod (.dual c0) c1))
      (.tprod sv0 sv1) := by
    simpa only [Basis.sof, hsof0, hsof1] using
      (C.Space.tprod ⟨SValid.tprod (.dual hs0) hs1⟩
        (C.Space.dual ⟨.dual hs0⟩ hsv0) hsv1)
  rcases hsOr with rfl | rfl
  · let svS : ValSpace := .ffs .image (.tprod sv0 sv1)
      (ValExpr.reshapBase v (.tprod sv0 sv1))
    have hS : C.Space Gamma Psi (.img s0 s1 e) svS :=
      .img ⟨.img hs0 hs1 hwt⟩
        (by simp only [Basis.sof, hsof0, hsof1])
        ⟨c0, c1, rfl⟩ hsvMap he
    have hproj : Basis.BasisValid Gamma (.proj (.img s0 s1 e) c0 c1) :=
      .proj_img hc0 hc1 htof0 htof1 ⟨hwt⟩
    have hbOut : Basis.BasisValid Gamma
        (.tprod (.dual (.proj (.img s0 s1 e) c0 c1)) c1) :=
      .tprod (.dual hproj rfl) hc1 rfl hsb1.tof_eq
    have hsvOut : C.Space Gamma Psi
        (.tprod (.dual (.img s0 s1 e)) s1) (.tprod svS sv1) :=
      .tprod ⟨.tprod (.dual (.img hs0 hs1 hwt)) hs1⟩
        (.dual ⟨.dual (.img hs0 hs1 hwt)⟩ hS) hsv1
    have htyOut : C.TyAt Gamma Psi
        (.tprod (.dual (.proj (.img s0 s1 e) c0 c1)) c1)
        (.space (.tprod svS sv1)) :=
      .space rfl hbOut (by simpa only [Basis.sof, hsof1] using hsvOut)
    have htOut : Nonempty (HasType (∅ : LCtx) Gamma
        (Term.lembd (.img s0 s1 e))
        (Basis.tof (.tprod (.dual (.proj (.img s0 s1 e) c0 c1)) c1))) := by
      simpa only [Basis.tof, Basis.sof, hsof1] using
        (show Nonempty (HasType (∅ : LCtx) Gamma
          (Term.lembd (.img s0 s1 e))
          (.space (.tprod (.dual (.img s0 s1 e)) s1))) from
          ⟨HasType.lembd (.sub_img hs0 hs1 hwt)⟩)
    exact ⟨svS, _, hS,
      C.Term.embed_img hsof0 hsof1 htOut hbOut htyOut hi0 hi1 he⟩
  · let svS : ValSpace := .ffs .coimage (.tprod sv0 sv1)
      (ValExpr.reshapBase v (.tprod sv0 sv1))
    have hS : C.Space Gamma Psi (.coimg s0 s1 e) svS :=
      .coimg ⟨.coimg hs0 hs1 hwt⟩
        (by simp only [Basis.sof, hsof0, hsof1])
        ⟨c0, c1, rfl⟩ hsvMap he
    have hproj : Basis.BasisValid Gamma (.proj (.coimg s0 s1 e) c0 c1) :=
      .proj_coimg hc0 hc1 htof0 htof1 ⟨hwt⟩
    have hbOut : Basis.BasisValid Gamma
        (.tprod (.dual (.proj (.coimg s0 s1 e) c0 c1)) c1) :=
      .tprod (.dual hproj rfl) hc1 rfl hsb1.tof_eq
    have hsvOut : C.Space Gamma Psi
        (.tprod (.dual (.coimg s0 s1 e)) s1) (.tprod svS sv1) :=
      .tprod ⟨.tprod (.dual (.coimg hs0 hs1 hwt)) hs1⟩
        (.dual ⟨.dual (.coimg hs0 hs1 hwt)⟩ hS) hsv1
    have htyOut : C.TyAt Gamma Psi
        (.tprod (.dual (.proj (.coimg s0 s1 e) c0 c1)) c1)
        (.space (.tprod svS sv1)) :=
      .space rfl hbOut (by simpa only [Basis.sof, hsof1] using hsvOut)
    have htOut : Nonempty (HasType (∅ : LCtx) Gamma
        (Term.lembd (.coimg s0 s1 e))
        (Basis.tof (.tprod (.dual (.proj (.coimg s0 s1 e) c0 c1)) c1))) := by
      simpa only [Basis.tof, Basis.sof, hsof1] using
        (show Nonempty (HasType (∅ : LCtx) Gamma
          (Term.lembd (.coimg s0 s1 e))
          (.space (.tprod (.dual (.coimg s0 s1 e)) s1))) from
          ⟨HasType.lembd (.sub_coimg hs0 hs1 hwt)⟩)
    exact ⟨svS, _, hS,
      C.Term.embed_coimg hsof0 hsof1 htOut hbOut htyOut hi0 hi1 he⟩

/-- Literal checked reflexivity at a standard space basis. -/
theorem checkedCob_refl_stdSpace
    {Gamma : NLCtx} {Psi : EvalCtx} {s : Space} {sv : ValSpace}
    (hs : SValid Gamma s) (hsv : C.Space Gamma Psi s sv) :
    C.Cob Gamma Psi (Basis.stdSpace s)
      (.reshap (.idelta sv) (.space (.tprod sv sv)) (.space (.tprod sv sv)))
      (Basis.stdSpace s) := by
  exact .refl (Basis.stdSpace_valid s hs) (Basis.htof_stdSpace s)
    (by simpa only [Basis.sof_stdSpace] using hsv)

/-- The complete checked projection construction for the domain-side
kernel/cokernel pair.  It follows the ordinary proof's all-standard -> mixed
-> arbitrary dependency order, but every intermediate term and COB remains a
literal `C` derivation. -/
theorem checkedCob_proj_dom_arm
    (hprogress : CheckedClosedStdProgress)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 : Basis}
    (hsOr : s = .ker s0 s1 e ∨ s = .coker s0 s1 e)
    (hsS : SValid Gamma s) (hsub : SubType Gamma s s0)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (_hstored : V2.StoredWF Psi)
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (hsof0 : Basis.sof b0 = s0) (hsof1 : Basis.sof b1 = s1)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj s b0 b1) env
      (Basis.std (Basis.tof (.proj s b0 b1))) := by
  obtain ⟨hwt⟩ := hw
  have htof0 : Basis.tof b0 = .space s0 :=
    hsb0.tof_eq.trans (congrArg Ty.space hsof0)
  have htof1 : Basis.tof b1 = .space s1 :=
    hsb1.tof_eq.trans (congrArg Ty.space hsof1)
  have hs0 : SValid Gamma s0 := hsof0 ▸ Classical.choice hb0.sof_valid
  have hs1 : SValid Gamma s1 := hsof1 ▸ Classical.choice hb1.sof_valid
  have hstdS : Basis.stdSpace s =
      .proj s (Basis.stdSpace s0) (Basis.stdSpace s1) := by
    rcases hsOr with rfl | rfl <;> rfl
  obtain ⟨sv0, hsv0⟩ := checkedSpace_of_closedStdProgress hprogress hP hcov hs0
  obtain ⟨sv1, hsv1⟩ := checkedSpace_of_closedStdProgress hprogress hP hcov hs1
  obtain ⟨env0, hc00⟩ := ih0
  obtain ⟨env1, hc10⟩ := ih1
  have hc0 : C.Cob Gamma Psi b0 env0 (Basis.stdSpace s0) := by
    have h := checkedCob_stdSpace_of_stdTof hsb0 hc00
    simpa only [hsof0] using h
  have hc1 : C.Cob Gamma Psi b1 env1 (Basis.stdSpace s1) := by
    have h := checkedCob_stdSpace_of_stdTof hsb1 hc10
    simpa only [hsof1] using h
  let refl0 := checkedCob_refl_stdSpace hs0 hsv0
  let refl1 := checkedCob_refl_stdSpace hs1 hsv1
  obtain ⟨vi0, hi0⟩ := checkedInner_at_spaceBasis hprogress hP hcov
    hb0 hsb0 hsof0 hc0 hs0 hsv0
  obtain ⟨vi1, hi1⟩ := checkedInner_at_spaceBasis hprogress hP hcov
    hb1 hsb1 hsof1 hc1 hs1 hsv1
  have hi0std := checked_inner_at hs0 hsv0
  have hi1std := checked_inner_at hs1 hsv1
  have hstd0 : Basis.BasisValid Gamma (Basis.stdSpace s0) :=
    Basis.stdSpace_valid s0 hs0
  have hstd1 : Basis.BasisValid Gamma (Basis.stdSpace s1) :=
    Basis.stdSpace_valid s1 hs1
  -- Witness evaluations at arbitrary, one-sided-standard, and all-standard bases.
  obtain ⟨ve1, he1⟩ := checkedMapTerm_at_bases hprogress hP hcov ⟨hwt⟩
    hb0 hb1 hsb0 hsb1 hsof0 hsof1 hc0 hc1 hsv0 hsv1
  obtain ⟨ve2, he2⟩ := checkedMapTerm_at_bases hprogress hP hcov ⟨hwt⟩
    hb0 hstd1 hsb0 (Basis.isSpaceBasis_stdSpace s1)
    hsof0 (Basis.sof_stdSpace s1) hc0 refl1 hsv0 hsv1
  obtain ⟨ve3, he3⟩ := checkedMapTerm_at_bases hprogress hP hcov ⟨hwt⟩
    hstd0 hstd1 (Basis.isSpaceBasis_stdSpace s0)
    (Basis.isSpaceBasis_stdSpace s1)
    (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    refl0 refl1 hsv0 hsv1
  -- Step 1: all-standard embed and projection.
  obtain ⟨svS3, em3, hS3, hem3⟩ := checkedEmbed_domside hsOr
    hstd0 hstd1 (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    hs0 hs1 hwt hsv0 hsv1 hi0std hi1std he3
  have hP3 : Basis.BasisValid Gamma
      (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) := by
    rcases hsOr with rfl | rfl
    · exact .proj_ker hstd0 hstd1 (Basis.tof_stdSpace s0)
        (Basis.tof_stdSpace s1) ⟨hwt⟩
    · exact .proj_coker hstd0 hstd1 (Basis.tof_stdSpace s0)
        (Basis.tof_stdSpace s1) ⟨hwt⟩
  have hprojOutValid : Basis.BasisValid Gamma
      (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))) :=
    .tprod (.dual hstd0 (Basis.htof_stdSpace s0)) hP3 rfl rfl
  have hsvProjOut : C.Space Gamma Psi (.tprod (.dual s0) s)
      (.tprod sv0 svS3) :=
    .tprod ⟨.tprod (.dual hs0) hsS⟩ (.dual ⟨.dual hs0⟩ hsv0) hS3
  have htyProjOut : C.TyAt Gamma Psi
      (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.space (.tprod sv0 svS3)) :=
    .space rfl hprojOutValid (by
      simpa only [Basis.sof, Basis.sof_stdSpace] using hsvProjOut)
  have htProjOut : Nonempty (HasType (∅ : LCtx) Gamma
      (Term.lproj s s0)
      (Basis.tof (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType (∅ : LCtx) Gamma (Term.lproj s s0)
        (.space (.tprod (.dual s0) s))) from
        ⟨HasType.lproj hsS hs0 hsub⟩)
  have htProjRaw : Nonempty (HasType (∅ : LCtx) Gamma
      (.pinvT
        (Basis.sof (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
        (Basis.sof (Basis.stdSpace s0)) (Term.lembd s))
      (Basis.tof (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))))) := by
    simpa only [Term.lproj, Basis.sof, Basis.sof_stdSpace] using htProjOut
  have hp3raw := C.Term.pinvT_std
    (b₀ := Basis.stdSpace s0)
    (b₁ := .proj s (Basis.stdSpace s0) (Basis.stdSpace s1))
    (Basis.isStd_stdSpace s0)
    (show Basis.isStd (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) from
      ⟨Basis.isStd_stdSpace s0, Basis.isStd_stdSpace s1⟩)
    htProjRaw hprojOutValid htyProjOut hem3
  have hp3 : C.Term (∅ : LCtx) Gamma Psi (Term.lproj s s0)
      (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.pinv em3) (.space (.tprod sv0 svS3)) := by
    simpa only [Term.lproj, Basis.sof, Basis.sof_stdSpace] using hp3raw
  -- Step 2: standardize the domain coordinate while codomain is already std.
  obtain ⟨svS2, em2, hS2, hem2⟩ := checkedEmbed_domside hsOr
    hb0 hstd1 hsof0 (Basis.sof_stdSpace s1)
    hs0 hs1 hwt hsv0 hsv1 hi0 hi1std he2
  have hP2 : Basis.BasisValid Gamma
      (.proj s b0 (Basis.stdSpace s1)) := by
    rcases hsOr with rfl | rfl
    · exact .proj_ker hb0 hstd1 htof0 (Basis.tof_stdSpace s1) ⟨hwt⟩
    · exact .proj_coker hb0 hstd1 htof0 (Basis.tof_stdSpace s1) ⟨hwt⟩
  have hspaceB0 : C.Space Gamma Psi (Basis.sof b0) sv0 := by
    simpa only [hsof0] using hsv0
  have hspaceStd0 : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s0)) sv0 := by
    simpa only [Basis.sof_stdSpace] using hsv0
  have hspaceStd1 : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s1)) sv1 := by
    simpa only [Basis.sof_stdSpace] using hsv1
  have hp3' : C.Term (∅ : LCtx) Gamma Psi
      (Term.lproj s (Basis.sof (Basis.stdSpace s0)))
      (.tprod (.dual (Basis.stdSpace s0))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.pinv em3) (.space (.tprod sv0 svS3)) := by
    simpa only [Basis.sof_stdSpace] using hp3
  have hC2raw := C.Cob.proj_ker_coker hP2 hP3 hsOr hsof0
    (Basis.sof_stdSpace s1) hspaceB0 hspaceStd1 hS2 hS3 hspaceStd0
    hc0 hem2 hp3'
  have hC2 : C.Cob Gamma Psi (.proj s b0 (Basis.stdSpace s1)) _
      (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) := hC2raw

  obtain ⟨svS1, em1, hS1, hem1⟩ := checkedEmbed_domside hsOr
    hb0 hb1 hsof0 hsof1 hs0 hs1 hwt hsv0 hsv1 hi0 hi1 he1
  have hP1 : Basis.BasisValid Gamma (.proj s b0 b1) := by
    rcases hsOr with rfl | rfl
    · exact .proj_ker hb0 hb1 htof0 htof1 ⟨hwt⟩
    · exact .proj_coker hb0 hb1 htof0 htof1 ⟨hwt⟩
  have hC2stdExists : exists env,
      C.Cob Gamma Psi (.proj s b0 (Basis.stdSpace s1)) env
        (Basis.stdSpace s) := by
    exact ⟨_, by simpa only [hstdS] using hC2⟩
  obtain ⟨envP2, hC2std⟩ := hC2stdExists
  obtain ⟨envMix, hMixConv0⟩ := checkedCob_tprod_dual
    hb0 hP2 hsb0 ⟨hsb0, Basis.isSpaceBasis_stdSpace s1⟩
    hsof0 rfl hc0 hC2std
  have hMixConv : C.Cob Gamma Psi
      (.tprod (.dual b0) (.proj s b0 (Basis.stdSpace s1))) envMix
      (Basis.stdSpace (.tprod (.dual s0) s)) := by
    simpa only [Basis.stdSpace] using hMixConv0
  have hMixValid : Basis.BasisValid Gamma
      (.tprod (.dual b0) (.proj s b0 (Basis.stdSpace s1))) :=
    .tprod (.dual hb0 hsb0.tof_eq) hP2 rfl rfl
  have hMixSof : Basis.sof
      (.tprod (.dual b0) (.proj s b0 (Basis.stdSpace s1))) =
      .tprod (.dual s0) s := by simp only [Basis.sof, hsof0]
  have hMixSpace : C.Space Gamma Psi (.tprod (.dual s0) s)
      (.tprod sv0 svS2) :=
    .tprod ⟨.tprod (.dual hs0) hsS⟩ (.dual ⟨.dual hs0⟩ hsv0) hS2
  obtain ⟨pmix, hpmix⟩ := checkedTerm_at_spaceBasis hprogress hP hcov
    ⟨HasType.lproj hsS hs0 hsub⟩ hMixValid
    ⟨hsb0, ⟨hsb0, Basis.isSpaceBasis_stdSpace s1⟩⟩
    hMixSof hMixConv hMixSpace
  have hspaceP1 : C.Space Gamma Psi (Basis.sof (.proj s b0 b1)) svS1 := by
    simpa only [Basis.sof] using hS1
  have hpmix' : C.Term (∅ : LCtx) Gamma Psi
      (Term.lproj s (Basis.sof b0))
      (.tprod (.dual b0) (.proj s b0 (Basis.stdSpace s1)))
      pmix (.space (.tprod sv0 svS2)) := by
    simpa only [hsof0] using hpmix
  have hC1 := C.Cob.proj_ker_coker_cod hP1 hP2 hsOr hsof0 hsof1
    (Basis.sof_stdSpace s1) hspaceB0 hS1 hS2 hem1 hpmix'
  have htrans := C.Cob.trans hP1 hP3 hC1 hC2 hspaceP1
  have htoStdSpace : exists env, C.Cob Gamma Psi (.proj s b0 b1) env
      (Basis.stdSpace (Basis.sof (.proj s b0 b1))) := by
    exact ⟨_, by simpa only [Basis.sof, hstdS] using htrans⟩
  obtain ⟨out, hout⟩ := htoStdSpace
  exact ⟨out, checkedCob_stdTof_of_stdSpace ⟨hsb0, hsb1⟩ hout⟩

/-- Mirror of `checkedCob_proj_dom_arm` for image/coimage, where the
codomain component is the ambient side. -/
theorem checkedCob_proj_cod_arm
    (hprogress : CheckedClosedStdProgress)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 : Basis}
    (hsOr : s = .img s0 s1 e ∨ s = .coimg s0 s1 e)
    (hsS : SValid Gamma s) (hsub : SubType Gamma s s1)
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (_hstored : V2.StoredWF Psi)
    (hb0 : Basis.BasisValid Gamma b0) (hb1 : Basis.BasisValid Gamma b1)
    (hsof0 : Basis.sof b0 = s0) (hsof1 : Basis.sof b1 = s1)
    (hw : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1))))
    (hsb0 : Basis.IsSpaceBasis b0) (hsb1 : Basis.IsSpaceBasis b1)
    (ih0 : exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih1 : exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) :
    exists env, C.Cob Gamma Psi (.proj s b0 b1) env
      (Basis.std (Basis.tof (.proj s b0 b1))) := by
  obtain ⟨hwt⟩ := hw
  have htof0 : Basis.tof b0 = .space s0 :=
    hsb0.tof_eq.trans (congrArg Ty.space hsof0)
  have htof1 : Basis.tof b1 = .space s1 :=
    hsb1.tof_eq.trans (congrArg Ty.space hsof1)
  have hs0 : SValid Gamma s0 := hsof0 ▸ Classical.choice hb0.sof_valid
  have hs1 : SValid Gamma s1 := hsof1 ▸ Classical.choice hb1.sof_valid
  have hstdS : Basis.stdSpace s =
      .proj s (Basis.stdSpace s0) (Basis.stdSpace s1) := by
    rcases hsOr with rfl | rfl <;> rfl
  obtain ⟨sv0, hsv0⟩ := checkedSpace_of_closedStdProgress hprogress hP hcov hs0
  obtain ⟨sv1, hsv1⟩ := checkedSpace_of_closedStdProgress hprogress hP hcov hs1
  obtain ⟨env0, hc00⟩ := ih0
  obtain ⟨env1, hc10⟩ := ih1
  have hc0 : C.Cob Gamma Psi b0 env0 (Basis.stdSpace s0) := by
    have h := checkedCob_stdSpace_of_stdTof hsb0 hc00
    simpa only [hsof0] using h
  have hc1 : C.Cob Gamma Psi b1 env1 (Basis.stdSpace s1) := by
    have h := checkedCob_stdSpace_of_stdTof hsb1 hc10
    simpa only [hsof1] using h
  let refl0 := checkedCob_refl_stdSpace hs0 hsv0
  let refl1 := checkedCob_refl_stdSpace hs1 hsv1
  obtain ⟨vi0, hi0⟩ := checkedInner_at_spaceBasis hprogress hP hcov
    hb0 hsb0 hsof0 hc0 hs0 hsv0
  obtain ⟨vi1, hi1⟩ := checkedInner_at_spaceBasis hprogress hP hcov
    hb1 hsb1 hsof1 hc1 hs1 hsv1
  have hi0std := checked_inner_at hs0 hsv0
  have hi1std := checked_inner_at hs1 hsv1
  have hstd0 : Basis.BasisValid Gamma (Basis.stdSpace s0) :=
    Basis.stdSpace_valid s0 hs0
  have hstd1 : Basis.BasisValid Gamma (Basis.stdSpace s1) :=
    Basis.stdSpace_valid s1 hs1
  obtain ⟨ve1, he1⟩ := checkedMapTerm_at_bases hprogress hP hcov ⟨hwt⟩
    hb0 hb1 hsb0 hsb1 hsof0 hsof1 hc0 hc1 hsv0 hsv1
  obtain ⟨ve2, he2⟩ := checkedMapTerm_at_bases hprogress hP hcov ⟨hwt⟩
    hstd0 hb1 (Basis.isSpaceBasis_stdSpace s0) hsb1
    (Basis.sof_stdSpace s0) hsof1 refl0 hc1 hsv0 hsv1
  obtain ⟨ve3, he3⟩ := checkedMapTerm_at_bases hprogress hP hcov ⟨hwt⟩
    hstd0 hstd1 (Basis.isSpaceBasis_stdSpace s0)
    (Basis.isSpaceBasis_stdSpace s1)
    (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    refl0 refl1 hsv0 hsv1
  -- Step 1: all-standard inclusion and projection.
  obtain ⟨svS3, em3, hS3, hem3⟩ := checkedEmbed_codside hsOr
    hstd0 hstd1 (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    hs0 hs1 hwt hsv0 hsv1 hi0std hi1std he3
  have hP3 : Basis.BasisValid Gamma
      (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) := by
    rcases hsOr with rfl | rfl
    · exact .proj_img hstd0 hstd1 (Basis.tof_stdSpace s0)
        (Basis.tof_stdSpace s1) ⟨hwt⟩
    · exact .proj_coimg hstd0 hstd1 (Basis.tof_stdSpace s0)
        (Basis.tof_stdSpace s1) ⟨hwt⟩
  have hprojOutValid : Basis.BasisValid Gamma
      (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))) :=
    .tprod (.dual hstd1 (Basis.htof_stdSpace s1)) hP3 rfl rfl
  have hsvProjOut : C.Space Gamma Psi (.tprod (.dual s1) s)
      (.tprod sv1 svS3) :=
    .tprod ⟨.tprod (.dual hs1) hsS⟩ (.dual ⟨.dual hs1⟩ hsv1) hS3
  have htyProjOut : C.TyAt Gamma Psi
      (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.space (.tprod sv1 svS3)) :=
    .space rfl hprojOutValid (by
      simpa only [Basis.sof, Basis.sof_stdSpace] using hsvProjOut)
  have htProjOut : Nonempty (HasType (∅ : LCtx) Gamma
      (Term.lproj s s1)
      (Basis.tof (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType (∅ : LCtx) Gamma (Term.lproj s s1)
        (.space (.tprod (.dual s1) s))) from
        ⟨HasType.lproj hsS hs1 hsub⟩)
  have htProjRaw : Nonempty (HasType (∅ : LCtx) Gamma
      (.pinvT
        (Basis.sof (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
        (Basis.sof (Basis.stdSpace s1)) (Term.lembd s))
      (Basis.tof (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1))))) := by
    simpa only [Term.lproj, Basis.sof, Basis.sof_stdSpace] using htProjOut
  have hp3raw := C.Term.pinvT_std
    (b₀ := Basis.stdSpace s1)
    (b₁ := .proj s (Basis.stdSpace s0) (Basis.stdSpace s1))
    (Basis.isStd_stdSpace s1)
    (show Basis.isStd (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) from
      ⟨Basis.isStd_stdSpace s0, Basis.isStd_stdSpace s1⟩)
    htProjRaw hprojOutValid htyProjOut hem3
  have hp3 : C.Term (∅ : LCtx) Gamma Psi (Term.lproj s s1)
      (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.pinv em3) (.space (.tprod sv1 svS3)) := by
    simpa only [Term.lproj, Basis.sof, Basis.sof_stdSpace] using hp3raw
  -- Step 2: standardize the codomain coordinate while domain is already std.
  obtain ⟨svS2, em2, hS2, hem2⟩ := checkedEmbed_codside hsOr
    hstd0 hb1 (Basis.sof_stdSpace s0) hsof1
    hs0 hs1 hwt hsv0 hsv1 hi0std hi1 he2
  have hP2 : Basis.BasisValid Gamma
      (.proj s (Basis.stdSpace s0) b1) := by
    rcases hsOr with rfl | rfl
    · exact .proj_img hstd0 hb1 (Basis.tof_stdSpace s0) htof1 ⟨hwt⟩
    · exact .proj_coimg hstd0 hb1 (Basis.tof_stdSpace s0) htof1 ⟨hwt⟩
  have hspaceB1 : C.Space Gamma Psi (Basis.sof b1) sv1 := by
    simpa only [hsof1] using hsv1
  have hspaceStd0 : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s0)) sv0 := by
    simpa only [Basis.sof_stdSpace] using hsv0
  have hspaceStd1 : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s1)) sv1 := by
    simpa only [Basis.sof_stdSpace] using hsv1
  have hp3' : C.Term (∅ : LCtx) Gamma Psi
      (Term.lproj s (Basis.sof (Basis.stdSpace s1)))
      (.tprod (.dual (Basis.stdSpace s1))
        (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)))
      (.pinv em3) (.space (.tprod sv1 svS3)) := by
    simpa only [Basis.sof_stdSpace] using hp3
  have hC2raw := C.Cob.proj_img_coimg hP2 hP3 hsOr
    (Basis.sof_stdSpace s0) hsof1 hspaceStd0 hspaceB1 hS2 hS3
    hspaceStd1 hc1 hem2 hp3'
  have hC2 : C.Cob Gamma Psi (.proj s (Basis.stdSpace s0) b1) _
      (.proj s (Basis.stdSpace s0) (Basis.stdSpace s1)) := hC2raw
  -- Step 3: standardize the remaining domain coordinate.
  obtain ⟨svS1, em1, hS1, hem1⟩ := checkedEmbed_codside hsOr
    hb0 hb1 hsof0 hsof1 hs0 hs1 hwt hsv0 hsv1 hi0 hi1 he1
  have hP1 : Basis.BasisValid Gamma (.proj s b0 b1) := by
    rcases hsOr with rfl | rfl
    · exact .proj_img hb0 hb1 htof0 htof1 ⟨hwt⟩
    · exact .proj_coimg hb0 hb1 htof0 htof1 ⟨hwt⟩
  have hC2stdExists : exists env,
      C.Cob Gamma Psi (.proj s (Basis.stdSpace s0) b1) env
        (Basis.stdSpace s) := by
    exact ⟨_, by simpa only [hstdS] using hC2⟩
  obtain ⟨envP2, hC2std⟩ := hC2stdExists
  obtain ⟨envMix, hMixConv0⟩ := checkedCob_tprod_dual
    hb1 hP2 hsb1 ⟨Basis.isSpaceBasis_stdSpace s0, hsb1⟩
    hsof1 rfl hc1 hC2std
  have hMixConv : C.Cob Gamma Psi
      (.tprod (.dual b1) (.proj s (Basis.stdSpace s0) b1)) envMix
      (Basis.stdSpace (.tprod (.dual s1) s)) := by
    simpa only [Basis.stdSpace] using hMixConv0
  have hMixValid : Basis.BasisValid Gamma
      (.tprod (.dual b1) (.proj s (Basis.stdSpace s0) b1)) :=
    .tprod (.dual hb1 hsb1.tof_eq) hP2 rfl rfl
  have hMixSof : Basis.sof
      (.tprod (.dual b1) (.proj s (Basis.stdSpace s0) b1)) =
      .tprod (.dual s1) s := by simp only [Basis.sof, hsof1]
  have hMixSpace : C.Space Gamma Psi (.tprod (.dual s1) s)
      (.tprod sv1 svS2) :=
    .tprod ⟨.tprod (.dual hs1) hsS⟩ (.dual ⟨.dual hs1⟩ hsv1) hS2
  obtain ⟨pmix, hpmix⟩ := checkedTerm_at_spaceBasis hprogress hP hcov
    ⟨HasType.lproj hsS hs1 hsub⟩ hMixValid
    ⟨hsb1, ⟨Basis.isSpaceBasis_stdSpace s0, hsb1⟩⟩
    hMixSof hMixConv hMixSpace
  have hspaceP1 : C.Space Gamma Psi (Basis.sof (.proj s b0 b1)) svS1 := by
    simpa only [Basis.sof] using hS1
  have hpmix' : C.Term (∅ : LCtx) Gamma Psi
      (Term.lproj s (Basis.sof b1))
      (.tprod (.dual b1) (.proj s (Basis.stdSpace s0) b1))
      pmix (.space (.tprod sv1 svS2)) := by
    simpa only [hsof1] using hpmix
  have hC1 := C.Cob.proj_img_coimg_dom hP1 hP2 hsOr hsof0 hsof1
    (Basis.sof_stdSpace s0) hspaceB1 hS1 hS2 hem1 hpmix'
  have htrans := C.Cob.trans hP1 hP3 hC1 hC2 hspaceP1
  have htoStdSpace : exists env, C.Cob Gamma Psi (.proj s b0 b1) env
      (Basis.stdSpace (Basis.sof (.proj s b0 b1))) := by
    exact ⟨_, by simpa only [Basis.sof, hstdS] using htrans⟩
  obtain ⟨out, hout⟩ := htoStdSpace
  exact ⟨out, checkedCob_stdTof_of_stdSpace ⟨hsb0, hsb1⟩ hout⟩

structure CheckedCobTermArms : Prop where
  proj_ker :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
      {b0 b1 : Basis},
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.StoredWF Psi ->
      Basis.BasisValid Gamma b0 -> Basis.BasisValid Gamma b1 ->
      Basis.sof b0 = s0 -> Basis.sof b1 = s1 ->
      Nonempty (HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))) ->
      Basis.IsSpaceBasis b0 -> Basis.IsSpaceBasis b1 ->
      (exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0))) ->
      (exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) ->
      exists env, C.Cob Gamma Psi (.proj (.ker s0 s1 e) b0 b1) env
        (Basis.std (Basis.tof (.proj (.ker s0 s1 e) b0 b1)))
  proj_coker :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
      {b0 b1 : Basis},
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.StoredWF Psi ->
      Basis.BasisValid Gamma b0 -> Basis.BasisValid Gamma b1 ->
      Basis.sof b0 = s0 -> Basis.sof b1 = s1 ->
      Nonempty (HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))) ->
      Basis.IsSpaceBasis b0 -> Basis.IsSpaceBasis b1 ->
      (exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0))) ->
      (exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) ->
      exists env, C.Cob Gamma Psi (.proj (.coker s0 s1 e) b0 b1) env
        (Basis.std (Basis.tof (.proj (.coker s0 s1 e) b0 b1)))
  proj_img :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
      {b0 b1 : Basis},
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.StoredWF Psi ->
      Basis.BasisValid Gamma b0 -> Basis.BasisValid Gamma b1 ->
      Basis.sof b0 = s0 -> Basis.sof b1 = s1 ->
      Nonempty (HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))) ->
      Basis.IsSpaceBasis b0 -> Basis.IsSpaceBasis b1 ->
      (exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0))) ->
      (exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) ->
      exists env, C.Cob Gamma Psi (.proj (.img s0 s1 e) b0 b1) env
        (Basis.std (Basis.tof (.proj (.img s0 s1 e) b0 b1)))
  proj_coimg :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : Space} {e : Term}
      {b0 b1 : Basis},
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.StoredWF Psi ->
      Basis.BasisValid Gamma b0 -> Basis.BasisValid Gamma b1 ->
      Basis.sof b0 = s0 -> Basis.sof b1 = s1 ->
      Nonempty (HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))) ->
      Basis.IsSpaceBasis b0 -> Basis.IsSpaceBasis b1 ->
      (exists env, C.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0))) ->
      (exists env, C.Cob Gamma Psi b1 env (Basis.std (Basis.tof b1))) ->
      exists env, C.Cob Gamma Psi (.proj (.coimg s0 s1 e) b0 b1) env
        (Basis.std (Basis.tof (.proj (.coimg s0 s1 e) b0 b1)))
  image :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
      {s0 s1 : Space} {e : Term},
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.StoredWF Psi ->
      Basis.BasisValid Gamma b -> Basis.sof b = .coker s0 s1 e ->
      Nonempty (HasType (∅ : LCtx) Gamma e (.space (.tprod (.dual s0) s1))) ->
      Basis.IsSpaceBasis b ->
      (exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) ->
      exists env, C.Cob Gamma Psi (.image b) env
        (Basis.std (Basis.tof (.image b)))
  terms :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s : Space}
      {es : List Term} {b : Basis},
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi -> V2.StoredWF Psi ->
      Basis.BasisValid Gamma b -> Basis.sof b = s -> Nonempty (SValid Gamma s) ->
      (forall e, e ∈ es -> Nonempty (HasType (∅ : LCtx) Gamma e (.space s))) ->
      es ≠ [] -> Basis.IsSpaceBasis b ->
      (exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))) ->
      exists env, C.Cob Gamma Psi (.terms s es b) env
        (Basis.std (Basis.tof (.terms s es b)))

/-- Direct checked induction on `BasisValid`; only the six source-term arms
are delegated to the precisely shaped record above. -/
theorem checkedCobToStd_of_termArms
    (arms : CheckedCobTermArms) : CheckedCobToStd := by
  intro Gamma Psi b hP hcov hstored hb
  revert hcov hstored
  induction hb with
  | empty =>
      intro _ _ _
      exact ⟨_, .refl .empty rfl .empty⟩
  | one =>
      intro _ _ _
      exact ⟨_, .refl .one rfl .real⟩
  | @dual Gamma b hb htof ih =>
      intro hcov hstored hsb
      obtain ⟨env, henv⟩ := ih hcov hstored hsb
      exact ⟨_, by
        simpa only [Basis.std, Basis.tof, Basis.sof] using
          checkedCob_dual_toStdSpace hb hsb henv⟩
  | @dsum Gamma b0 b1 hb0 hb1 htof0 htof1 ih0 ih1 =>
      intro hcov hstored hsb
      obtain ⟨hs0, hs1⟩ := hsb
      obtain ⟨env0, h0⟩ := ih0 hcov hstored hs0
      obtain ⟨env1, h1⟩ := ih1 hcov hstored hs1
      have h0' := checkedCob_stdSpace_of_stdTof hs0 h0
      have h1' := checkedCob_stdSpace_of_stdTof hs1 h1
      exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hs0, hs1⟩
        (checkedCob_dsum_toStdSpace hb0 hb1 hs0 hs1 h0' h1')⟩
  | @tprod Gamma b0 b1 hb0 hb1 htof0 htof1 ih0 ih1 =>
      intro hcov hstored hsb
      obtain ⟨hs0, hs1⟩ := hsb
      obtain ⟨env0, h0⟩ := ih0 hcov hstored hs0
      obtain ⟨env1, h1⟩ := ih1 hcov hstored hs1
      have h0' := checkedCob_stdSpace_of_stdTof hs0 h0
      have h1' := checkedCob_stdSpace_of_stdTof hs1 h1
      exact ⟨_, checkedCob_stdTof_of_stdSpace ⟨hs0, hs1⟩
        (checkedCob_tprod_toStdSpace hb0 hb1 hs0 hs1 h0' h1')⟩
  | @proj_ker Gamma s0 s1 e b0 b1 hb0 hb1 hsof0 hsof1 hw ih0 ih1 =>
      intro hcov hstored hsb
      have hs0 := Basis.sof_eq_of_tof_eq_space hsof0
      have hs1 := Basis.sof_eq_of_tof_eq_space hsof1
      exact arms.proj_ker hP hcov hstored hb0 hb1 hs0 hs1 hw hsb.1 hsb.2
        (ih0 hcov hstored hsb.1) (ih1 hcov hstored hsb.2)
  | @proj_coker Gamma s0 s1 e b0 b1 hb0 hb1 hsof0 hsof1 hw ih0 ih1 =>
      intro hcov hstored hsb
      have hs0 := Basis.sof_eq_of_tof_eq_space hsof0
      have hs1 := Basis.sof_eq_of_tof_eq_space hsof1
      exact arms.proj_coker hP hcov hstored hb0 hb1 hs0 hs1 hw hsb.1 hsb.2
        (ih0 hcov hstored hsb.1) (ih1 hcov hstored hsb.2)
  | @proj_img Gamma s0 s1 e b0 b1 hb0 hb1 hsof0 hsof1 hw ih0 ih1 =>
      intro hcov hstored hsb
      have hs0 := Basis.sof_eq_of_tof_eq_space hsof0
      have hs1 := Basis.sof_eq_of_tof_eq_space hsof1
      exact arms.proj_img hP hcov hstored hb0 hb1 hs0 hs1 hw hsb.1 hsb.2
        (ih0 hcov hstored hsb.1) (ih1 hcov hstored hsb.2)
  | @proj_coimg Gamma s0 s1 e b0 b1 hb0 hb1 hsof0 hsof1 hw ih0 ih1 =>
      intro hcov hstored hsb
      have hs0 := Basis.sof_eq_of_tof_eq_space hsof0
      have hs1 := Basis.sof_eq_of_tof_eq_space hsof1
      exact arms.proj_coimg hP hcov hstored hb0 hb1 hs0 hs1 hw hsb.1 hsb.2
        (ih0 hcov hstored hsb.1) (ih1 hcov hstored hsb.2)
  | @image Gamma b s0 s1 e hb hsof hw ih =>
      intro hcov hstored hsb
      exact arms.image hP hcov hstored hb hsof hw hsb
        (ih hcov hstored hsb)
  | @terms Gamma s es b hb htof hsv hall hne ih =>
      intro hcov hstored hsb
      have hsof := Basis.sof_eq_of_tof_eq_space htof
      exact arms.terms hP hcov hstored hb hsof hsv hall hne hsb.2
        (ih hcov hstored hsb.2)
  | frame L hb0 hbody ih0 ihbody =>
      intro _ _ hsb
      exact False.elim hsb

/-- All six source-term arms are consequences of the single closed checked
standard-progress re-entry. -/
theorem checkedCobTermArms_of_closedStdProgress
    (hprogress : CheckedClosedStdProgress) : CheckedCobTermArms := by
  constructor
  · intro Gamma Psi s0 s1 e b0 b1 hP hcov hstored hb0 hb1
      hsof0 hsof1 hw hsb0 hsb1 ih0 ih1
    obtain ⟨hwt⟩ := hw
    have hs0 : SValid Gamma s0 := hsof0 ▸ Classical.choice hb0.sof_valid
    have hs1 : SValid Gamma s1 := hsof1 ▸ Classical.choice hb1.sof_valid
    exact checkedCob_proj_dom_arm hprogress (Or.inl rfl)
      (.ker hs0 hs1 hwt) (.sub_ker hs0 hs1 hwt)
      hP hcov hstored hb0 hb1 hsof0 hsof1 ⟨hwt⟩ hsb0 hsb1 ih0 ih1
  · intro Gamma Psi s0 s1 e b0 b1 hP hcov hstored hb0 hb1
      hsof0 hsof1 hw hsb0 hsb1 ih0 ih1
    obtain ⟨hwt⟩ := hw
    have hs0 : SValid Gamma s0 := hsof0 ▸ Classical.choice hb0.sof_valid
    have hs1 : SValid Gamma s1 := hsof1 ▸ Classical.choice hb1.sof_valid
    exact checkedCob_proj_dom_arm hprogress (Or.inr rfl)
      (.coker hs0 hs1 hwt) (.sub_coker hs0 hs1 hwt)
      hP hcov hstored hb0 hb1 hsof0 hsof1 ⟨hwt⟩ hsb0 hsb1 ih0 ih1
  · intro Gamma Psi s0 s1 e b0 b1 hP hcov hstored hb0 hb1
      hsof0 hsof1 hw hsb0 hsb1 ih0 ih1
    obtain ⟨hwt⟩ := hw
    have hs0 : SValid Gamma s0 := hsof0 ▸ Classical.choice hb0.sof_valid
    have hs1 : SValid Gamma s1 := hsof1 ▸ Classical.choice hb1.sof_valid
    exact checkedCob_proj_cod_arm hprogress (Or.inl rfl)
      (.img hs0 hs1 hwt) (.sub_img hs0 hs1 hwt)
      hP hcov hstored hb0 hb1 hsof0 hsof1 ⟨hwt⟩ hsb0 hsb1 ih0 ih1
  · intro Gamma Psi s0 s1 e b0 b1 hP hcov hstored hb0 hb1
      hsof0 hsof1 hw hsb0 hsb1 ih0 ih1
    obtain ⟨hwt⟩ := hw
    have hs0 : SValid Gamma s0 := hsof0 ▸ Classical.choice hb0.sof_valid
    have hs1 : SValid Gamma s1 := hsof1 ▸ Classical.choice hb1.sof_valid
    exact checkedCob_proj_cod_arm hprogress (Or.inr rfl)
      (.coimg hs0 hs1 hwt) (.sub_coimg hs0 hs1 hwt)
      hP hcov hstored hb0 hb1 hsof0 hsof1 ⟨hwt⟩ hsb0 hsb1 ih0 ih1
  · intro Gamma Psi b s0 s1 e hP hcov hstored hb hsof hw hsb ih
    exact checkedCob_image_arm hprogress hP hcov hstored hb hsof hw hsb ih
  · intro Gamma Psi s es b hP hcov hstored hb hsof hsv hall hne hsb ih
    exact checkedCob_terms_arm hprogress hP hcov hstored hb hsof hsv hall hne hsb ih

/-- Checked change-of-basis progress by mutual induction. -/
theorem checkedCobToStd_of_closedStdProgress
    (hprogress : CheckedClosedStdProgress) : CheckedCobToStd :=
  checkedCobToStd_of_termArms
    (checkedCobTermArms_of_closedStdProgress hprogress)

/-- Consequently, supplying the existing eight explicit checked-progress
arms closes checked COB progress with no additional COB-specific axiom. -/
theorem checkedCobToStd_of_openArms
    (gaps : CheckedProgressOpenArms) : CheckedCobToStd :=
  checkedCobToStd_of_closedStdProgress
    (checkedClosedStdProgress_of_openArms gaps)

end RawCertifiedProgressScratch
end GLang
