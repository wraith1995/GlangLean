import GLang.Proofs.Adequacy.Partial.Source.PartialSourceWorld
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceBridge
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceValueBridge
import GLang.Proofs.Adequacy.Foundations.Foundations
import GLang.Proofs.Adequacy.Foundations.Erasure

/-! Exact-basis type adequacy for the actual partial evaluator. -/
namespace GLang.PartialAdequacy

open Basis (BasisValid)

/-- Space leaf of exact-basis type adequacy. -/
theorem mTyAt_space
    {orc : PartialFFSOracleSem} {C : WorldPred}
    (hspace : SpaceClaim orc C)
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {sv : ValSpace}
    (htof : Basis.tof b = .space (Basis.sof b))
    (_hbv : BasisValid Gamma b)
    (hs : S.Space Gamma Psi (Basis.sof b) sv) :
    MTyAt orc C Gamma Psi b (.space sv) := by
  intro rho Delta' Gamma' sigma GammaV hle hc
  rw [htof]
  simpa only [DimsAt] using
    hspace hs rho Delta' Gamma' sigma GammaV hle hc

/-- Dependent-frame leaf.  The callback argument is already represented in
the domain basis carried by this same frame. -/
theorem mTyAt_frame
    {orc : PartialFFSOracleSem} {C : WorldPred}
    (hext : WorldExtendNLAt orc C)
    (hworldLc : WorldLc C)
    (hpush : PartialDirectOpenPush.OracleOpenPush orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {tauv0 tauv1 : ValTy}
    (hbv : BasisValid Gamma (.frame b0 b1))
    (hdom : S.TyAt Gamma Psi b0 tauv0)
    (L : Finset Name)
    (hcod : forall y, y ∉ L ->
      S.TyAt
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1)
        (ValTy.openVar y tauv0 tauv1))
    (hisTy : Basis.IsTyBasis (.frame b0 b1))
    (ihdom : MTyAt orc C Gamma Psi b0 tauv0)
    (ihcod : forall y, y ∉ L ->
      MTyAt orc C
        (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauv0))
        (Basis.openVar y b1)
        (ValTy.openVar y tauv0 tauv1)) :
    MTyAt orc C Gamma Psi (.frame b0 b1)
      (.piTy tauv0 tauv1) := by
  intro rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨hbv0, ⟨Lb, _hbv1⟩, _k0, _k1, _ht⟩ := hbv.frame_inv
  have hd0 : DimsAt orc sigma rho [] [] []
      (Basis.tof b0) tauv0 (denotBasis sigma b0) :=
    ihdom rho Delta' Gamma' sigma GammaV hle hc
  simp only [Basis.tof, DimsAt]
  refine ⟨by simpa only [denotBasis_frame_domainBasis] using hd0, ?_⟩
  intro x' argVal arg _hto harg
  let d := (denotTy sigma (Basis.tof b0)).embed x'
  have harg0 : Agree orc sigma rho [] [] []
      (Basis.tof b0) tauv0 (denotBasis sigma b0) d argVal := by
    simpa only [denotBasis_frame_domainBasis, d] using harg
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    (L ∪ Lb ∪ Delta'.keys ∪ Gamma'.keys ∪ Psi.keyNames ∪
      Ty.fv (Basis.tof b1) ∪ ValTy.fv tauv0 ∪ ValTy.fv tauv1 ∪
      Basis.fv b1)
  simp only [Finset.mem_union, not_or] at hy
  rcases hy with
    ⟨⟨⟨⟨⟨⟨⟨⟨hyL, _hyLb⟩, hyDeltaKeys⟩, hyGammaKeys⟩,
      hyPsiNames⟩, hyTau1⟩, hyTauv0⟩, hyTauv1⟩, hyb1⟩
  have hyDelta : y ∉ Delta' :=
    fun hym => hyDeltaKeys (Finmap.mem_keys.mpr hym)
  have hyGamma : y ∉ Gamma' :=
    fun hym => hyGammaKeys (Finmap.mem_keys.mpr hym)
  have hyPsi : forall b, (y, b) ∉ Psi := by
    intro b hym
    apply hyPsiNames
    rw [EvalCtx.keyNames]
    exact Finset.mem_image.mpr
      ⟨(y, b), Finmap.mem_keys.mpr hym, rfl⟩
  have hle' : NLCtxIncl
      (Finmap.insert y (Basis.tof b0) Gamma)
      (Finmap.insert y (Basis.tof b0) Gamma') := by
    intro z tau hz
    by_cases hzy : z = y
    · subst z
      rw [Finmap.lookup_insert] at hz ⊢
      exact hz
    · rw [Finmap.lookup_insert_of_ne _ hzy] at hz ⊢
      exact hle z tau hz
  have hc' : C Delta' (Finmap.insert y (Basis.tof b0) Gamma')
      (Psi.extend y b0 (.var y tauv0)) (Finmap.insert y tauv0 GammaV)
      (sigma.bind y d) (rho.update y argVal) := by
    exact hext hc hle ⟨hyDelta, hyGamma, hyPsi⟩ hbv0 hisTy.1 hdom
      x' argVal harg0 hd0
  have hopenBasis := ihcod y hyL (rho.update y argVal) Delta'
    (Finmap.insert y (Basis.tof b0) Gamma') (sigma.bind y d)
    (Finmap.insert y tauv0 GammaV) hle' hc'
  have hopen : DimsAt orc (sigma.bind y d)
      (rho.update y argVal) [] [] []
      (Ty.openVar y (Basis.tof b1)) (ValTy.openVar y tauv0 tauv1)
      (denotBasis (sigma.bind y d) (Basis.openVar y b1)) := by
    simpa only [Basis.openVar, Basis.tof_openRec] using hopenBasis
  obtain ⟨_k, htOpen⟩ := (hcod y hyL).toTy.tvalid
  have hlcOpen : Ty.lc (Ty.openVar y (Basis.tof b1)) := by
    simpa only [Basis.openVar, Basis.tof_openRec] using TValid.lc htOpen.some
  let Bopen := denotBasis (sigma.bind y d) (Basis.openVar y b1)
  have hopenStack : DimsAt orc (sigma.bind y d)
      (rho.update y argVal) [d] [] []
      (Ty.openVar y (Basis.tof b1))
      (ValTy.openVar y tauv0 tauv1) Bopen :=
    (DimsAt.lc_irrel_src orc hlcOpen
      (ValTy.openVar y tauv0 tauv1) (sigma.bind y d)
      (rho.update y argVal) [] [d] [] [] Bopen).mp
      (by simpa only [Bopen] using hopen)
  have hsourceBridge := DimsAt.openRec_bind_src orc (z := y)
    sigma (rho.update y argVal) (Basis.tof b1)
    (ValTy.openVar y tauv0 tauv1) [d] [] [] 0 Bopen hyTau1
  simp only [List.getD_cons_zero] at hsourceBridge
  have hsource : DimsAt orc sigma (rho.update y argVal)
      [d] [] [] (Basis.tof b1) (ValTy.openVar y tauv0 tauv1) Bopen :=
    hsourceBridge.mp hopenStack
  have hpushed : DimsAt orc sigma rho [d] [tauv0] [argVal]
      (Basis.tof b1) tauv1 Bopen :=
    DimsAt.valueOpenPush (G := []) (D := []) hpush (evalT_lc hdom.toEvalT (hworldLc hc))
      hyTauv0 (by intro t ht; cases ht) rfl hyTauv1 hsource
  have hbasis :
      (denotBasis sigma (.frame b0 b1)).applyEl x' = Bopen := by
    simpa only [d, Bopen] using
      denotBasis_frame_applyEl_openVar y hyb1 x'
  simpa only [hbasis] using hpushed

/-- Complete exact-basis type induction. -/
theorem mTyAt_holds
    {orc : PartialFFSOracleSem} {C : WorldPred}
    (hext : WorldExtendNLAt orc C)
    (hworldLc : WorldLc C)
    (hpush : PartialDirectOpenPush.OracleOpenPush orc)
    (hspace : SpaceClaim orc C) :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {tauv : ValTy},
      S.TyAt Gamma Psi b tauv -> MTyAt orc C Gamma Psi b tauv := by
  intro Gamma Psi b tauv h
  apply h.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun Gamma Psi b tauv _ =>
      MTyAt orc C Gamma Psi b tauv)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
  all_goals try (intros; trivial)
  · intro Gamma Psi b sv htof hbv hs _ihSpace
    exact mTyAt_space hspace htof hbv hs
  · intro Gamma Psi b0 b1 tauv0 tauv1 hbv hdom L hcod ihdom ihcod
    exact mTyAt_frame hext hworldLc hpush
      hbv hdom L hcod hbv.isTyBasis ihdom ihcod

end GLang.PartialAdequacy
