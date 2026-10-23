import GLang.Proofs.Progress.Certificates.RawCertifiedProgressArms
import GLang.Graded.SourceSubst

namespace GLang
namespace RawCertifiedProgressScratch

open RawCertifiedOperational

/-- The checked dependent cut needed by nonlinear application.

The `ESubst` premise identifies the fresh placeholder with the evaluated
argument.  The result basis is exact, while its checked runtime annotation is
existential.  The freshness premise is exactly the one used by
`appN_realize_core` to align named substitution with locally-nameless
instantiation. -/
def CheckedTyAtAppCut : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {y : VName}
    {b0 b1 : Basis} {tauv0 tauv1 : ValTy}
    {n1 : Term} {arg : ValExpr},
    V2.CtxWF' ∅ Gamma ->
    EvalCtxLc Psi ->
    y ∉ Gamma ->
    y ∉ Basis.fv b0 ->
    ESubst y b0 tauv0 n1 arg
      (Psi.extend y b0 (.var y tauv0)) Psi ->
    C.Term ∅ Gamma Psi n1 (Basis.subst y n1 b0) arg
      (ValTy.subst y arg tauv0) ->
    y ∉ Basis.fv b1 ->
    C.TyAt (Finmap.insert y (Basis.tof b0) Gamma)
      (Psi.extend y b0 (.var y tauv0))
      (Basis.openVar y b1) (ValTy.openVar y tauv0 tauv1) ->
    exists tauOut,
      C.TyAt Gamma Psi (Basis.instantiate n1 b1) tauOut

/-- Exact inversion of a standard-frame certificate.  In particular, the
domain and opened codomain remain anchored at the literal component bases
of `Basis.std`. -/
theorem checkedTyAt_std_pi_inv
    (h : C.TyAt Gamma Psi (Basis.std (.piTy tau0 tau1)) tauv) :
    exists tauv0 tauv1,
      tauv = .piTy tauv0 tauv1 /\
      C.TyAt Gamma Psi (Basis.std tau0) tauv0 /\
      exists L : Finset VName, forall y, y ∉ L ->
        C.TyAt (Finmap.insert y (Basis.tof (Basis.std tau0)) Gamma)
          (Psi.extend y (Basis.std tau0) (.var y tauv0))
          (Basis.openVar y (Basis.std tau1))
          (ValTy.openVar y tauv0 tauv1) := by
  simpa only [Basis.std] using
    (checkedTyAt_frame_inv_full
      (b0 := Basis.std tau0) (b1 := Basis.std tau1) h)

/-- The application result's standard basis is source-valid independently
of the checked dependent cut.  The function certificate supplies validity
of the Pi type; the already-proved graded source substitution theorem
instantiates its codomain with the typed argument. -/
noncomputable def checked_app_result_basisValid
    (ht1 : HasType ∅ Gamma e1 tau0)
    (hfun : C.Term ∅ Gamma Psi e0 (Basis.std (.piTy tau0 tau1)) env0 tauvFun) :
    Basis.BasisValid Gamma (Basis.std (Ty.instantiate e1 tau1)) := by
  obtain ⟨k, ⟨hvalid⟩⟩ := hfun.basisValid.tof_tvalid
  have hpi : TValid Gamma (.piTy tau0 tau1) k := by
    simpa only [Basis.tof_std] using hvalid
  cases hpi with
  | piTy L h0 h1 =>
      exact Basis.std_valid _
        (Graded.tvalid_instantiate (.piTy L h0 h1) ht1)

theorem checked_arm_app_nonlinear_of_tyAt_appCut
    (happCut : CheckedTyAtAppCut) :
    forall {Gamma : NLCtx} {e0 e1 : Term} {tau0 tau1 : Ty}
      (ht0 : HasType ∅ Gamma e0 (.piTy tau0 tau1))
      (ht1 : HasType ∅ Gamma e1 tau0),
      V2.CtxWF' ∅ Gamma ->
      cMotiveH ∅ Gamma e0 (.piTy tau0 tau1) ->
      cMotiveH ∅ Gamma e1 tau0 ->
      cMotiveH ∅ Gamma (.appN e0 e1) (Ty.instantiate e1 tau1) := by
  intro Gamma e0 e1 tau0 tau1 ht0 ht1 hwf ih0 ih1 Psi hP hcov
  obtain ⟨env0, tauvFun, hfun⟩ := ih0 Psi hP hcov
  obtain ⟨env1, tauvArg, harg⟩ := ih1 Psi hP hcov
  obtain ⟨tauv0, tauv1, rfl, hdom, L, hcod⟩ :=
    checkedTyAt_std_pi_inv hfun.tyAt

  have heval0 : ValTy.EvalT Psi tau0 tauv0 := by
    simpa only [Basis.tof_std] using hdom.erase
  have hlcn1 : Term.lc e1 := ht1.lc
  have hlcenv1 : ValExpr.lc env1 := opStep_lc harg.erase hP.1.toEvalCtxLc
  have hlctauv0 : ValTy.lc tauv0 := evalT_lc heval0 hP.1.toEvalCtxLc
  have hlctauvArg : ValTy.lc tauvArg :=
    evalT_lc harg.tyAt.erase hP.1.toEvalCtxLc

  have hargCut : C.Term ∅ Gamma Psi e1 (Basis.std tau0)
      (.reshap env1 tauv0 tauvArg) tauv0 :=
    retag harg hdom

  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Psi ∪ L ∪ Basis.fv (Basis.std tau0) ∪
      Basis.fv (Basis.std tau1) ∪ ValTy.fv tauv1)
  simp only [Finset.mem_union, not_or] at hy
  obtain ⟨⟨⟨⟨hyPsi, hyL⟩, hyb0⟩, hyb1⟩, _hytauv1⟩ := hy
  obtain ⟨hyfresh, hyvals, hybases⟩ := EvalCtx.avoidB_spec hyPsi
  have hytauv0 : y ∉ ValTy.fv tauv0 := by
    intro hm
    have hkn : y ∈ Psi.keyNames := V2.evalT_fv heval0 hP.1 hm
    have : y ∈ EvalCtx.avoidB Psi := by
      rw [EvalCtx.avoidB, EvalCtx.avoid]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hkn)
    exact hyPsi this

  have hes := V2.appN_esubst
    (Ψ₀ := Psi) (y := y) (b₀ := Basis.std tau0) (τv₀ := tauv0)
    (n₁ := e1) (env₁ := .reshap env1 tauv0 tauvArg)
    hyfresh hyb0
    (fun z b v hl => hyvals (z, b) v hl)
    (fun z b v hl => hybases z b (Finmap.mem_of_lookup_eq_some hl))
    hlcn1 (.reshap hlcenv1 hlctauv0 hlctauvArg)
    (by
      simp only [ValExpr.inferSpace]
      exact (ValSpace.subst_fresh y _ _
        (fun hm => hytauv0 (ValSpace.fv_spaceOf_subset tauv0 hm))).symm)
    (by simpa only [ValExpr.inferType] using (ValTy.subst_fresh y _ tauv0 hytauv0).symm)
    hargCut.erase
  have hyGamma : y ∉ Gamma := by
    intro hm
    obtain ⟨tau, hlookup⟩ := Finmap.mem_iff.mp hm
    obtain ⟨b, hmem, _htof⟩ := hcov.2 y tau hlookup
    have hkey : y ∈ Psi.keyNames := by
      exact Finset.mem_image.mpr
        ⟨(y, b), Finmap.mem_keys.mpr hmem, rfl⟩
    exact hyPsi (V2.keyNames_subset_avoidB Psi hkey)
  have hargCut' : C.Term ∅ Gamma Psi e1
      (Basis.subst y e1 (Basis.std tau0))
      (.reshap env1 tauv0 tauvArg)
      (ValTy.subst y (.reshap env1 tauv0 tauvArg) tauv0) := by
    simpa only [Basis.subst_fresh y e1 (Basis.std tau0) hyb0,
      ValTy.subst_fresh y (.reshap env1 tauv0 tauvArg) tauv0 hytauv0]
      using hargCut
  obtain ⟨tauOut, hout⟩ := happCut hwf hP.1.toEvalCtxLc hyGamma hyb0
    hes hargCut' hyb1 (hcod y hyL)

  have htyped : Nonempty (HasType ∅ Gamma (.appN e0 e1)
      (Basis.tof (Basis.instantiate e1 (Basis.std tau1)))) := by
    refine ⟨?_⟩
    simpa only [Basis.instantiate, Basis.tof_openRec, Basis.tof_std,
      Ty.instantiate] using HasType.app_nonlinear ht0 ht1
  have hbout : Basis.BasisValid Gamma
      (Basis.instantiate e1 (Basis.std tau1)) := by
    change Basis.BasisValid Gamma (Basis.openRec 0 e1 (Basis.std tau1))
    rw [← Basis.std_openRec e1 tau1 0]
    exact checked_app_result_basisValid ht1 hfun
  have hstep := C.Term.appN_val htyped hbout hout hfun harg
  rw [show Basis.std (Ty.instantiate e1 tau1) =
      Basis.instantiate e1 (Basis.std tau1) from
    Basis.std_openRec e1 tau1 0]
  exact ⟨_, _, hstep⟩

end RawCertifiedProgressScratch
end GLang
