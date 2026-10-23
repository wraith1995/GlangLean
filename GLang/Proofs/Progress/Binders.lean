import GLang.Proofs.Progress.Certificates.RawCertifiedProgressArms
import GLang.Proofs.Progress.Certificates.RawCertifiedRename
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLift
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLower
import GLang.Proofs.Progress.ContextExtension
import GLang.Proofs.Adequacy.Foundations.StrengthenedMono

namespace GLang
namespace RawCertifiedBinderProgressSpike

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch

/-! ## Minimally WF-indexed motives -/

def cMotiveSWF (Gamma : NLCtx) (s : Space) : Prop :=
  forall Psi : EvalCtx, V2.PCarrier Psi -> V2.VarsCovered ∅ Gamma Psi ->
    V2.CtxWF' ∅ Gamma ->
    exists sv, C.Space Gamma Psi s sv

def cMotiveTWF (Gamma : NLCtx) (tau : Ty) : Prop :=
  forall Psi : EvalCtx, V2.PCarrier Psi -> V2.VarsCovered ∅ Gamma Psi ->
    V2.CtxWF' ∅ Gamma ->
    exists tauv, C.Ty Gamma Psi tau tauv /\
      C.TyAt Gamma Psi (Basis.std tau) tauv

def cMotiveSubWF (Gamma : NLCtx) (s0 s1 : Space) : Prop :=
  forall Psi : EvalCtx, V2.PCarrier Psi -> V2.VarsCovered ∅ Gamma Psi ->
    V2.CtxWF' ∅ Gamma ->
    exists v tauv, C.Term ∅ Gamma Psi (.embed s0)
      (Basis.std (.space (.tprod (.dual s0) s1))) v tauv

def cMotiveHWF (Delta : LCtx) (Gamma : NLCtx) (e : Term) (tau : Ty) : Prop :=
  forall Psi : EvalCtx, V2.PCarrier Psi -> V2.VarsCovered Delta Gamma Psi ->
    V2.CtxWF' Delta Gamma ->
    exists v tauv, C.Term Delta Gamma Psi e (Basis.std tau) v tauv

/-- Space/type subderivations forget the linear half of a well-formed
context. -/
theorem ctxWF_dropLin (h : V2.CtxWF' Delta Gamma) : V2.CtxWF' ∅ Gamma where
  disjoint := fun _ hm => absurd hm Finmap.notMem_empty
  lin_fv := fun _ _ hm => absurd (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
  nl_fv := h.nl_fv
  lin_valid := fun _ _ hm => absurd (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
  nl_valid := h.nl_valid

/-! ## Exact-standard `TyAt` already contains an unindexed checked `Ty`

This structural conversion is why `CheckedRenameLaws` does not need a
separate `C.Ty` field.  At a Pi type, the exact standard frame contains the
same checked domain and cofinite checked codomain needed by `C.Ty.piTy`.
-/

theorem checkedTy_of_tyAtStd
    (h : C.TyAt Gamma Psi (Basis.std tau) tauv) :
    C.Ty Gamma Psi tau tauv := by
  have hs := h.toS.toTy
  rw [Basis.tof_std] at hs
  exact RawCertifiedOperational.S.Ty.toC hs

/-- A checked space realization can be reused under a genuinely fresh
evaluator extension.  We route through the already-proved exact namespace
isomorphism and strengthened monotonicity. -/
theorem checkedSpace_extend
    (h : C.Space Gamma Psi s sv) (hx : x ∉ EvalCtx.avoidB Psi) :
    C.Space Gamma (Psi.extend x b v) s sv := by
  have hxnames : x ∉ Psi.names := by
    intro hm
    obtain ⟨⟨z, b'⟩, hkey, hz⟩ := Finset.mem_image.mp hm
    simp only at hz
    subst z
    exact (EvalCtx.avoidB_spec hx).1 b'
      (Finmap.mem_keys.mp hkey)
  have hsub : Psi.Subctx (Psi.extend x b v) :=
    EvalCtx.Subctx.extend_right_of_name_fresh hxnames b v
  exact RawCertifiedOperational.S.Space.toC (h.toS.mono hsub)

/-- Invert an exact certificate at the standard basis of a Pi type while
normalizing both standard-basis equations in the cofinite codomain. -/
theorem tyAtStdPi_inv
    (h : C.TyAt Gamma Psi (Basis.std (.piTy tau0 tau1)) tauv) :
    exists tauv0 tauv1,
      tauv = .piTy tauv0 tauv1 /\
      Basis.BasisValid Gamma (.frame (Basis.std tau0) (Basis.std tau1)) /\
      C.TyAt Gamma Psi (Basis.std tau0) tauv0 /\
      exists L : Finset Name, forall y, y ∉ L ->
        C.TyAt (Finmap.insert y tau0 Gamma)
          (Psi.extend y (Basis.std tau0) (.var y tauv0))
          (Basis.std (Ty.openVar y tau1))
          (ValTy.openVar y tauv0 tauv1) := by
  change C.TyAt Gamma Psi
    (.frame (Basis.std tau0) (Basis.std tau1)) tauv at h
  obtain ⟨tauv0, tauv1, rfl, hdom, L, hcod⟩ :=
    checkedTyAt_frame_inv_full h
  have hbv : Basis.BasisValid Gamma
      (.frame (Basis.std tau0) (Basis.std tau1)) := h.toS.basisValid
  refine ⟨tauv0, tauv1, rfl, hbv, hdom, L, ?_⟩
  intro y hy
  have hc := hcod y hy
  rw [← Basis.std_openVar] at hc
  simpa only [Basis.tof_std] using hc

/-! ## Pi-type formation -/

theorem checked_arm_ty_pi_wf
    (laws : CheckedRenameLaws) :
    forall {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind}
      (L : Finset Name)
      (ht0 : TValid Gamma tau0 k0)
      (ht1 : forall y, y ∉ L ->
        TValid (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1) k1),
      cMotiveTWF Gamma tau0 ->
      (forall y, y ∉ L ->
        cMotiveTWF (Finmap.insert y tau0 Gamma) (Ty.openVar y tau1)) ->
      cMotiveTWF Gamma (.piTy tau0 tau1) := by
  intro Gamma tau0 tau1 k0 k1 L ht0 ht1 ih0 ih1 Psi hP hcov hwf
  obtain ⟨tauv0, _hTy0, hAt0⟩ := ih0 Psi hP hcov hwf
  have h0eval : ValTy.EvalT Psi tau0 tauv0 := by
    simpa only [Basis.tof_std] using hAt0.erase
  have hanc0 : V2.StdAnchored Psi tau0 tauv0 := tyAt_stdAnchored hAt0
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Psi ∪ L ∪ Gamma.keys ∪ Ty.fv tau1 ∪
      Basis.fv (Basis.std tau0) ∪ ValTy.fv tauv0)
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨hxPsi, hxL⟩, hxGammaKeys⟩, hxtau1⟩, hxb0⟩, hxtauv0⟩ := hx
  have hxGamma : x ∉ Gamma := by
    intro hm
    exact hxGammaKeys (Finmap.mem_keys.mpr hm)
  have hfresh : (x, Basis.std tau0) ∉ Psi :=
    (EvalCtx.avoidB_spec hxPsi).1 _
  have hP' : V2.PCarrier
      (Psi.extend x (Basis.std tau0) (.var x tauv0)) :=
    hP.extend_var hfresh (V2.evalT_fv h0eval hP.1) h0eval
      (fun a b heq => ⟨tauv0, heq ▸ hanc0⟩)
  have hcov' : V2.VarsCovered ∅ (Finmap.insert x tau0 Gamma)
      (Psi.extend x (Basis.std tau0) (.var x tauv0)) := hcov.extend_var
  have hwf' : V2.CtxWF' ∅ (Finmap.insert x tau0 Gamma) := by
    have h := RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
      (b := Basis.std tau0) hwf Finmap.notMem_empty hxGamma
      (Basis.std_valid tau0 ht0)
    simpa only [Basis.tof_std] using h
  obtain ⟨tauv1, _hTy1, hAt1⟩ :=
    ih1 x hxL _ hP' hcov' hwf'
  have hlctauv0 : ValTy.lc tauv0 :=
    evalT_lc h0eval hP.1.toEvalCtxLc
  have hlctauv1 : ValTy.lc tauv1 :=
    evalT_lc hAt1.erase hP'.1.toEvalCtxLc
  obtain ⟨L1, hcod⟩ := checkedTyAt_cofinite_of_fresh laws hwf
    ⟨k0, ⟨ht0⟩⟩ hxGamma hAt1 hxPsi hxb0 hxtauv0 hxtau1
    hlctauv0 hlctauv1
  let tauvOut := ValTy.closeRec 0 x tauv1
  have hAtOut : C.TyAt Gamma Psi (Basis.std (.piTy tau0 tau1))
      (.piTy tauv0 tauvOut) := by
    apply C.TyAt.frame (Basis.std_valid (.piTy tau0 tau1) (.piTy L ht0 ht1))
      hAt0 L1
    intro y hy
    have hc := hcod y hy
    rw [Basis.std_openVar] at hc
    simpa only [tauvOut, Basis.tof_std] using hc
  exact ⟨.piTy tauv0 tauvOut, checkedTy_of_tyAtStd hAtOut, hAtOut⟩

/-! ## Linear binders -/

theorem checked_arm_llam_real_wf
    (laws : CheckedRenameLaws) :
    forall {Delta : LCtx} {Gamma : NLCtx} {s : Space} {e : Term}
      (L : Finset Name),
      SValid Gamma s ->
      (forall y, y ∉ L -> HasType (Finmap.insert y s Delta) Gamma
        (Term.openVar y e) (.space .real)) ->
      cMotiveSWF Gamma s ->
      (forall y, y ∉ L -> cMotiveHWF (Finmap.insert y s Delta) Gamma
        (Term.openVar y e) (.space .real)) ->
      cMotiveHWF Delta Gamma (.llam s .real e) (.space (.dual s)) := by
  intro Delta Gamma s e L hs hbody ihs ihbody Psi hP hcov hwf
  obtain ⟨sv, hsv⟩ := ihs Psi hP hcov.drop_lin (ctxWF_dropLin hwf)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Psi ∪ L ∪ Delta.keys ∪ Gamma.keys ∪ Term.fv e ∪
      Basis.fv (Basis.stdSpace s) ∪ ValSpace.fv sv)
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨⟨hxPsi, hxL⟩, hxDeltaKeys⟩, hxGammaKeys⟩,
    hxe⟩, hxb⟩, hxsv⟩ := hx
  have hxDelta : x ∉ Delta := by
    intro hm
    exact hxDeltaKeys (Finmap.mem_keys.mpr hm)
  have hxGamma : x ∉ Gamma := by
    intro hm
    exact hxGammaKeys (Finmap.mem_keys.mpr hm)
  have heval : ValTy.EvalT Psi (.space s) (.space sv) := .space hsv.erase
  have hfresh : (x, Basis.stdSpace s) ∉ Psi :=
    (EvalCtx.avoidB_spec hxPsi).1 _
  have hP' : V2.PCarrier
      (Psi.extend x (Basis.stdSpace s) (.var x (.space sv))) :=
    hP.extend_var hfresh (V2.evalT_fv heval hP.1) heval
      (fun _ _ h => nomatch h)
  have hcov' : V2.VarsCovered (Finmap.insert x s Delta) Gamma
      (Psi.extend x (Basis.stdSpace s) (.var x (.space sv))) :=
    hcov.extend_var_lin
  have hwf' : V2.CtxWF' (Finmap.insert x s Delta) Gamma := by
    have h := RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
      (b := Basis.stdSpace s) hwf hxDelta hxGamma
      (Basis.stdSpace_valid s hs)
    simpa only [Basis.sof_stdSpace] using h
  obtain ⟨v, tauv, hv⟩ := ihbody x hxL _ hP' hcov' hwf'
  have hv' : C.Term (Finmap.insert x s Delta) Gamma
      (Psi.extend x (Basis.stdSpace s) (.var x (.space sv)))
      (Term.openVar x e) .one
      (.reshap v (.space .real) tauv) (.space .real) :=
    retag hv tyAt_one_any
  have hlcsv : ValSpace.lc sv :=
    realize_lc_joint.1 hsv.erase hP.1.toEvalCtxLc
  obtain ⟨L1, hfam⟩ := checkedTerm_llam_cofinite_of_placeholder laws
    hwf ⟨hs⟩ hxDelta hxGamma hv' hxPsi hxb hxsv hxe
    (by simp [Basis.fv]) (by simp [ValTy.fv, ValSpace.fv]) hlcsv
  let env : Fin (ValSpace.dofUB sv) -> ValExpr := fun i =>
    ValExpr.subst x (.delta i.val sv) (.reshap v (.space .real) tauv)
  have hspaceDual : C.Space Gamma Psi (.dual s) sv :=
    .dual ⟨.dual hs⟩ hsv
  have hAtOut : C.TyAt Gamma Psi (.dual (Basis.stdSpace s)) (.space sv) := by
    simpa only [Basis.std, Basis.stdSpace] using
      (checked_tyAt_space (.dual hs) hspaceDual)
  have ht : Nonempty (HasType Delta Gamma
      (.llam (Basis.sof (Basis.stdSpace s)) .real e)
      (Basis.tof (.dual (Basis.stdSpace s)))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType Delta Gamma (.llam s .real e) (.space (.dual s)))
        from ⟨.llam_real L hs hbody⟩)
  have hstep := C.Term.llam_assemble_real
    (b' := Basis.stdSpace s) (e := e) (env := env)
    (Basis.htof_stdSpace s) ht
    (.dual (Basis.stdSpace_valid s hs)
      (by rw [Basis.tof_stdSpace, Basis.sof_stdSpace])) hAtOut
    (by simpa only [Basis.sof_stdSpace] using hsv) L1
    (fun y hy i => by
      simpa only [env, Basis.sof_stdSpace] using hfam y hy i.val)
  exact ⟨_, _, by
    simpa only [Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_llam_tensor_wf
    (laws : CheckedRenameLaws) :
    forall {Delta : LCtx} {Gamma : NLCtx} {s0 s : Space} {e : Term}
      (L : Finset Name),
      s ≠ .real -> SValid Gamma s0 -> SValid Gamma s ->
      (forall y, y ∉ L -> HasType (Finmap.insert y s0 Delta) Gamma
        (Term.openVar y e) (.space s)) ->
      cMotiveSWF Gamma s0 -> cMotiveSWF Gamma s ->
      (forall y, y ∉ L -> cMotiveHWF (Finmap.insert y s0 Delta) Gamma
        (Term.openVar y e) (.space s)) ->
      cMotiveHWF Delta Gamma (.llam s0 s e)
        (.space (.tprod (.dual s0) s)) := by
  intro Delta Gamma s0 s e L hne hs0 hs hbody ihs0 ihs ihbody
    Psi hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ihs0 Psi hP hcov.drop_lin (ctxWF_dropLin hwf)
  obtain ⟨sv, hsv⟩ := ihs Psi hP hcov.drop_lin (ctxWF_dropLin hwf)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Psi ∪ L ∪ Delta.keys ∪ Gamma.keys ∪ Term.fv e ∪
      Basis.fv (Basis.stdSpace s0) ∪ Basis.fv (Basis.stdSpace s) ∪
      ValSpace.fv sv0 ∪ ValSpace.fv sv)
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hxPsi, hxL⟩, hxDeltaKeys⟩, hxGammaKeys⟩,
    hxe⟩, hxb0⟩, hxbs⟩, hxsv0⟩, hxsv⟩ := hx
  have hxDelta : x ∉ Delta := by
    intro hm
    exact hxDeltaKeys (Finmap.mem_keys.mpr hm)
  have hxGamma : x ∉ Gamma := by
    intro hm
    exact hxGammaKeys (Finmap.mem_keys.mpr hm)
  have heval0 : ValTy.EvalT Psi (.space s0) (.space sv0) := .space hsv0.erase
  have hfresh : (x, Basis.stdSpace s0) ∉ Psi :=
    (EvalCtx.avoidB_spec hxPsi).1 _
  have hP' : V2.PCarrier
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0))) :=
    hP.extend_var hfresh (V2.evalT_fv heval0 hP.1) heval0
      (fun _ _ h => nomatch h)
  have hcov' : V2.VarsCovered (Finmap.insert x s0 Delta) Gamma
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0))) :=
    hcov.extend_var_lin
  have hwf' : V2.CtxWF' (Finmap.insert x s0 Delta) Gamma := by
    have h := RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
      (b := Basis.stdSpace s0) hwf hxDelta hxGamma
      (Basis.stdSpace_valid s0 hs0)
    simpa only [Basis.sof_stdSpace] using h
  obtain ⟨v, tauv, hv⟩ := ihbody x hxL _ hP' hcov' hwf'
  have hsvExt : C.Space Gamma
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0))) s sv :=
    checkedSpace_extend hsv hxPsi
  have hAtCod : C.TyAt Gamma
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0)))
      (Basis.stdSpace s) (.space sv) := by
    simpa only [Basis.std, Basis.sof_stdSpace] using checked_tyAt_space hs hsvExt
  have hv' : C.Term (Finmap.insert x s0 Delta) Gamma
      (Psi.extend x (Basis.stdSpace s0) (.var x (.space sv0)))
      (Term.openVar x e) (Basis.stdSpace s)
      (.reshap v (.space sv) tauv) (.space sv) := retag hv hAtCod
  have hlcsv0 : ValSpace.lc sv0 :=
    realize_lc_joint.1 hsv0.erase hP.1.toEvalCtxLc
  obtain ⟨L1, hfam⟩ := checkedTerm_llam_cofinite_of_placeholder laws
    hwf ⟨hs0⟩ hxDelta hxGamma hv' hxPsi hxb0 hxsv0 hxe hxbs
    (by simpa only [ValTy.fv] using hxsv) hlcsv0
  let env : Fin (ValSpace.dofUB sv0) -> ValExpr := fun i =>
    ValExpr.subst x (.delta i.val sv0) (.reshap v (.space sv) tauv)
  have hspaceOut : C.Space Gamma Psi (.tprod (.dual s0) s) (.tprod sv0 sv) :=
    .tprod ⟨.tprod (.dual hs0) hs⟩ (.dual ⟨.dual hs0⟩ hsv0) hsv
  have hAtOut : C.TyAt Gamma Psi
      (.tprod (.dual (Basis.stdSpace s0)) (Basis.stdSpace s))
      (.space (.tprod sv0 sv)) := by
    simpa only [Basis.std, Basis.stdSpace] using
      (checked_tyAt_space (.tprod (.dual hs0) hs) hspaceOut)
  have ht : Nonempty (HasType Delta Gamma
      (.llam (Basis.sof (Basis.stdSpace s0)) (Basis.sof (Basis.stdSpace s)) e)
      (Basis.tof (.tprod (.dual (Basis.stdSpace s0)) (Basis.stdSpace s)))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType Delta Gamma (.llam s0 s e)
        (.space (.tprod (.dual s0) s))) from
        ⟨.llam_tensor L hne hs0 hs hbody⟩)
  have hbv : Basis.BasisValid Gamma
      (.tprod (.dual (Basis.stdSpace s0)) (Basis.stdSpace s)) :=
    .tprod
      (.dual (Basis.stdSpace_valid s0 hs0)
        (by rw [Basis.tof_stdSpace, Basis.sof_stdSpace]))
      (Basis.stdSpace_valid s hs)
      rfl
      (by rw [Basis.tof_stdSpace, Basis.sof_stdSpace])
  have hstep := C.Term.llam_assemble
    (b' := Basis.stdSpace s0) (b := Basis.stdSpace s)
    (e := e) (env := env)
    (Basis.htof_stdSpace s0) ht hbv hAtOut
    (by simpa only [Basis.sof_stdSpace] using hsv0)
    (by simpa only [Basis.sof_stdSpace] using hsv) L1
    (fun y hy i => by
      simpa only [env, Basis.sof_stdSpace] using hfam y hy i.val)
  exact ⟨_, _, by
    simpa only [Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

/-! ## Nonlinear binder -/

theorem checked_arm_nllam_wf
    (laws : CheckedRenameLaws) :
    forall {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind} {e : Term}
      (L : Finset Name)
      (ht : TValid Gamma (.piTy tau0 tau1) (.arrow k0 k1))
      (hbody : forall y, y ∉ L -> HasType ∅ (Finmap.insert y tau0 Gamma)
        (Term.openVar y e) (Ty.openVar y tau1)),
      cMotiveTWF Gamma (.piTy tau0 tau1) ->
      (forall y, y ∉ L -> cMotiveHWF ∅ (Finmap.insert y tau0 Gamma)
        (Term.openVar y e) (Ty.openVar y tau1)) ->
      cMotiveHWF ∅ Gamma (.nllam tau0 e) (.piTy tau0 tau1) := by
  intro Gamma tau0 tau1 k0 k1 e L ht hbody ihT ihbody Psi hP hcov hwf
  cases ht with
  | piTy Lv ht0 htvalid1 =>
      obtain ⟨tauvPi, _hTyPi, hAtPi⟩ := ihT Psi hP hcov hwf
      obtain ⟨tauv0, tauv1, rfl, hbv, hdom, LAt, hcod⟩ :=
        tyAtStdPi_inv hAtPi
      have h0eval : ValTy.EvalT Psi tau0 tauv0 := by
        simpa only [Basis.tof_std] using hdom.erase
      have hanc0 : V2.StdAnchored Psi tau0 tauv0 := tyAt_stdAnchored hdom
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
        (EvalCtx.avoidB Psi ∪ L ∪ LAt ∪ Gamma.keys ∪ Term.fv e ∪
          Ty.fv tau1 ∪ Basis.fv (Basis.std tau0) ∪ ValTy.fv tauv0)
      simp only [Finset.mem_union, not_or] at hx
      obtain ⟨⟨⟨⟨⟨⟨⟨hxPsi, hxL⟩, hxLAt⟩, hxGammaKeys⟩,
        hxe⟩, hxtau1⟩, hxb0⟩, hxtauv0⟩ := hx
      have hxGamma : x ∉ Gamma := by
        intro hm
        exact hxGammaKeys (Finmap.mem_keys.mpr hm)
      have hfresh : (x, Basis.std tau0) ∉ Psi :=
        (EvalCtx.avoidB_spec hxPsi).1 _
      have hP' : V2.PCarrier
          (Psi.extend x (Basis.std tau0) (.var x tauv0)) :=
        hP.extend_var hfresh (V2.evalT_fv h0eval hP.1) h0eval
          (fun a b heq => ⟨tauv0, heq ▸ hanc0⟩)
      have hcov' : V2.VarsCovered ∅ (Finmap.insert x tau0 Gamma)
          (Psi.extend x (Basis.std tau0) (.var x tauv0)) := hcov.extend_var
      have hwf' : V2.CtxWF' ∅ (Finmap.insert x tau0 Gamma) := by
        have h := RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
          (b := Basis.std tau0) hwf Finmap.notMem_empty hxGamma
          (Basis.std_valid tau0 ht0)
        simpa only [Basis.tof_std] using h
      obtain ⟨v, tauv, hv⟩ := ihbody x hxL _ hP' hcov' hwf'
      have hcodx := hcod x hxLAt
      have hv' := retag hv hcodx
      have hlctauv0 : ValTy.lc tauv0 :=
        evalT_lc h0eval hP.1.toEvalCtxLc
      have hlcv : ValExpr.lc (.reshap v (ValTy.openVar x tauv0 tauv1) tauv) :=
        opStep_lc hv'.erase hP'.1.toEvalCtxLc
      have hlctauv1 : ValTy.lc (ValTy.openVar x tauv0 tauv1) :=
        evalT_lc hcodx.erase hP'.1.toEvalCtxLc
      obtain ⟨LTerm, hterm⟩ := checkedTerm_nllam_cofinite_of_fresh
        laws hwf ⟨k0, ⟨ht0⟩⟩ hxGamma hv' hxPsi hxb0 hxtauv0
        hxe hxtau1 hlctauv0 hlcv hlctauv1
      obtain ⟨LTy, hty⟩ := checkedTyAt_cofinite_of_fresh laws hwf
        ⟨k0, ⟨ht0⟩⟩ hxGamma hcodx hxPsi hxb0 hxtauv0
        hxtau1 hlctauv0 hlctauv1
      let tauvOut := ValTy.closeRec 0 x (ValTy.openVar x tauv0 tauv1)
      let env := ValExpr.closeRec 0 x
        (.reshap v (ValTy.openVar x tauv0 tauv1) tauv)
      have hAtOut : C.TyAt Gamma Psi
          (.frame (Basis.std tau0) (Basis.std tau1))
          (.piTy tauv0 tauvOut) := by
        apply C.TyAt.frame hbv hdom LTy
        intro y hy
        have hc := hty y hy
        rw [Basis.std_openVar] at hc
        simpa only [tauvOut, Basis.tof_std] using hc
      have htTerm : Nonempty (HasType ∅ Gamma (.nllam tau0 e)
          (Basis.tof (.frame (Basis.std tau0) (Basis.std tau1)))) := by
        simpa only [Basis.tof, Basis.tof_std] using
          (show Nonempty (HasType ∅ Gamma (.nllam tau0 e)
            (.piTy tau0 tau1)) from
            ⟨.nllam L (.piTy Lv ht0 htvalid1) hbody⟩)
      have hstep := C.Term.nllam
        (b₀ := Basis.std tau0) (b₁ := Basis.std tau1)
        (env := env)
        (Basis.tof_std tau0) (Basis.tof_std tau1) htTerm
        (Basis.std_valid (.piTy tau0 tau1) (.piTy Lv ht0 htvalid1))
        hAtOut hdom (LTerm ∪ LTy)
        (fun y hy => by
          have hyt : y ∉ LTerm :=
            fun hm => hy (Finset.mem_union_left _ hm)
          have hc := hterm y hyt
          rw [Basis.std_openVar] at hc
          simpa only [env, tauvOut, Basis.tof_std] using hc)
        (fun y hy => by
          have hyy : y ∉ LTy :=
            fun hm => hy (Finset.mem_union_right _ hm)
          have hc := hty y hyy
          rw [Basis.std_openVar] at hc
          simpa only [tauvOut, Basis.tof_std] using hc)
      exact ⟨_, _, by simpa only [Basis.std] using hstep⟩

end RawCertifiedBinderProgressSpike
end GLang
