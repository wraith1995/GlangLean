import GLang.Proofs.Progress.CheckedInterfaces

/-!
# Constructor-local checked progress arms

This file develops the direct checked counterpart of the ordinary progress
master.  It deliberately keeps the existing `HasType` induction as the
driver: every value mentioned in a `C.Term` conclusion is therefore also the
literal value produced after erasure.
-/

namespace GLang
namespace RawCertifiedProgressScratch

open OperationalStrengthening
open RawCertifiedOperational

private theorem tyAt_stdAnchored_of_eq :
    forall {Γ : NLCtx} {Ψ : EvalCtx} {b : Basis} {τv : ValTy},
      C.TyAt Γ Ψ b τv -> forall {τ : Ty}, b = Basis.std τ ->
        V2.StdAnchored Ψ τ τv := by
  intro Γ Ψ b τv h
  intro tau heq
  refine (C.TyAt.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ Psi b tauV _ =>
      forall tau, b = Basis.std tau -> V2.StdAnchored Psi tau tauV)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    (fun {_ _} => True.intro) (fun {_ _} => True.intro)
    ?spaceDual ?spaceKer ?spaceCoker
    ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
    ?tySpace ?tyPi
    ?tyAtSpace ?tyAtFrame
    ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
    ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
    ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
    ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
    ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
    ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
    ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
    ?termAppL ?termAppI ?termNllam ?termAppNVal
    ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
    ?termZero ?termRlit h) tau heq
  case tyAtSpace =>
    intro Gamma Psi b sv htof hbv hspace _ tau heq
    cases tau with
    | space s =>
        have htof' : Basis.tof b = .space s := by
          rw [heq, Basis.tof_std]
        have hsof : Basis.sof b = s :=
          Ty.space.inj (htof.symm.trans htof')
        exact .space (by rw [← hsof]; exact .space hspace.erase)
    | piTy tau0 tau1 =>
        have htof' := congrArg Basis.tof heq
        simp only [Basis.tof_std] at htof'
        rw [htof] at htof'
        simp at htof'
  case tyAtFrame =>
    intro Gamma Psi b0 b1 tauV0 tauV1 hbv hdom L hcod
      ihdom ihcod tau heq
    cases tau with
    | space s =>
        have htof' := congrArg Basis.tof heq
        simp [Basis.tof, Basis.tof_std] at htof'
    | piTy tau0 tau1 =>
        have heq' : b0 = Basis.std tau0 ∧ b1 = Basis.std tau1 := by
          simpa only [Basis.std, Basis.frame.injEq] using heq
        refine .piTy (ihdom tau0 heq'.1) L ?_
        intro y hy
        have hc := ihcod y hy (Ty.openVar y tau1)
          (by rw [heq'.2, ← Basis.std_openVar])
        simpa only [heq'.1] using hc
  all_goals simp

/-- An exact certificate at the literal standard basis is precisely the
recursive standard anchoring needed by higher-order progress. -/
theorem tyAt_stdAnchored
    {Gamma : NLCtx} {Psi : EvalCtx} {tau : Ty} {tauV : ValTy}
    (h : C.TyAt Gamma Psi (Basis.std tau) tauV) :
    V2.StdAnchored Psi tau tauV :=
  tyAt_stdAnchored_of_eq h rfl

/-- Full space-head inversion of a `C.TyAt` certificate. -/
theorem checkedTyAt_space_inv_full
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {s : Space} {tauV : ValTy}
    (htof : Basis.tof b = .space s) (h : C.TyAt Gamma Psi b tauV) :
    exists sv, tauV = .space sv /\ C.Space Gamma Psi (Basis.sof b) sv := by
  refine (C.TyAt.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun Gamma Psi b tauV _ =>
      forall s, Basis.tof b = .space s ->
        exists sv, tauV = .space sv /\ C.Space Gamma Psi (Basis.sof b) sv)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    (fun {_ _} => True.intro) (fun {_ _} => True.intro)
    ?spaceDual ?spaceKer ?spaceCoker
    ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
    ?tySpace ?tyPi
    ?tyAtSpace ?tyAtFrame
    ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
    ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
    ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
    ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
    ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
    ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
    ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
    ?termAppL ?termAppI ?termNllam ?termAppNVal
    ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
    ?termZero ?termRlit h) s htof
  case tyAtSpace =>
    intro Gamma Psi b sv hshape hbv hspace _ s htof
    exact ⟨sv, rfl, hspace⟩
  case tyAtFrame =>
    intro Gamma Psi b0 b1 tauV0 tauV1 hbv hdom L hcod
      ihdom ihcod s htof
    simp [Basis.tof] at htof
  all_goals simp

/-- Full frame-head inversion, exposing the domain and codomain certificates. -/
theorem checkedTyAt_frame_inv_full
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {tauV : ValTy}
    (h : C.TyAt Gamma Psi (.frame b0 b1) tauV) :
    exists tauV0 tauV1,
      tauV = .piTy tauV0 tauV1 /\
      C.TyAt Gamma Psi b0 tauV0 /\
      exists L : Finset Name, forall y, y ∉ L ->
        C.TyAt (Finmap.insert y (Basis.tof b0) Gamma)
          (Psi.extend y b0 (.var y tauV0))
          (Basis.openVar y b1) (ValTy.openVar y tauV0 tauV1) := by
  have result := C.TyAt.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun Gamma Psi b tauV _ =>
      forall b0 b1, b = .frame b0 b1 ->
        exists tauV0 tauV1,
          tauV = .piTy tauV0 tauV1 /\
          C.TyAt Gamma Psi b0 tauV0 /\
          exists L : Finset Name, forall y, y ∉ L ->
            C.TyAt (Finmap.insert y (Basis.tof b0) Gamma)
              (Psi.extend y b0 (.var y tauV0))
              (Basis.openVar y b1) (ValTy.openVar y tauV0 tauV1))
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    (fun {_ _} => True.intro) (fun {_ _} => True.intro)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp)
    (by simp) (by simp)
    (by
      intro Gamma Psi b sv htof hbv hspace _ c0 c1 heq
      rw [heq] at htof
      simp [Basis.tof] at htof)
    (by
      intro Gamma Psi d0 d1 tauV0 tauV1 hbv hdom L hcod
        ihdom ihcod c0 c1 heq
      cases heq
      exact ⟨tauV0, tauV1, rfl, hdom, L, hcod⟩)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp)
    (by simp)
    h
  exact result b0 b1 rfl

/-- Retag a checked run at the same source basis.  The inserted reshape is
part of the ordinary value too, so literal erasure remains exact. -/
theorem retag
    (h : C.Term Δ Γ Ψ e b v τv)
    (hτv' : C.TyAt Γ Ψ b τv') :
    C.Term Δ Γ Ψ e b (.reshap v τv' τv) τv' :=
  .reshape_cob h.hasType h.basisValid hτv' h

/-- Restrict the forward-only covering to the nonlinear context. -/
theorem checkedDropLin
    (h : V2.VarsCovered Δ Γ Ψ) : V2.VarsCovered ∅ Γ Ψ :=
  ⟨fun _ _ hx => by simp [Finmap.lookup_empty] at hx, h.2⟩

/-! ## Space and type-formation arms -/

theorem checked_arm_empty :
    ∀ {Γ : NLCtx}, cMotiveS Γ .empty := by
  intro Γ Ψ _ _
  exact ⟨.empty, .empty⟩

theorem checked_arm_real :
    ∀ {Γ : NLCtx}, cMotiveS Γ .real := by
  intro Γ Ψ _ _
  exact ⟨.real, .real⟩

theorem checked_arm_dual :
    ∀ {Γ : NLCtx} {s : Space} (hs : SValid Γ s),
      cMotiveS Γ s → cMotiveS Γ (.dual s) := by
  intro Γ s hs ih Ψ hP hcov
  obtain ⟨sv, hsv⟩ := ih Ψ hP hcov
  exact ⟨sv, .dual ⟨.dual hs⟩ hsv⟩

theorem checked_arm_dsum :
    ∀ {Γ : NLCtx} {s₀ s₁ : Space} (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ → cMotiveS Γ (.dsum s₀ s₁) := by
  intro Γ s₀ s₁ hs₀ hs₁ ih₀ ih₁ Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  exact ⟨.dsum sv₀ sv₁, .dsum ⟨.dsum hs₀ hs₁⟩ hsv₀ hsv₁⟩

theorem checked_arm_tprod :
    ∀ {Γ : NLCtx} {s₀ s₁ : Space} (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ → cMotiveS Γ (.tprod s₀ s₁) := by
  intro Γ s₀ s₁ hs₀ hs₁ ih₀ ih₁ Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  exact ⟨.tprod sv₀ sv₁, .tprod ⟨.tprod hs₀ hs₁⟩ hsv₀ hsv₁⟩

/-- The standard type certificate induced by a checked realization of a
well-formed space. -/
theorem checked_tyAt_space
    (hs : SValid Γ s) (hsv : C.Space Γ Ψ s sv) :
    C.TyAt Γ Ψ (Basis.std (.space s)) (.space sv) := by
  apply C.TyAt.space (Basis.htof_stdSpace s) (Basis.stdSpace_valid s hs)
  · simpa only [Basis.std, Basis.sof_stdSpace] using hsv

theorem checked_arm_ty_space :
    ∀ {Γ : NLCtx} {s : Space} (hs : SValid Γ s),
      cMotiveS Γ s → cMotiveT Γ (.space s) := by
  intro Γ s hs ih Ψ hP hcov
  obtain ⟨sv, hsv⟩ := ih Ψ hP hcov
  exact ⟨.space sv, .space hsv, checked_tyAt_space hs hsv⟩

/-- Common checked witness alignment for the four FFS space constructors. -/
theorem checked_ffs_witness
    (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
    (hsv₀ : C.Space Γ Ψ s₀ sv₀) (hsv₁ : C.Space Γ Ψ s₁ sv₁)
    (he : C.Term ∅ Γ Ψ e
      (Basis.std (.space (.tprod (.dual s₀) s₁))) v τv) :
    ∃ v',
      C.Space Γ Ψ
        (Basis.sof (Basis.stdSpace (.tprod (.dual s₀) s₁)))
        (.tprod sv₀ sv₁) ∧
      C.Term ∅ Γ Ψ e
        (Basis.std (.space (.tprod (.dual s₀) s₁))) v'
        (.space (.tprod sv₀ sv₁)) := by
  have hsvb : C.Space Γ Ψ
      (Basis.sof (Basis.stdSpace (.tprod (.dual s₀) s₁)))
      (.tprod sv₀ sv₁) := by
    rw [Basis.sof_stdSpace]
    exact .tprod ⟨.tprod (.dual hs₀) hs₁⟩ (.dual ⟨.dual hs₀⟩ hsv₀) hsv₁
  have hτv : C.TyAt Γ Ψ
      (Basis.std (.space (.tprod (.dual s₀) s₁)))
      (.space (.tprod sv₀ sv₁)) :=
    checked_tyAt_space (.tprod (.dual hs₀) hs₁)
      (by exact .tprod ⟨.tprod (.dual hs₀) hs₁⟩ (.dual ⟨.dual hs₀⟩ hsv₀) hsv₁)
  exact ⟨_, hsvb, retag he hτv⟩

theorem checked_arm_ker :
    ∀ {Γ : NLCtx} {e : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (he : HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH ∅ Γ e (.space (.tprod (.dual s₀) s₁)) →
      cMotiveS Γ (.ker s₀ s₁ e) := by
  intro Γ e s₀ s₁ hs₀ hs₁ he ih₀ ih₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, τv, hev⟩ := ihe Ψ hP hcov
  obtain ⟨v', hsvb, hev'⟩ := checked_ffs_witness hs₀ hs₁ hsv₀ hsv₁ hev
  exact ⟨_, .ker ⟨.ker hs₀ hs₁ he⟩ (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩
    hsvb hev'⟩

theorem checked_arm_coker :
    ∀ {Γ : NLCtx} {e : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (he : HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH ∅ Γ e (.space (.tprod (.dual s₀) s₁)) →
      cMotiveS Γ (.coker s₀ s₁ e) := by
  intro Γ e s₀ s₁ hs₀ hs₁ he ih₀ ih₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, τv, hev⟩ := ihe Ψ hP hcov
  obtain ⟨v', hsvb, hev'⟩ := checked_ffs_witness hs₀ hs₁ hsv₀ hsv₁ hev
  exact ⟨_, .coker ⟨.coker hs₀ hs₁ he⟩ (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩
    hsvb hev'⟩

theorem checked_arm_img :
    ∀ {Γ : NLCtx} {e : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (he : HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH ∅ Γ e (.space (.tprod (.dual s₀) s₁)) →
      cMotiveS Γ (.img s₀ s₁ e) := by
  intro Γ e s₀ s₁ hs₀ hs₁ he ih₀ ih₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, τv, hev⟩ := ihe Ψ hP hcov
  obtain ⟨v', hsvb, hev'⟩ := checked_ffs_witness hs₀ hs₁ hsv₀ hsv₁ hev
  exact ⟨_, .img ⟨.img hs₀ hs₁ he⟩ (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩
    hsvb hev'⟩

theorem checked_arm_coimg :
    ∀ {Γ : NLCtx} {e : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (he : HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH ∅ Γ e (.space (.tprod (.dual s₀) s₁)) →
      cMotiveS Γ (.coimg s₀ s₁ e) := by
  intro Γ e s₀ s₁ hs₀ hs₁ he ih₀ ih₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, τv, hev⟩ := ihe Ψ hP hcov
  obtain ⟨v', hsvb, hev'⟩ := checked_ffs_witness hs₀ hs₁ hsv₀ hsv₁ hev
  exact ⟨_, .coimg ⟨.coimg hs₀ hs₁ he⟩ (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩
    hsvb hev'⟩

/-! ## First-order term arms -/

theorem checked_arm_zero :
    ∀ {Δ : LCtx} {Γ : NLCtx} {s : Space} (hs : SValid Γ s),
      cMotiveS Γ s → cMotiveH Δ Γ (.zero s) (.space s) := by
  intro Δ Γ s hs ihs Ψ hP hcov
  obtain ⟨sv, hsv⟩ := ihs Ψ hP (checkedDropLin hcov)
  have hτv := checked_tyAt_space hs hsv
  have hsv' : C.Space Γ Ψ (Basis.sof (Basis.stdSpace s)) sv := by
    simpa only [Basis.sof_stdSpace] using hsv
  have ht : Nonempty (HasType Δ Γ (.zero (Basis.sof (Basis.stdSpace s)))
      (Basis.tof (Basis.stdSpace s))) := by
    simpa only [Basis.sof_stdSpace, Basis.htof_stdSpace] using
      (show Nonempty (HasType Δ Γ (.zero s) (.space s)) from ⟨.zero hs⟩)
  have h := C.Term.zero (Δ := Δ) (Ψ := Ψ)
    (Basis.htof_stdSpace s) ht
    (Basis.stdSpace_valid s hs) hτv hsv'
  exact ⟨.zero sv, .space sv,
    by simpa only [Basis.std, Basis.sof_stdSpace] using h⟩

theorem checked_arm_real_lit :
    ∀ {Γ : NLCtx} (r : ℝ),
      cMotiveH ∅ Γ (.real r) (.space .real) := by
  intro Γ r Ψ _ _
  have hτv : C.TyAt Γ Ψ .one (.space .real) :=
    .space rfl .one .real
  exact ⟨.rlit r, .space .real, .rlit r ⟨.real_lit r⟩ hτv⟩

theorem checked_arm_smul :
    ∀ {Δ₀ Δ₁ : LCtx} {Γ : NLCtx} {e₀ e₁ : Term} {s : Space}
      (hs : SValid Γ s) (hdisj : Finmap.Disjoint Δ₀ Δ₁)
      (ht₀ : HasType Δ₀ Γ e₀ (.space .real))
      (ht₁ : HasType Δ₁ Γ e₁ (.space s)),
      cMotiveS Γ s → cMotiveH Δ₀ Γ e₀ (.space .real) →
      cMotiveH Δ₁ Γ e₁ (.space s) →
      cMotiveH (Δ₀ ∪ Δ₁) Γ (.smul e₀ e₁) (.space s) := by
  intro Δ₀ Δ₁ Γ e₀ e₁ s hs hdisj ht₀ ht₁ ihs ih₀ ih₁ Ψ hP hcov
  obtain ⟨hcov₀, hcov₁⟩ := hcov.mono_lin hdisj
  obtain ⟨sv, hsv⟩ := ihs Ψ hP (checkedDropLin hcov)
  obtain ⟨v₀, τv₀, hv₀⟩ := ih₀ Ψ hP hcov₀
  obtain ⟨v₁, τv₁, hv₁⟩ := ih₁ Ψ hP hcov₁
  have hout := checked_tyAt_space hs hsv
  have hreal : C.TyAt Γ Ψ .one (.space .real) :=
    .space rfl .one .real
  have hv₀' := retag hv₀ hreal
  have hv₁' := retag hv₁ hout
  have ht : Nonempty (HasType (Δ₀ ∪ Δ₁) Γ (.smul e₀ e₁)
      (Basis.tof (Basis.stdSpace s))) := by
    simpa only [Basis.htof_stdSpace, Basis.sof_stdSpace] using
      (show Nonempty (HasType (Δ₀ ∪ Δ₁) Γ (.smul e₀ e₁) (.space s)) from
        ⟨.smul hs hdisj ht₀ ht₁⟩)
  exact ⟨_, .space sv, .scale hdisj (Basis.htof_stdSpace s)
    ht (Basis.stdSpace_valid s hs)
    hout hv₀' hv₁'⟩

theorem checked_arm_add :
    ∀ {Δ : LCtx} {Γ : NLCtx} {e₀ e₁ : Term} {s : Space}
      (hs : SValid Γ s) (ht₀ : HasType Δ Γ e₀ (.space s))
      (ht₁ : HasType Δ Γ e₁ (.space s)),
      cMotiveS Γ s → cMotiveH Δ Γ e₀ (.space s) →
      cMotiveH Δ Γ e₁ (.space s) →
      cMotiveH Δ Γ (.add e₀ e₁) (.space s) := by
  intro Δ Γ e₀ e₁ s hs ht₀ ht₁ ihs ih₀ ih₁ Ψ hP hcov
  obtain ⟨sv, hsv⟩ := ihs Ψ hP (checkedDropLin hcov)
  obtain ⟨v₀, τv₀, hv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨v₁, τv₁, hv₁⟩ := ih₁ Ψ hP hcov
  have hout := checked_tyAt_space hs hsv
  have hv₀' := retag hv₀ hout
  have hv₁' := retag hv₁ hout
  have ht : Nonempty (HasType Δ Γ (.add e₀ e₁)
      (Basis.tof (Basis.stdSpace s))) := by
    simpa only [Basis.htof_stdSpace, Basis.sof_stdSpace] using
      (show Nonempty (HasType Δ Γ (.add e₀ e₁) (.space s)) from
        ⟨.add hs ht₀ ht₁⟩)
  exact ⟨_, .space sv, .add (Basis.htof_stdSpace s)
    ht (Basis.stdSpace_valid s hs)
    hout hv₀' hv₁'⟩

theorem checked_arm_inner :
    ∀ {Γ : NLCtx} {s : Space} (hs : SValid Γ s),
      cMotiveS Γ s →
      cMotiveH ∅ Γ (.inner s) (.space (.tprod (.dual s) (.dual s))) := by
  intro Γ s hs ihs Ψ hP hcov
  obtain ⟨sv, hsv⟩ := ihs Ψ hP hcov
  have hsout : SValid Γ (.tprod (.dual s) (.dual s)) :=
    .tprod (.dual hs) (.dual hs)
  have hsvout : C.Space Γ Ψ (.tprod (.dual s) (.dual s)) (.tprod sv sv) :=
    .tprod ⟨hsout⟩ (.dual ⟨.dual hs⟩ hsv) (.dual ⟨.dual hs⟩ hsv)
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType ∅ Γ (.inner s)
      (Basis.tof (.tprod (.dual (Basis.stdSpace s))
        (.dual (Basis.stdSpace s))))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType ∅ Γ (.inner s)
        (.space (.tprod (.dual s) (.dual s)))) from ⟨.inner hs⟩)
  have h := C.Term.inner_std (Γ := Γ) (Ψ := Ψ)
    (b₀ := Basis.stdSpace s) (s := s)
    (Basis.isStd_stdSpace s) (Basis.sof_stdSpace s)
    ht
    (Basis.stdSpace_valid _ hsout) hout hsv
  exact ⟨.idelta sv, .space (.tprod sv sv), by
    simpa only [Basis.std, Basis.sof_stdSpace] using h⟩

theorem checked_arm_dsumE :
    ∀ {Δ : LCtx} {Γ : NLCtx} {e₀ e₁ : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (ht₀ : HasType Δ Γ e₀ (.space s₀))
      (ht₁ : HasType Δ Γ e₁ (.space s₁)),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH Δ Γ e₀ (.space s₀) → cMotiveH Δ Γ e₁ (.space s₁) →
      cMotiveH Δ Γ (.dsumE e₀ e₁) (.space (.dsum s₀ s₁)) := by
  intro Δ Γ e₀ e₁ s₀ s₁ hs₀ hs₁ ht₀ ht₁ ihs₀ ihs₁ ih₀ ih₁ Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ihs₀ Ψ hP (checkedDropLin hcov)
  obtain ⟨sv₁, hsv₁⟩ := ihs₁ Ψ hP (checkedDropLin hcov)
  obtain ⟨v₀, τv₀, hv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨v₁, τv₁, hv₁⟩ := ih₁ Ψ hP hcov
  have hτ₀ := checked_tyAt_space hs₀ hsv₀
  have hτ₁ := checked_tyAt_space hs₁ hsv₁
  have hsout : SValid Γ (.dsum s₀ s₁) := .dsum hs₀ hs₁
  have hsvout : C.Space Γ Ψ (.dsum s₀ s₁) (.dsum sv₀ sv₁) :=
    .dsum ⟨hsout⟩ hsv₀ hsv₁
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType Δ Γ (.dsumE e₀ e₁)
      (Basis.tof (.dsum (Basis.stdSpace s₀) (Basis.stdSpace s₁)))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType Δ Γ (.dsumE e₀ e₁) (.space (.dsum s₀ s₁))) from
        ⟨.dsumE hs₀ hs₁ ht₀ ht₁⟩)
  exact ⟨_, .space (.dsum sv₀ sv₁),
    .dsumE (Basis.htof_stdSpace s₀) (Basis.htof_stdSpace s₁)
      ht (Basis.stdSpace_valid _ hsout)
      hout (retag hv₀ hτ₀) (retag hv₁ hτ₁)⟩

theorem checked_arm_tprodE :
    ∀ {Δ₀ Δ₁ : LCtx} {Γ : NLCtx} {e₀ e₁ : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (hdisj : Finmap.Disjoint Δ₀ Δ₁)
      (ht₀ : HasType Δ₀ Γ e₀ (.space s₀))
      (ht₁ : HasType Δ₁ Γ e₁ (.space s₁)),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH Δ₀ Γ e₀ (.space s₀) → cMotiveH Δ₁ Γ e₁ (.space s₁) →
      cMotiveH (Δ₀ ∪ Δ₁) Γ (.tprodE e₀ e₁) (.space (.tprod s₀ s₁)) := by
  intro Δ₀ Δ₁ Γ e₀ e₁ s₀ s₁ hs₀ hs₁ hdisj ht₀ ht₁ ihs₀ ihs₁ ih₀ ih₁ Ψ hP hcov
  obtain ⟨hcov₀, hcov₁⟩ := hcov.mono_lin hdisj
  obtain ⟨sv₀, hsv₀⟩ := ihs₀ Ψ hP (checkedDropLin hcov)
  obtain ⟨sv₁, hsv₁⟩ := ihs₁ Ψ hP (checkedDropLin hcov)
  obtain ⟨v₀, τv₀, hv₀⟩ := ih₀ Ψ hP hcov₀
  obtain ⟨v₁, τv₁, hv₁⟩ := ih₁ Ψ hP hcov₁
  have hτ₀ := checked_tyAt_space hs₀ hsv₀
  have hτ₁ := checked_tyAt_space hs₁ hsv₁
  have hsout : SValid Γ (.tprod s₀ s₁) := .tprod hs₀ hs₁
  have hsvout : C.Space Γ Ψ (.tprod s₀ s₁) (.tprod sv₀ sv₁) :=
    .tprod ⟨hsout⟩ hsv₀ hsv₁
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType (Δ₀ ∪ Δ₁) Γ (.tprodE e₀ e₁)
      (Basis.tof (.tprod (Basis.stdSpace s₀) (Basis.stdSpace s₁)))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType (Δ₀ ∪ Δ₁) Γ (.tprodE e₀ e₁)
        (.space (.tprod s₀ s₁))) from ⟨.tprodE hs₀ hs₁ hdisj ht₀ ht₁⟩)
  exact ⟨_, .space (.tprod sv₀ sv₁),
    .tprodE hdisj (Basis.htof_stdSpace s₀) (Basis.htof_stdSpace s₁)
      ht (Basis.stdSpace_valid _ hsout)
      hout (retag hv₀ hτ₀) (retag hv₁ hτ₁)⟩

/-! ## Linear application and standard pseudo-inverse arms -/

theorem checked_arm_app_linear :
    ∀ {Δ₀ Δ₁ : LCtx} {Γ : NLCtx} {e₀ e₁ : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (hdisj : Finmap.Disjoint Δ₀ Δ₁)
      (ht₀ : HasType Δ₀ Γ e₀ (.space (.tprod (.dual s₀) s₁)))
      (ht₁ : HasType Δ₁ Γ e₁ (.space s₀)),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH Δ₀ Γ e₀ (.space (.tprod (.dual s₀) s₁)) →
      cMotiveH Δ₁ Γ e₁ (.space s₀) →
      cMotiveH (Δ₀ ∪ Δ₁) Γ (.appL s₀ s₁ e₀ e₁) (.space s₁) := by
  intro Δ₀ Δ₁ Γ e₀ e₁ s₀ s₁ hs₀ hs₁ hdisj ht₀ ht₁ ihs₀ ihs₁ ih₀ ih₁ Ψ hP hcov
  obtain ⟨hcov₀, hcov₁⟩ := hcov.mono_lin hdisj
  obtain ⟨sv₀, hsv₀⟩ := ihs₀ Ψ hP (checkedDropLin hcov)
  obtain ⟨sv₁, hsv₁⟩ := ihs₁ Ψ hP (checkedDropLin hcov)
  obtain ⟨v₀, τv₀, hv₀⟩ := ih₀ Ψ hP hcov₀
  obtain ⟨v₁, τv₁, hv₁⟩ := ih₁ Ψ hP hcov₁
  have hmatS : SValid Γ (.tprod (.dual s₀) s₁) := .tprod (.dual hs₀) hs₁
  have hmatV : C.Space Γ Ψ (.tprod (.dual s₀) s₁) (.tprod sv₀ sv₁) :=
    .tprod ⟨hmatS⟩ (.dual ⟨.dual hs₀⟩ hsv₀) hsv₁
  have hmat := checked_tyAt_space hmatS hmatV
  have harg := checked_tyAt_space hs₀ hsv₀
  have hout := checked_tyAt_space hs₁ hsv₁
  have ht : Nonempty (HasType (Δ₀ ∪ Δ₁) Γ
      (.appL (Basis.sof (Basis.stdSpace s₀))
        (Basis.sof (Basis.stdSpace s₁)) e₀ e₁)
      (Basis.tof (Basis.stdSpace s₁))) := by
    simpa only [Basis.sof_stdSpace, Basis.htof_stdSpace] using
      (show Nonempty (HasType (Δ₀ ∪ Δ₁) Γ (.appL s₀ s₁ e₀ e₁) (.space s₁)) from
        ⟨.app_linear hs₀ hs₁ hdisj ht₀ ht₁⟩)
  have hsv₀' : C.Space Γ Ψ (Basis.sof (Basis.stdSpace s₀)) sv₀ := by
    simpa only [Basis.sof_stdSpace] using hsv₀
  have h := C.Term.appL_lin
    (b₀ := Basis.stdSpace s₀) (b₁ := Basis.stdSpace s₁)
    hdisj (Basis.htof_stdSpace s₁) ht (Basis.stdSpace_valid s₁ hs₁)
    hsv₀' hout (retag hv₀ hmat) (retag hv₁ harg)
  exact ⟨_, .space sv₁, by
    simpa only [Basis.std, Basis.sof_stdSpace] using h⟩

theorem checked_arm_app_inner :
    ∀ {Δ₀ Δ₁ : LCtx} {Γ : NLCtx} {e₀ e₁ : Term} {s : Space}
      (hs : SValid Γ s) (hdisj : Finmap.Disjoint Δ₀ Δ₁)
      (ht₀ : HasType Δ₀ Γ e₀ (.space (.dual s)))
      (ht₁ : HasType Δ₁ Γ e₁ (.space s)),
      cMotiveS Γ s → cMotiveH Δ₀ Γ e₀ (.space (.dual s)) →
      cMotiveH Δ₁ Γ e₁ (.space s) →
      cMotiveH (Δ₀ ∪ Δ₁) Γ (.appI s e₀ e₁) (.space .real) := by
  intro Δ₀ Δ₁ Γ e₀ e₁ s hs hdisj ht₀ ht₁ ihs ih₀ ih₁ Ψ hP hcov
  obtain ⟨hcov₀, hcov₁⟩ := hcov.mono_lin hdisj
  obtain ⟨sv, hsv⟩ := ihs Ψ hP (checkedDropLin hcov)
  obtain ⟨v₀, τv₀, hv₀⟩ := ih₀ Ψ hP hcov₀
  obtain ⟨v₁, τv₁, hv₁⟩ := ih₁ Ψ hP hcov₁
  have hfun := checked_tyAt_space (.dual hs) (.dual ⟨.dual hs⟩ hsv)
  have harg := checked_tyAt_space hs hsv
  have hout : C.TyAt Γ Ψ .one (.space .real) :=
    .space rfl .one .real
  have ht : Nonempty (HasType (Δ₀ ∪ Δ₁) Γ
      (.appI (Basis.sof (Basis.stdSpace s)) e₀ e₁) (Basis.tof .one)) := by
    simpa only [Basis.sof_stdSpace, Basis.tof] using
      (show Nonempty (HasType (Δ₀ ∪ Δ₁) Γ (.appI s e₀ e₁) (.space .real)) from
        ⟨.app_inner hs hdisj ht₀ ht₁⟩)
  have hsv' : C.Space Γ Ψ (Basis.sof (Basis.stdSpace s)) sv := by
    simpa only [Basis.sof_stdSpace] using hsv
  have h := C.Term.appI_lin (b₀ := Basis.stdSpace s)
    hdisj ht hsv' hout (retag hv₀ hfun) (retag hv₁ harg)
  exact ⟨_, .space .real, by
    simpa only [Basis.std, Basis.sof_stdSpace] using h⟩

theorem checked_arm_pinv_tensor :
    ∀ {Γ : NLCtx} {e : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (ht : HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH ∅ Γ e (.space (.tprod (.dual s₀) s₁)) →
      cMotiveH ∅ Γ (.pinvT s₀ s₁ e) (.space (.tprod (.dual s₁) s₀)) := by
  intro Γ e s₀ s₁ hs₀ hs₁ ht ihs₀ ihs₁ ih Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ihs₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ihs₁ Ψ hP hcov
  obtain ⟨v, τv, hv⟩ := ih Ψ hP hcov
  have hinS : SValid Γ (.tprod (.dual s₀) s₁) := .tprod (.dual hs₀) hs₁
  have hinV : C.Space Γ Ψ (.tprod (.dual s₀) s₁) (.tprod sv₀ sv₁) :=
    .tprod ⟨hinS⟩ (.dual ⟨.dual hs₀⟩ hsv₀) hsv₁
  have hin := checked_tyAt_space hinS hinV
  have houtS : SValid Γ (.tprod (.dual s₁) s₀) := .tprod (.dual hs₁) hs₀
  have houtV : C.Space Γ Ψ (.tprod (.dual s₁) s₀) (.tprod sv₁ sv₀) :=
    .tprod ⟨houtS⟩ (.dual ⟨.dual hs₁⟩ hsv₁) hsv₀
  have hout := checked_tyAt_space houtS houtV
  have hty : Nonempty (HasType ∅ Γ
      (.pinvT (Basis.sof (Basis.stdSpace s₀))
        (Basis.sof (Basis.stdSpace s₁)) e)
      (Basis.tof (.tprod (.dual (Basis.stdSpace s₁)) (Basis.stdSpace s₀)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Γ (.pinvT s₀ s₁ e)
        (.space (.tprod (.dual s₁) s₀))) from ⟨.pinv_tensor hs₀ hs₁ ht⟩)
  have hstep := C.Term.pinvT_std
    (b₀ := Basis.stdSpace s₁) (b₁ := Basis.stdSpace s₀)
    (Basis.isStd_stdSpace s₁) (Basis.isStd_stdSpace s₀)
    hty (Basis.stdSpace_valid _ houtS) hout (retag hv hin)
  exact ⟨_, .space (.tprod sv₁ sv₀), by
    simpa only [Basis.std, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_pinv_dual :
    ∀ {Γ : NLCtx} {e : Term} {s : Space}
      (hs : SValid Γ s) (ht : HasType ∅ Γ e (.space (.dual s))),
      cMotiveS Γ s → cMotiveH ∅ Γ e (.space (.dual s)) →
      cMotiveH ∅ Γ (.pinvD s e) (.space (.tprod (.dual .real) s)) := by
  intro Γ e s hs ht ihs ih Ψ hP hcov
  obtain ⟨sv, hsv⟩ := ihs Ψ hP hcov
  obtain ⟨v, τv, hv⟩ := ih Ψ hP hcov
  have hin := checked_tyAt_space (.dual hs) (.dual ⟨.dual hs⟩ hsv)
  have houtS : SValid Γ (.tprod (.dual .real) s) :=
    .tprod (.dual .real) hs
  have houtV : C.Space Γ Ψ (.tprod (.dual .real) s) (.tprod .real sv) :=
    .tprod ⟨houtS⟩ (.dual ⟨SValid.dual SValid.real⟩ .real) hsv
  have hout := checked_tyAt_space houtS houtV
  have hty : Nonempty (HasType ∅ Γ
      (.pinvD (Basis.sof (Basis.stdSpace s)) e)
      (Basis.tof (.tprod (.dual (.one)) (Basis.stdSpace s)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Γ (.pinvD s e)
        (.space (.tprod (.dual .real) s))) from ⟨.pinv_dual hs ht⟩)
  have hstep := C.Term.pinvD_std
    (b₀ := .one) (b₁ := Basis.stdSpace s)
    rfl trivial (Basis.isStd_stdSpace s) hty
    (Basis.stdSpace_valid _ houtS) hout (retag hv hin)
  exact ⟨_, .space (.tprod .real sv), by
    simpa only [Basis.std, Basis.sof_stdSpace] using hstep⟩

/-! ## Subspace and embedding arms -/

theorem checked_inner_at
    (hs : SValid Γ s) (hsv : C.Space Γ Ψ s sv) :
    C.Term ∅ Γ Ψ (.inner s)
      (.tprod (.dual (Basis.stdSpace s)) (.dual (Basis.stdSpace s)))
      (.idelta sv) (.space (.tprod sv sv)) := by
  have hsout : SValid Γ (.tprod (.dual s) (.dual s)) :=
    .tprod (.dual hs) (.dual hs)
  have hsvout : C.Space Γ Ψ (.tprod (.dual s) (.dual s)) (.tprod sv sv) :=
    .tprod ⟨hsout⟩ (.dual ⟨.dual hs⟩ hsv) (.dual ⟨.dual hs⟩ hsv)
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType ∅ Γ (.inner s)
      (Basis.tof (.tprod (.dual (Basis.stdSpace s))
        (.dual (Basis.stdSpace s))))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType ∅ Γ (.inner s)
        (.space (.tprod (.dual s) (.dual s)))) from ⟨.inner hs⟩)
  exact .inner_std (Basis.isStd_stdSpace s) (Basis.sof_stdSpace s)
    ht (Basis.stdSpace_valid _ hsout) hout hsv

theorem checked_arm_sub_ker :
    ∀ {Γ : NLCtx} {e : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (he : HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH ∅ Γ e (.space (.tprod (.dual s₀) s₁)) →
      cMotiveSub Γ (.ker s₀ s₁ e) s₀ := by
  intro Γ e s₀ s₁ hs₀ hs₁ he ihs₀ ihs₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ihs₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ihs₁ Ψ hP hcov
  obtain ⟨v, τv, hev⟩ := ihe Ψ hP hcov
  obtain ⟨v', hsvb, hev'⟩ := checked_ffs_witness hs₀ hs₁ hsv₀ hsv₁ hev
  let svk : ValSpace :=
    .ffs .kernel (.tprod sv₀ sv₁) (.reshapBase v' (.tprod sv₀ sv₁))
  have hker : C.Space Γ Ψ (.ker s₀ s₁ e) svk :=
    .ker ⟨.ker hs₀ hs₁ he⟩ (Basis.sof_stdSpace _)
      ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩
      hsvb hev'
  have hsout : SValid Γ (.tprod (.dual (.ker s₀ s₁ e)) s₀) :=
    .tprod (.dual (.ker hs₀ hs₁ he)) hs₀
  have hsvout : C.Space Γ Ψ (.tprod (.dual (.ker s₀ s₁ e)) s₀)
      (.tprod svk sv₀) :=
    .tprod ⟨hsout⟩ (.dual ⟨.dual (.ker hs₀ hs₁ he)⟩ hker) hsv₀
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType ∅ Γ
      (.embed (.ker s₀ s₁ e))
      (Basis.tof (.tprod
        (.dual (.proj (.ker s₀ s₁ e) (Basis.stdSpace s₀) (Basis.stdSpace s₁)))
        (Basis.stdSpace s₀)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Γ (.embed (.ker s₀ s₁ e))
        (.space (.tprod (.dual (.ker s₀ s₁ e)) s₀))) from
        ⟨.embed (.sub_ker hs₀ hs₁ he)⟩)
  have hstep := C.Term.embed_ker
    (b₀ := Basis.stdSpace s₀) (b₁ := Basis.stdSpace s₁)
    (Basis.sof_stdSpace s₀) (Basis.sof_stdSpace s₁)
    ht (Basis.stdSpace_valid _ hsout) hout
    (checked_inner_at hs₀ hsv₀) (checked_inner_at hs₁ hsv₁) hev'
  exact ⟨_, _, by
    simpa only [svk, Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_sub_coker :
    ∀ {Γ : NLCtx} {e : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (he : HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH ∅ Γ e (.space (.tprod (.dual s₀) s₁)) →
      cMotiveSub Γ (.coker s₀ s₁ e) s₀ := by
  intro Γ e s₀ s₁ hs₀ hs₁ he ihs₀ ihs₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ihs₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ihs₁ Ψ hP hcov
  obtain ⟨v, τv, hev⟩ := ihe Ψ hP hcov
  obtain ⟨v', hsvb, hev'⟩ := checked_ffs_witness hs₀ hs₁ hsv₀ hsv₁ hev
  let svc : ValSpace :=
    .ffs .cokernel (.tprod sv₀ sv₁) (.reshapBase v' (.tprod sv₀ sv₁))
  have hcoker : C.Space Γ Ψ (.coker s₀ s₁ e) svc :=
    .coker ⟨.coker hs₀ hs₁ he⟩ (Basis.sof_stdSpace _)
      ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩
      hsvb hev'
  have hsout : SValid Γ (.tprod (.dual (.coker s₀ s₁ e)) s₀) :=
    .tprod (.dual (.coker hs₀ hs₁ he)) hs₀
  have hsvout : C.Space Γ Ψ (.tprod (.dual (.coker s₀ s₁ e)) s₀)
      (.tprod svc sv₀) :=
    .tprod ⟨hsout⟩ (.dual ⟨.dual (.coker hs₀ hs₁ he)⟩ hcoker) hsv₀
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType ∅ Γ (.embed (.coker s₀ s₁ e))
      (Basis.tof (.tprod
        (.dual (.proj (.coker s₀ s₁ e) (Basis.stdSpace s₀) (Basis.stdSpace s₁)))
        (Basis.stdSpace s₀)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Γ (.embed (.coker s₀ s₁ e))
        (.space (.tprod (.dual (.coker s₀ s₁ e)) s₀))) from
        ⟨.embed (.sub_coker hs₀ hs₁ he)⟩)
  have hstep := C.Term.embed_coker
    (b₀ := Basis.stdSpace s₀) (b₁ := Basis.stdSpace s₁)
    (Basis.sof_stdSpace s₀) (Basis.sof_stdSpace s₁)
    ht (Basis.stdSpace_valid _ hsout) hout
    (checked_inner_at hs₀ hsv₀) (checked_inner_at hs₁ hsv₁) hev'
  exact ⟨_, _, by
    simpa only [svc, Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_sub_img :
    ∀ {Γ : NLCtx} {e : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (he : HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH ∅ Γ e (.space (.tprod (.dual s₀) s₁)) →
      cMotiveSub Γ (.img s₀ s₁ e) s₁ := by
  intro Γ e s₀ s₁ hs₀ hs₁ he ihs₀ ihs₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ihs₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ihs₁ Ψ hP hcov
  obtain ⟨v, τv, hev⟩ := ihe Ψ hP hcov
  obtain ⟨v', hsvb, hev'⟩ := checked_ffs_witness hs₀ hs₁ hsv₀ hsv₁ hev
  let svi : ValSpace :=
    .ffs .image (.tprod sv₀ sv₁) (.reshapBase v' (.tprod sv₀ sv₁))
  have himg : C.Space Γ Ψ (.img s₀ s₁ e) svi :=
    .img ⟨.img hs₀ hs₁ he⟩ (Basis.sof_stdSpace _)
      ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩
      hsvb hev'
  have hsout : SValid Γ (.tprod (.dual (.img s₀ s₁ e)) s₁) :=
    .tprod (.dual (.img hs₀ hs₁ he)) hs₁
  have hsvout : C.Space Γ Ψ (.tprod (.dual (.img s₀ s₁ e)) s₁)
      (.tprod svi sv₁) :=
    .tprod ⟨hsout⟩ (.dual ⟨.dual (.img hs₀ hs₁ he)⟩ himg) hsv₁
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType ∅ Γ (.embed (.img s₀ s₁ e))
      (Basis.tof (.tprod
        (.dual (.proj (.img s₀ s₁ e) (Basis.stdSpace s₀) (Basis.stdSpace s₁)))
        (Basis.stdSpace s₁)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Γ (.embed (.img s₀ s₁ e))
        (.space (.tprod (.dual (.img s₀ s₁ e)) s₁))) from
        ⟨.embed (.sub_img hs₀ hs₁ he)⟩)
  have hstep := C.Term.embed_img
    (b₀ := Basis.stdSpace s₀) (b₁ := Basis.stdSpace s₁)
    (Basis.sof_stdSpace s₀) (Basis.sof_stdSpace s₁)
    ht (Basis.stdSpace_valid _ hsout) hout
    (checked_inner_at hs₀ hsv₀) (checked_inner_at hs₁ hsv₁) hev'
  exact ⟨_, _, by
    simpa only [svi, Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_sub_coimg :
    ∀ {Γ : NLCtx} {e : Term} {s₀ s₁ : Space}
      (hs₀ : SValid Γ s₀) (hs₁ : SValid Γ s₁)
      (he : HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))),
      cMotiveS Γ s₀ → cMotiveS Γ s₁ →
      cMotiveH ∅ Γ e (.space (.tprod (.dual s₀) s₁)) →
      cMotiveSub Γ (.coimg s₀ s₁ e) s₁ := by
  intro Γ e s₀ s₁ hs₀ hs₁ he ihs₀ ihs₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ihs₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ihs₁ Ψ hP hcov
  obtain ⟨v, τv, hev⟩ := ihe Ψ hP hcov
  obtain ⟨v', hsvb, hev'⟩ := checked_ffs_witness hs₀ hs₁ hsv₀ hsv₁ hev
  let svi : ValSpace :=
    .ffs .coimage (.tprod sv₀ sv₁) (.reshapBase v' (.tprod sv₀ sv₁))
  have hcoimg : C.Space Γ Ψ (.coimg s₀ s₁ e) svi :=
    .coimg ⟨.coimg hs₀ hs₁ he⟩ (Basis.sof_stdSpace _)
      ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩
      hsvb hev'
  have hsout : SValid Γ (.tprod (.dual (.coimg s₀ s₁ e)) s₁) :=
    .tprod (.dual (.coimg hs₀ hs₁ he)) hs₁
  have hsvout : C.Space Γ Ψ (.tprod (.dual (.coimg s₀ s₁ e)) s₁)
      (.tprod svi sv₁) :=
    .tprod ⟨hsout⟩ (.dual ⟨.dual (.coimg hs₀ hs₁ he)⟩ hcoimg) hsv₁
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType ∅ Γ (.embed (.coimg s₀ s₁ e))
      (Basis.tof (.tprod
        (.dual (.proj (.coimg s₀ s₁ e) (Basis.stdSpace s₀) (Basis.stdSpace s₁)))
        (Basis.stdSpace s₁)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Γ (.embed (.coimg s₀ s₁ e))
        (.space (.tprod (.dual (.coimg s₀ s₁ e)) s₁))) from
        ⟨.embed (.sub_coimg hs₀ hs₁ he)⟩)
  have hstep := C.Term.embed_coimg
    (b₀ := Basis.stdSpace s₀) (b₁ := Basis.stdSpace s₁)
    (Basis.sof_stdSpace s₀) (Basis.sof_stdSpace s₁)
    ht (Basis.stdSpace_valid _ hsout) hout
    (checked_inner_at hs₀ hsv₀) (checked_inner_at hs₁ hsv₁) hev'
  exact ⟨_, _, by
    simpa only [svi, Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_embed :
    ∀ {Γ : NLCtx} {s₀ s₁ : Space} (hsub : SubType Γ s₀ s₁),
      cMotiveSub Γ s₀ s₁ →
      cMotiveH ∅ Γ (.embed s₀) (.space (.tprod (.dual s₀) s₁)) := by
  intro Γ s₀ s₁ hsub ih Ψ hP hcov
  exact ih Ψ hP hcov

structure CheckedProgressOpenArms : Prop where
  ty_pi :
    ∀ {Γ : NLCtx} {τ₀ τ₁ : Ty} {k₀ k₁ : Kind} (L : Finset Name)
      (ht₀ : TValid Γ τ₀ k₀)
      (ht₁ : ∀ y, y ∉ L → TValid (Finmap.insert y τ₀ Γ) (Ty.openVar y τ₁) k₁),
      cMotiveT Γ τ₀ →
      (∀ y, y ∉ L → cMotiveT (Finmap.insert y τ₀ Γ) (Ty.openVar y τ₁)) →
      cMotiveT Γ (.piTy τ₀ τ₁)
  var_lin :
    ∀ {Γ : NLCtx} {x : Name} {s : Space},
      cMotiveH (Finmap.singleton x s) Γ (.var x) (.space s)
  var_nlin :
    ∀ {Γ : NLCtx} {x : Name} {τ : Ty},
      Γ.lookup x = some τ → cMotiveH ∅ Γ (.var x) τ
  promote :
    ∀ {Δ : LCtx} {Γ' : NLCtx} {e : Term} {τ : Ty} (lin : LCtx),
      Finmap.Disjoint lin Δ → Finmap.Disjoint lin.toNL Γ' →
      PromoteFresh lin Δ Γ' →
      ∀ (ht : HasType (lin ∪ Δ) Γ' e τ),
        cMotiveH (lin ∪ Δ) Γ' e τ →
        cMotiveH Δ (lin.toNL ∪ Γ') e τ
  llam_real :
    ∀ {Δ : LCtx} {Γ : NLCtx} {s : Space} {e : Term} (L : Finset Name),
      SValid Γ s →
      (∀ y, y ∉ L →
        HasType (Finmap.insert y s Δ) Γ (Term.openVar y e) (.space .real)) →
      cMotiveS Γ s →
      (∀ y, y ∉ L →
        cMotiveH (Finmap.insert y s Δ) Γ (Term.openVar y e) (.space .real)) →
      cMotiveH Δ Γ (.llam s .real e) (.space (.dual s))
  llam_tensor :
    ∀ {Δ : LCtx} {Γ : NLCtx} {s₀ s : Space} {e : Term} (L : Finset Name),
      s ≠ .real → SValid Γ s₀ → SValid Γ s →
      (∀ y, y ∉ L →
        HasType (Finmap.insert y s₀ Δ) Γ (Term.openVar y e) (.space s)) →
      cMotiveS Γ s₀ → cMotiveS Γ s →
      (∀ y, y ∉ L →
        cMotiveH (Finmap.insert y s₀ Δ) Γ (Term.openVar y e) (.space s)) →
      cMotiveH Δ Γ (.llam s₀ s e) (.space (.tprod (.dual s₀) s))
  nllam :
    ∀ {Γ : NLCtx} {τ₀ τ₁ : Ty} {k₀ k₁ : Kind} {e : Term} (L : Finset Name)
      (ht : TValid Γ (.piTy τ₀ τ₁) (.arrow k₀ k₁))
      (hbody : ∀ y, y ∉ L →
        HasType ∅ (Finmap.insert y τ₀ Γ) (Term.openVar y e) (Ty.openVar y τ₁)),
      cMotiveT Γ (.piTy τ₀ τ₁) →
      (∀ y, y ∉ L →
        cMotiveH ∅ (Finmap.insert y τ₀ Γ) (Term.openVar y e) (Ty.openVar y τ₁)) →
      cMotiveH ∅ Γ (.nllam τ₀ e) (.piTy τ₀ τ₁)
  app_nonlinear :
    ∀ {Γ : NLCtx} {e₀ e₁ : Term} {τ₀ τ₁ : Ty}
      (ht₀ : HasType ∅ Γ e₀ (.piTy τ₀ τ₁))
      (ht₁ : HasType ∅ Γ e₁ τ₀),
      cMotiveH ∅ Γ e₀ (.piTy τ₀ τ₁) → cMotiveH ∅ Γ e₁ τ₀ →
      cMotiveH ∅ Γ (.appN e₀ e₁) (Ty.instantiate e₁ τ₁)

/-- Checked progress from the eight source and basis induction cases. -/
theorem checked_progress_master_of (gaps : CheckedProgressOpenArms) :
    (∀ {Γ : NLCtx} {s : Space}, SValid Γ s → cMotiveS Γ s)
  ∧ (∀ {Γ : NLCtx} {τ : Ty} {k : Kind}, TValid Γ τ k → cMotiveT Γ τ)
  ∧ (∀ {Γ : NLCtx} {s₀ s₁ : Space}, SubType Γ s₀ s₁ → cMotiveSub Γ s₀ s₁)
  ∧ (∀ {Δ : LCtx} {Γ : NLCtx} {e : Term} {τ : Ty},
      HasType Δ Γ e τ → cMotiveH Δ Γ e τ) := by
  refine ⟨@fun Γ s h => ?_, @fun Γ τ k h => ?_,
    @fun Γ s₀ s₁ h => ?_, @fun Δ Γ e τ h => ?_⟩
  all_goals
    exact h.rec
      (motive_1 := fun Γ' s' _ => cMotiveS Γ' s')
      (motive_2 := fun Γ' τ' _k _ => cMotiveT Γ' τ')
      (motive_3 := fun Γ' s₀' s₁' _ => cMotiveSub Γ' s₀' s₁')
      (motive_4 := fun Δ' Γ' e' τ' _ => cMotiveH Δ' Γ' e' τ')
      -- SValid (9)
      checked_arm_empty checked_arm_real checked_arm_dual checked_arm_dsum
      checked_arm_tprod checked_arm_ker checked_arm_coker checked_arm_img
      checked_arm_coimg
      -- TValid (2)
      checked_arm_ty_space gaps.ty_pi
      -- SubType (4)
      checked_arm_sub_ker checked_arm_sub_coker checked_arm_sub_img
      checked_arm_sub_coimg
      -- HasType (19)
      checked_arm_zero checked_arm_smul checked_arm_add checked_arm_inner
      checked_arm_real_lit checked_arm_app_linear checked_arm_app_inner
      gaps.app_nonlinear gaps.var_lin gaps.var_nlin checked_arm_pinv_tensor
      checked_arm_pinv_dual gaps.promote checked_arm_dsumE checked_arm_tprodE
      gaps.llam_real gaps.llam_tensor checked_arm_embed gaps.nllam

/-- Once the eight fields are constructed, the term projection is exactly the
requested `HasType → cMotiveH` entry point. -/
theorem checked_term_progress_of (gaps : CheckedProgressOpenArms)
    (ht : HasType Δ Γ e τ) : cMotiveH Δ Γ e τ :=
  (checked_progress_master_of gaps).2.2.2 ht

/-- The corresponding standard-basis progress theorem. -/
theorem certifiedStdProgress_of (gaps : CheckedProgressOpenArms) :
    CertifiedStdProgress := by
  intro Ψ Δ Γ e τ hwfΔΓ hwfΨ hwflc hanch hΓΨ hstd ht
  exact checked_term_progress_of gaps ht Ψ
    (V2.pCarrier_of hwfΨ hwflc hanch hstd) (V2.varsCovered_of hΓΨ)

/-! ## The separate arbitrary-basis seam -/

/-- Checked counterpart of `V2.BasisTransport`. -/
def CheckedBasisTransport : Prop :=
  ∀ (Δ : LCtx) (Γ : NLCtx) (Ψ : EvalCtx) (e : Term)
    (b₁ b₂ : Basis) (v₁ : ValExpr) (τv₁ : ValTy),
    V2.PCarrier Ψ → V2.VarsCovered ∅ Γ Ψ → V2.StoredWF Ψ →
    Basis.BasisValid Γ b₁ → Basis.IsTyBasis b₁ →
    Basis.BasisValid Γ b₂ → Basis.IsTyBasis b₂ →
    Basis.tof b₂ = Basis.tof b₁ →
    C.Term Δ Γ Ψ e b₁ v₁ τv₁ →
    ∃ v₂ τv₂, C.Term Δ Γ Ψ e b₂ v₂ τv₂

/-- Standard checked progress and checked basis transport are logically
separate obligations.  Together they yield the full concrete progress
interface at the caller-selected basis. -/
theorem certifiedProgress_of_std_and_transport
    (hstd : CertifiedStdProgress)
    (htransport : CheckedBasisTransport) : CertifiedProgress := by
  intro Ψ Δ Γ e τ b htele hwfΔΓ hwfΨ hwflc hanch hΓΨ ht hb htb htof
  have hcomplete : V2.StdComplete Ψ := V2.stdComplete_of_ctxTele htele
  obtain ⟨v₁, τv₁, hv₁⟩ :=
    hstd hwfΔΓ hwfΨ hwflc hanch hΓΨ hcomplete ht
  obtain ⟨k, ⟨hTV⟩⟩ := hb.tof_tvalid
  rw [htof] at hTV
  obtain ⟨v₂, τv₂, hv₂⟩ := htransport Δ Γ Ψ e
    (Basis.std τ) b v₁ τv₁
    (V2.pCarrier_of hwfΨ hwflc hanch hcomplete)
    (V2.varsCovered_of hΓΨ).drop_lin htele.storedWF
    (Basis.std_valid τ hTV) (Basis.isTyBasis_std τ)
    hb htb (htof.trans (Basis.tof_std τ).symm) hv₁
  exact ⟨v₂, τv₂, hv₂⟩

/-- Consequently, the complete checked-progress target has exactly two
independent proof inputs: the eight standard-basis typing arms and checked
basis transport. -/
theorem certifiedProgress_of
    (gaps : CheckedProgressOpenArms)
    (htransport : CheckedBasisTransport) : CertifiedProgress :=
  certifiedProgress_of_std_and_transport (certifiedStdProgress_of gaps) htransport

end RawCertifiedProgressScratch
end GLang
