import GLang.Proofs.Progress.Certificates.RawCertifiedWorldBinderProgress

/-!
# Constructor-local checked progress over a restricted evaluator world

These are the 26 concrete non-binder arms from
`RawCertifiedProgressArms`, localized to a world predicate and threaded with
the `CtxWF'` data needed by the eventual binder/variable arms.  The checked
operational constructions are unchanged.
-/

namespace GLang
namespace RawCertifiedWorldProgressArms

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedWorldBinderProgress

/-! ## Linear-context projections -/

theorem ctxWF_union_left
    {Delta0 Delta1 : LCtx} {Gamma : NLCtx}
    (h : V2.CtxWF' (Delta0 ∪ Delta1) Gamma) :
    V2.CtxWF' Delta0 Gamma where
  disjoint := by
    intro x hx
    exact h.disjoint x (Finmap.mem_union.mpr (Or.inl hx))
  lin_fv := by
    intro x s hx
    apply h.lin_fv x s
    rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hx)]
    exact hx
  nl_fv := h.nl_fv
  lin_valid := by
    intro x s hx
    apply h.lin_valid x s
    rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hx)]
    exact hx
  nl_valid := h.nl_valid

theorem ctxWF_union_right
    {Delta0 Delta1 : LCtx} {Gamma : NLCtx}
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (h : V2.CtxWF' (Delta0 ∪ Delta1) Gamma) :
    V2.CtxWF' Delta1 Gamma where
  disjoint := by
    intro x hx
    exact h.disjoint x (Finmap.mem_union.mpr (Or.inr hx))
  lin_fv := by
    intro x s hx
    have hx1 : x ∈ Delta1 := Finmap.mem_of_lookup_eq_some hx
    have hx0 : x ∉ Delta0 := fun hm => hdisj x hm hx1
    apply h.lin_fv x s
    rw [Finmap.lookup_union_right hx0]
    exact hx
  nl_fv := h.nl_fv
  lin_valid := by
    intro x s hx
    have hx1 : x ∈ Delta1 := Finmap.mem_of_lookup_eq_some hx
    have hx0 : x ∉ Delta0 := fun hm => hdisj x hm hx1
    apply h.lin_valid x s
    rw [Finmap.lookup_union_right hx0]
    exact hx
  nl_valid := h.nl_valid

/-! ## Space and type formation -/

theorem checked_arm_empty_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx}, cMotiveSWorld W Gamma .empty := by
  intro Gamma Psi _hW _hP _hcov _hwf
  exact ⟨.empty, .empty⟩

theorem checked_arm_real_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx}, cMotiveSWorld W Gamma .real := by
  intro Gamma Psi _hW _hP _hcov _hwf
  exact ⟨.real, .real⟩

theorem checked_arm_dual_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {s : Space} (hs : SValid Gamma s),
      cMotiveSWorld W Gamma s →
      cMotiveSWorld W Gamma (.dual s) := by
  intro Gamma s hs ih Psi hW hP hcov hwf
  obtain ⟨sv, hsv⟩ := ih Psi hW hP hcov hwf
  exact ⟨sv, .dual ⟨.dual hs⟩ hsv⟩

theorem checked_arm_dsum_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveSWorld W Gamma (.dsum s0 s1) := by
  intro Gamma s0 s1 hs0 hs1 ih0 ih1 Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ih0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ih1 Psi hW hP hcov hwf
  exact ⟨.dsum sv0 sv1, .dsum ⟨.dsum hs0 hs1⟩ hsv0 hsv1⟩

theorem checked_arm_tprod_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveSWorld W Gamma (.tprod s0 s1) := by
  intro Gamma s0 s1 hs0 hs1 ih0 ih1 Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ih0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ih1 Psi hW hP hcov hwf
  exact ⟨.tprod sv0 sv1, .tprod ⟨.tprod hs0 hs1⟩ hsv0 hsv1⟩

theorem checked_arm_ty_space_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {s : Space} (hs : SValid Gamma s),
      cMotiveSWorld W Gamma s →
      cMotiveTWorld W Gamma (.space s) := by
  intro Gamma s hs ih Psi hW hP hcov hwf
  obtain ⟨sv, hsv⟩ := ih Psi hW hP hcov hwf
  exact ⟨.space sv, .space hsv, checked_tyAt_space hs hsv⟩

private theorem checked_ffs_witness_world
    (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
    (hsv0 : C.Space Gamma Psi s0 sv0)
    (hsv1 : C.Space Gamma Psi s1 sv1)
    (he : C.Term ∅ Gamma Psi e
      (Basis.std (.space (.tprod (.dual s0) s1))) v tauv) :
    ∃ v',
      C.Space Gamma Psi
        (Basis.sof (Basis.stdSpace (.tprod (.dual s0) s1)))
        (.tprod sv0 sv1) ∧
      C.Term ∅ Gamma Psi e
        (Basis.std (.space (.tprod (.dual s0) s1))) v'
        (.space (.tprod sv0 sv1)) :=
  checked_ffs_witness hs0 hs1 hsv0 hsv1 he

theorem checked_arm_ker_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1))),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W ∅ Gamma e (.space (.tprod (.dual s0) s1)) →
      cMotiveSWorld W Gamma (.ker s0 s1 e) := by
  intro Gamma e s0 s1 hs0 hs1 he ih0 ih1 ihe Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ih0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ih1 Psi hW hP hcov hwf
  obtain ⟨v, tauv, hev⟩ := ihe Psi hW hP hcov hwf
  obtain ⟨v', hsvb, hev'⟩ :=
    checked_ffs_witness_world hs0 hs1 hsv0 hsv1 hev
  exact ⟨_, .ker ⟨.ker hs0 hs1 he⟩ (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
    hsvb hev'⟩

theorem checked_arm_coker_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1))),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W ∅ Gamma e (.space (.tprod (.dual s0) s1)) →
      cMotiveSWorld W Gamma (.coker s0 s1 e) := by
  intro Gamma e s0 s1 hs0 hs1 he ih0 ih1 ihe Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ih0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ih1 Psi hW hP hcov hwf
  obtain ⟨v, tauv, hev⟩ := ihe Psi hW hP hcov hwf
  obtain ⟨v', hsvb, hev'⟩ :=
    checked_ffs_witness_world hs0 hs1 hsv0 hsv1 hev
  exact ⟨_, .coker ⟨.coker hs0 hs1 he⟩ (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
    hsvb hev'⟩

theorem checked_arm_img_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1))),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W ∅ Gamma e (.space (.tprod (.dual s0) s1)) →
      cMotiveSWorld W Gamma (.img s0 s1 e) := by
  intro Gamma e s0 s1 hs0 hs1 he ih0 ih1 ihe Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ih0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ih1 Psi hW hP hcov hwf
  obtain ⟨v, tauv, hev⟩ := ihe Psi hW hP hcov hwf
  obtain ⟨v', hsvb, hev'⟩ :=
    checked_ffs_witness_world hs0 hs1 hsv0 hsv1 hev
  exact ⟨_, .img ⟨.img hs0 hs1 he⟩ (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
    hsvb hev'⟩

theorem checked_arm_coimg_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1))),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W ∅ Gamma e (.space (.tprod (.dual s0) s1)) →
      cMotiveSWorld W Gamma (.coimg s0 s1 e) := by
  intro Gamma e s0 s1 hs0 hs1 he ih0 ih1 ihe Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ih0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ih1 Psi hW hP hcov hwf
  obtain ⟨v, tauv, hev⟩ := ihe Psi hW hP hcov hwf
  obtain ⟨v', hsvb, hev'⟩ :=
    checked_ffs_witness_world hs0 hs1 hsv0 hsv1 hev
  exact ⟨_, .coimg ⟨.coimg hs0 hs1 he⟩ (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
    hsvb hev'⟩

/-! ## First-order term arms -/

theorem checked_arm_zero_world (W : EvalCtx → Prop) :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {s : Space}
      (hs : SValid Gamma s), cMotiveSWorld W Gamma s →
      cMotiveHWorld W Delta Gamma (.zero s) (.space s) := by
  intro Delta Gamma s hs ihs Psi hW hP hcov hwf
  obtain ⟨sv, hsv⟩ := ihs Psi hW hP (checkedDropLin hcov)
    (ctxWF_dropLin hwf)
  have htauv := checked_tyAt_space hs hsv
  have hsv' : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s)) sv := by
    simpa only [Basis.sof_stdSpace] using hsv
  have ht : Nonempty (HasType Delta Gamma (.zero (Basis.sof (Basis.stdSpace s)))
      (Basis.tof (Basis.stdSpace s))) := by
    simpa only [Basis.sof_stdSpace, Basis.htof_stdSpace] using
      (show Nonempty (HasType Delta Gamma (.zero s) (.space s)) from ⟨.zero hs⟩)
  have h := C.Term.zero (Δ := Delta) (Ψ := Psi)
    (Basis.htof_stdSpace s) ht (Basis.stdSpace_valid s hs) htauv hsv'
  exact ⟨.zero sv, .space sv,
    by simpa only [Basis.std, Basis.sof_stdSpace] using h⟩

theorem checked_arm_real_lit_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} (r : ℝ),
      cMotiveHWorld W ∅ Gamma (.real r) (.space .real) := by
  intro Gamma r Psi _hW _hP _hcov _hwf
  have htauv : C.TyAt Gamma Psi .one (.space .real) :=
    .space rfl .one .real
  exact ⟨.rlit r, .space .real, .rlit r ⟨.real_lit r⟩ htauv⟩

theorem checked_arm_smul_world (W : EvalCtx → Prop) :
    ∀ {Delta0 Delta1 : LCtx} {Gamma : NLCtx} {e0 e1 : Term} {s : Space}
      (hs : SValid Gamma s) (hdisj : Finmap.Disjoint Delta0 Delta1)
      (ht0 : HasType Delta0 Gamma e0 (.space .real))
      (ht1 : HasType Delta1 Gamma e1 (.space s)),
      cMotiveSWorld W Gamma s →
      cMotiveHWorld W Delta0 Gamma e0 (.space .real) →
      cMotiveHWorld W Delta1 Gamma e1 (.space s) →
      cMotiveHWorld W (Delta0 ∪ Delta1) Gamma (.smul e0 e1) (.space s) := by
  intro Delta0 Delta1 Gamma e0 e1 s hs hdisj ht0 ht1 ihs ih0 ih1
    Psi hW hP hcov hwf
  obtain ⟨hcov0, hcov1⟩ := hcov.mono_lin hdisj
  obtain ⟨sv, hsv⟩ := ihs Psi hW hP (checkedDropLin hcov)
    (ctxWF_dropLin hwf)
  obtain ⟨v0, tauv0, hv0⟩ :=
    ih0 Psi hW hP hcov0 (ctxWF_union_left hwf)
  obtain ⟨v1, tauv1, hv1⟩ :=
    ih1 Psi hW hP hcov1 (ctxWF_union_right hdisj hwf)
  have hout := checked_tyAt_space hs hsv
  have hreal : C.TyAt Gamma Psi .one (.space .real) :=
    .space rfl .one .real
  have hv0' := retag hv0 hreal
  have hv1' := retag hv1 hout
  have ht : Nonempty (HasType (Delta0 ∪ Delta1) Gamma (.smul e0 e1)
      (Basis.tof (Basis.stdSpace s))) := by
    simpa only [Basis.htof_stdSpace, Basis.sof_stdSpace] using
      (show Nonempty (HasType (Delta0 ∪ Delta1) Gamma (.smul e0 e1)
        (.space s)) from ⟨.smul hs hdisj ht0 ht1⟩)
  exact ⟨_, .space sv, .scale hdisj (Basis.htof_stdSpace s)
    ht (Basis.stdSpace_valid s hs) hout hv0' hv1'⟩

theorem checked_arm_add_world (W : EvalCtx → Prop) :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {e0 e1 : Term} {s : Space}
      (hs : SValid Gamma s) (ht0 : HasType Delta Gamma e0 (.space s))
      (ht1 : HasType Delta Gamma e1 (.space s)),
      cMotiveSWorld W Gamma s →
      cMotiveHWorld W Delta Gamma e0 (.space s) →
      cMotiveHWorld W Delta Gamma e1 (.space s) →
      cMotiveHWorld W Delta Gamma (.add e0 e1) (.space s) := by
  intro Delta Gamma e0 e1 s hs ht0 ht1 ihs ih0 ih1 Psi hW hP hcov hwf
  obtain ⟨sv, hsv⟩ := ihs Psi hW hP (checkedDropLin hcov)
    (ctxWF_dropLin hwf)
  obtain ⟨v0, tauv0, hv0⟩ := ih0 Psi hW hP hcov hwf
  obtain ⟨v1, tauv1, hv1⟩ := ih1 Psi hW hP hcov hwf
  have hout := checked_tyAt_space hs hsv
  have hv0' := retag hv0 hout
  have hv1' := retag hv1 hout
  have ht : Nonempty (HasType Delta Gamma (.add e0 e1)
      (Basis.tof (Basis.stdSpace s))) := by
    simpa only [Basis.htof_stdSpace, Basis.sof_stdSpace] using
      (show Nonempty (HasType Delta Gamma (.add e0 e1) (.space s)) from
        ⟨.add hs ht0 ht1⟩)
  exact ⟨_, .space sv, .add (Basis.htof_stdSpace s)
    ht (Basis.stdSpace_valid s hs) hout hv0' hv1'⟩

theorem checked_arm_inner_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {s : Space} (hs : SValid Gamma s),
      cMotiveSWorld W Gamma s →
      cMotiveHWorld W ∅ Gamma (.inner s)
        (.space (.tprod (.dual s) (.dual s))) := by
  intro Gamma s hs ihs Psi hW hP hcov hwf
  obtain ⟨sv, hsv⟩ := ihs Psi hW hP hcov hwf
  exact ⟨_, _, by
    simpa only [Basis.std, Basis.stdSpace] using checked_inner_at hs hsv⟩

theorem checked_arm_dsumE_world (W : EvalCtx → Prop) :
    ∀ {Delta : LCtx} {Gamma : NLCtx} {e0 e1 : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (ht0 : HasType Delta Gamma e0 (.space s0))
      (ht1 : HasType Delta Gamma e1 (.space s1)),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W Delta Gamma e0 (.space s0) →
      cMotiveHWorld W Delta Gamma e1 (.space s1) →
      cMotiveHWorld W Delta Gamma (.dsumE e0 e1) (.space (.dsum s0 s1)) := by
  intro Delta Gamma e0 e1 s0 s1 hs0 hs1 ht0 ht1 ihs0 ihs1 ih0 ih1
    Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ihs0 Psi hW hP (checkedDropLin hcov)
    (ctxWF_dropLin hwf)
  obtain ⟨sv1, hsv1⟩ := ihs1 Psi hW hP (checkedDropLin hcov)
    (ctxWF_dropLin hwf)
  obtain ⟨v0, tauv0, hv0⟩ := ih0 Psi hW hP hcov hwf
  obtain ⟨v1, tauv1, hv1⟩ := ih1 Psi hW hP hcov hwf
  have htau0 := checked_tyAt_space hs0 hsv0
  have htau1 := checked_tyAt_space hs1 hsv1
  have hsout : SValid Gamma (.dsum s0 s1) := .dsum hs0 hs1
  have hsvout : C.Space Gamma Psi (.dsum s0 s1) (.dsum sv0 sv1) :=
    .dsum ⟨hsout⟩ hsv0 hsv1
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType Delta Gamma (.dsumE e0 e1)
      (Basis.tof (.dsum (Basis.stdSpace s0) (Basis.stdSpace s1)))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType Delta Gamma (.dsumE e0 e1)
        (.space (.dsum s0 s1))) from ⟨.dsumE hs0 hs1 ht0 ht1⟩)
  exact ⟨_, .space (.dsum sv0 sv1),
    .dsumE (Basis.htof_stdSpace s0) (Basis.htof_stdSpace s1)
      ht (Basis.stdSpace_valid _ hsout)
      hout (retag hv0 htau0) (retag hv1 htau1)⟩

theorem checked_arm_tprodE_world (W : EvalCtx → Prop) :
    ∀ {Delta0 Delta1 : LCtx} {Gamma : NLCtx}
      {e0 e1 : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (hdisj : Finmap.Disjoint Delta0 Delta1)
      (ht0 : HasType Delta0 Gamma e0 (.space s0))
      (ht1 : HasType Delta1 Gamma e1 (.space s1)),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W Delta0 Gamma e0 (.space s0) →
      cMotiveHWorld W Delta1 Gamma e1 (.space s1) →
      cMotiveHWorld W (Delta0 ∪ Delta1) Gamma (.tprodE e0 e1)
        (.space (.tprod s0 s1)) := by
  intro Delta0 Delta1 Gamma e0 e1 s0 s1 hs0 hs1 hdisj ht0 ht1
    ihs0 ihs1 ih0 ih1 Psi hW hP hcov hwf
  obtain ⟨hcov0, hcov1⟩ := hcov.mono_lin hdisj
  obtain ⟨sv0, hsv0⟩ := ihs0 Psi hW hP (checkedDropLin hcov)
    (ctxWF_dropLin hwf)
  obtain ⟨sv1, hsv1⟩ := ihs1 Psi hW hP (checkedDropLin hcov)
    (ctxWF_dropLin hwf)
  obtain ⟨v0, tauv0, hv0⟩ :=
    ih0 Psi hW hP hcov0 (ctxWF_union_left hwf)
  obtain ⟨v1, tauv1, hv1⟩ :=
    ih1 Psi hW hP hcov1 (ctxWF_union_right hdisj hwf)
  have htau0 := checked_tyAt_space hs0 hsv0
  have htau1 := checked_tyAt_space hs1 hsv1
  have hsout : SValid Gamma (.tprod s0 s1) := .tprod hs0 hs1
  have hsvout : C.Space Gamma Psi (.tprod s0 s1) (.tprod sv0 sv1) :=
    .tprod ⟨hsout⟩ hsv0 hsv1
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType (Delta0 ∪ Delta1) Gamma (.tprodE e0 e1)
      (Basis.tof (.tprod (Basis.stdSpace s0) (Basis.stdSpace s1)))) := by
    simpa only [Basis.tof, Basis.sof, Basis.sof_stdSpace] using
      (show Nonempty (HasType (Delta0 ∪ Delta1) Gamma (.tprodE e0 e1)
        (.space (.tprod s0 s1))) from ⟨.tprodE hs0 hs1 hdisj ht0 ht1⟩)
  exact ⟨_, .space (.tprod sv0 sv1),
    .tprodE hdisj (Basis.htof_stdSpace s0) (Basis.htof_stdSpace s1)
      ht (Basis.stdSpace_valid _ hsout)
      hout (retag hv0 htau0) (retag hv1 htau1)⟩

/-! ## Linear application and standard pseudo-inverses -/

theorem checked_arm_app_linear_world (W : EvalCtx → Prop) :
    ∀ {Delta0 Delta1 : LCtx} {Gamma : NLCtx}
      {e0 e1 : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (hdisj : Finmap.Disjoint Delta0 Delta1)
      (ht0 : HasType Delta0 Gamma e0 (.space (.tprod (.dual s0) s1)))
      (ht1 : HasType Delta1 Gamma e1 (.space s0)),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W Delta0 Gamma e0 (.space (.tprod (.dual s0) s1)) →
      cMotiveHWorld W Delta1 Gamma e1 (.space s0) →
      cMotiveHWorld W (Delta0 ∪ Delta1) Gamma (.appL s0 s1 e0 e1)
        (.space s1) := by
  intro Delta0 Delta1 Gamma e0 e1 s0 s1 hs0 hs1 hdisj ht0 ht1
    ihs0 ihs1 ih0 ih1 Psi hW hP hcov hwf
  obtain ⟨hcov0, hcov1⟩ := hcov.mono_lin hdisj
  obtain ⟨sv0, hsv0⟩ := ihs0 Psi hW hP (checkedDropLin hcov)
    (ctxWF_dropLin hwf)
  obtain ⟨sv1, hsv1⟩ := ihs1 Psi hW hP (checkedDropLin hcov)
    (ctxWF_dropLin hwf)
  obtain ⟨v0, tauv0, hv0⟩ :=
    ih0 Psi hW hP hcov0 (ctxWF_union_left hwf)
  obtain ⟨v1, tauv1, hv1⟩ :=
    ih1 Psi hW hP hcov1 (ctxWF_union_right hdisj hwf)
  have hmatS : SValid Gamma (.tprod (.dual s0) s1) :=
    .tprod (.dual hs0) hs1
  have hmatV : C.Space Gamma Psi (.tprod (.dual s0) s1) (.tprod sv0 sv1) :=
    .tprod ⟨hmatS⟩ (.dual ⟨.dual hs0⟩ hsv0) hsv1
  have hmat := checked_tyAt_space hmatS hmatV
  have harg := checked_tyAt_space hs0 hsv0
  have hout := checked_tyAt_space hs1 hsv1
  have ht : Nonempty (HasType (Delta0 ∪ Delta1) Gamma
      (.appL (Basis.sof (Basis.stdSpace s0))
        (Basis.sof (Basis.stdSpace s1)) e0 e1)
      (Basis.tof (Basis.stdSpace s1))) := by
    simpa only [Basis.sof_stdSpace, Basis.htof_stdSpace] using
      (show Nonempty (HasType (Delta0 ∪ Delta1) Gamma
        (.appL s0 s1 e0 e1) (.space s1)) from
        ⟨.app_linear hs0 hs1 hdisj ht0 ht1⟩)
  have hsv0' : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s0)) sv0 := by
    simpa only [Basis.sof_stdSpace] using hsv0
  have h := C.Term.appL_lin
    (b₀ := Basis.stdSpace s0) (b₁ := Basis.stdSpace s1)
    hdisj (Basis.htof_stdSpace s1) ht (Basis.stdSpace_valid s1 hs1)
    hsv0' hout (retag hv0 hmat) (retag hv1 harg)
  exact ⟨_, .space sv1, by
    simpa only [Basis.std, Basis.sof_stdSpace] using h⟩

theorem checked_arm_app_inner_world (W : EvalCtx → Prop) :
    ∀ {Delta0 Delta1 : LCtx} {Gamma : NLCtx} {e0 e1 : Term} {s : Space}
      (hs : SValid Gamma s) (hdisj : Finmap.Disjoint Delta0 Delta1)
      (ht0 : HasType Delta0 Gamma e0 (.space (.dual s)))
      (ht1 : HasType Delta1 Gamma e1 (.space s)),
      cMotiveSWorld W Gamma s →
      cMotiveHWorld W Delta0 Gamma e0 (.space (.dual s)) →
      cMotiveHWorld W Delta1 Gamma e1 (.space s) →
      cMotiveHWorld W (Delta0 ∪ Delta1) Gamma (.appI s e0 e1)
        (.space .real) := by
  intro Delta0 Delta1 Gamma e0 e1 s hs hdisj ht0 ht1 ihs ih0 ih1
    Psi hW hP hcov hwf
  obtain ⟨hcov0, hcov1⟩ := hcov.mono_lin hdisj
  obtain ⟨sv, hsv⟩ := ihs Psi hW hP (checkedDropLin hcov)
    (ctxWF_dropLin hwf)
  obtain ⟨v0, tauv0, hv0⟩ :=
    ih0 Psi hW hP hcov0 (ctxWF_union_left hwf)
  obtain ⟨v1, tauv1, hv1⟩ :=
    ih1 Psi hW hP hcov1 (ctxWF_union_right hdisj hwf)
  have hfun := checked_tyAt_space (.dual hs) (.dual ⟨.dual hs⟩ hsv)
  have harg := checked_tyAt_space hs hsv
  have hout : C.TyAt Gamma Psi .one (.space .real) :=
    .space rfl .one .real
  have ht : Nonempty (HasType (Delta0 ∪ Delta1) Gamma
      (.appI (Basis.sof (Basis.stdSpace s)) e0 e1) (Basis.tof .one)) := by
    simpa only [Basis.sof_stdSpace, Basis.tof] using
      (show Nonempty (HasType (Delta0 ∪ Delta1) Gamma
        (.appI s e0 e1) (.space .real)) from
        ⟨.app_inner hs hdisj ht0 ht1⟩)
  have hsv' : C.Space Gamma Psi (Basis.sof (Basis.stdSpace s)) sv := by
    simpa only [Basis.sof_stdSpace] using hsv
  have h := C.Term.appI_lin (b₀ := Basis.stdSpace s)
    hdisj ht hsv' hout (retag hv0 hfun) (retag hv1 harg)
  exact ⟨_, .space .real, by
    simpa only [Basis.std, Basis.sof_stdSpace] using h⟩

theorem checked_arm_pinv_tensor_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (ht : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1))),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W ∅ Gamma e (.space (.tprod (.dual s0) s1)) →
      cMotiveHWorld W ∅ Gamma (.pinvT s0 s1 e)
        (.space (.tprod (.dual s1) s0)) := by
  intro Gamma e s0 s1 hs0 hs1 ht ihs0 ihs1 ih Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ihs0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ihs1 Psi hW hP hcov hwf
  obtain ⟨v, tauv, hv⟩ := ih Psi hW hP hcov hwf
  have hinS : SValid Gamma (.tprod (.dual s0) s1) := .tprod (.dual hs0) hs1
  have hinV : C.Space Gamma Psi (.tprod (.dual s0) s1) (.tprod sv0 sv1) :=
    .tprod ⟨hinS⟩ (.dual ⟨.dual hs0⟩ hsv0) hsv1
  have hin := checked_tyAt_space hinS hinV
  have houtS : SValid Gamma (.tprod (.dual s1) s0) := .tprod (.dual hs1) hs0
  have houtV : C.Space Gamma Psi (.tprod (.dual s1) s0) (.tprod sv1 sv0) :=
    .tprod ⟨houtS⟩ (.dual ⟨.dual hs1⟩ hsv1) hsv0
  have hout := checked_tyAt_space houtS houtV
  have hty : Nonempty (HasType ∅ Gamma
      (.pinvT (Basis.sof (Basis.stdSpace s0))
        (Basis.sof (Basis.stdSpace s1)) e)
      (Basis.tof (.tprod (.dual (Basis.stdSpace s1)) (Basis.stdSpace s0)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Gamma (.pinvT s0 s1 e)
        (.space (.tprod (.dual s1) s0))) from ⟨.pinv_tensor hs0 hs1 ht⟩)
  have hstep := C.Term.pinvT_std
    (b₀ := Basis.stdSpace s1) (b₁ := Basis.stdSpace s0)
    (Basis.isStd_stdSpace s1) (Basis.isStd_stdSpace s0)
    hty (Basis.stdSpace_valid _ houtS) hout (retag hv hin)
  exact ⟨_, .space (.tprod sv1 sv0), by
    simpa only [Basis.std, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_pinv_dual_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e : Term} {s : Space}
      (hs : SValid Gamma s) (ht : HasType ∅ Gamma e (.space (.dual s))),
      cMotiveSWorld W Gamma s →
      cMotiveHWorld W ∅ Gamma e (.space (.dual s)) →
      cMotiveHWorld W ∅ Gamma (.pinvD s e)
        (.space (.tprod (.dual .real) s)) := by
  intro Gamma e s hs ht ihs ih Psi hW hP hcov hwf
  obtain ⟨sv, hsv⟩ := ihs Psi hW hP hcov hwf
  obtain ⟨v, tauv, hv⟩ := ih Psi hW hP hcov hwf
  have hin := checked_tyAt_space (.dual hs) (.dual ⟨.dual hs⟩ hsv)
  have houtS : SValid Gamma (.tprod (.dual .real) s) :=
    .tprod (.dual .real) hs
  have houtV : C.Space Gamma Psi (.tprod (.dual .real) s) (.tprod .real sv) :=
    .tprod ⟨houtS⟩ (.dual ⟨SValid.dual SValid.real⟩ .real) hsv
  have hout := checked_tyAt_space houtS houtV
  have hty : Nonempty (HasType ∅ Gamma
      (.pinvD (Basis.sof (Basis.stdSpace s)) e)
      (Basis.tof (.tprod (.dual .one) (Basis.stdSpace s)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Gamma (.pinvD s e)
        (.space (.tprod (.dual .real) s))) from ⟨.pinv_dual hs ht⟩)
  have hstep := C.Term.pinvD_std
    (b₀ := .one) (b₁ := Basis.stdSpace s)
    rfl trivial (Basis.isStd_stdSpace s) hty
    (Basis.stdSpace_valid _ houtS) hout (retag hv hin)
  exact ⟨_, .space (.tprod .real sv), by
    simpa only [Basis.std, Basis.sof_stdSpace] using hstep⟩

/-! ## Subspace and embedding arms -/

theorem checked_arm_sub_ker_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1))),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W ∅ Gamma e (.space (.tprod (.dual s0) s1)) →
      cMotiveSubWorld W Gamma (.ker s0 s1 e) s0 := by
  intro Gamma e s0 s1 hs0 hs1 he ihs0 ihs1 ihe Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ihs0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ihs1 Psi hW hP hcov hwf
  obtain ⟨v, tauv, hev⟩ := ihe Psi hW hP hcov hwf
  obtain ⟨v', hsvb, hev'⟩ :=
    checked_ffs_witness_world hs0 hs1 hsv0 hsv1 hev
  let svk : ValSpace :=
    .ffs .kernel (.tprod sv0 sv1) (.reshapBase v' (.tprod sv0 sv1))
  have hker : C.Space Gamma Psi (.ker s0 s1 e) svk :=
    .ker ⟨.ker hs0 hs1 he⟩ (Basis.sof_stdSpace _)
      ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
      hsvb hev'
  have hsout : SValid Gamma (.tprod (.dual (.ker s0 s1 e)) s0) :=
    .tprod (.dual (.ker hs0 hs1 he)) hs0
  have hsvout : C.Space Gamma Psi (.tprod (.dual (.ker s0 s1 e)) s0)
      (.tprod svk sv0) :=
    .tprod ⟨hsout⟩ (.dual ⟨.dual (.ker hs0 hs1 he)⟩ hker) hsv0
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType ∅ Gamma (.embed (.ker s0 s1 e))
      (Basis.tof (.tprod
        (.dual (.proj (.ker s0 s1 e) (Basis.stdSpace s0) (Basis.stdSpace s1)))
        (Basis.stdSpace s0)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Gamma (.embed (.ker s0 s1 e))
        (.space (.tprod (.dual (.ker s0 s1 e)) s0))) from
        ⟨.embed (.sub_ker hs0 hs1 he)⟩)
  have hstep := C.Term.embed_ker
    (b₀ := Basis.stdSpace s0) (b₁ := Basis.stdSpace s1)
    (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    ht (Basis.stdSpace_valid _ hsout) hout
    (checked_inner_at hs0 hsv0) (checked_inner_at hs1 hsv1) hev'
  exact ⟨_, _, by
    simpa only [svk, Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_sub_coker_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1))),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W ∅ Gamma e (.space (.tprod (.dual s0) s1)) →
      cMotiveSubWorld W Gamma (.coker s0 s1 e) s0 := by
  intro Gamma e s0 s1 hs0 hs1 he ihs0 ihs1 ihe Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ihs0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ihs1 Psi hW hP hcov hwf
  obtain ⟨v, tauv, hev⟩ := ihe Psi hW hP hcov hwf
  obtain ⟨v', hsvb, hev'⟩ :=
    checked_ffs_witness_world hs0 hs1 hsv0 hsv1 hev
  let svc : ValSpace :=
    .ffs .cokernel (.tprod sv0 sv1) (.reshapBase v' (.tprod sv0 sv1))
  have hcoker : C.Space Gamma Psi (.coker s0 s1 e) svc :=
    .coker ⟨.coker hs0 hs1 he⟩ (Basis.sof_stdSpace _)
      ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
      hsvb hev'
  have hsout : SValid Gamma (.tprod (.dual (.coker s0 s1 e)) s0) :=
    .tprod (.dual (.coker hs0 hs1 he)) hs0
  have hsvout : C.Space Gamma Psi (.tprod (.dual (.coker s0 s1 e)) s0)
      (.tprod svc sv0) :=
    .tprod ⟨hsout⟩ (.dual ⟨.dual (.coker hs0 hs1 he)⟩ hcoker) hsv0
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType ∅ Gamma (.embed (.coker s0 s1 e))
      (Basis.tof (.tprod
        (.dual (.proj (.coker s0 s1 e) (Basis.stdSpace s0) (Basis.stdSpace s1)))
        (Basis.stdSpace s0)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Gamma (.embed (.coker s0 s1 e))
        (.space (.tprod (.dual (.coker s0 s1 e)) s0))) from
        ⟨.embed (.sub_coker hs0 hs1 he)⟩)
  have hstep := C.Term.embed_coker
    (b₀ := Basis.stdSpace s0) (b₁ := Basis.stdSpace s1)
    (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    ht (Basis.stdSpace_valid _ hsout) hout
    (checked_inner_at hs0 hsv0) (checked_inner_at hs1 hsv1) hev'
  exact ⟨_, _, by
    simpa only [svc, Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_sub_img_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1))),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W ∅ Gamma e (.space (.tprod (.dual s0) s1)) →
      cMotiveSubWorld W Gamma (.img s0 s1 e) s1 := by
  intro Gamma e s0 s1 hs0 hs1 he ihs0 ihs1 ihe Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ihs0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ihs1 Psi hW hP hcov hwf
  obtain ⟨v, tauv, hev⟩ := ihe Psi hW hP hcov hwf
  obtain ⟨v', hsvb, hev'⟩ :=
    checked_ffs_witness_world hs0 hs1 hsv0 hsv1 hev
  let svi : ValSpace :=
    .ffs .image (.tprod sv0 sv1) (.reshapBase v' (.tprod sv0 sv1))
  have himg : C.Space Gamma Psi (.img s0 s1 e) svi :=
    .img ⟨.img hs0 hs1 he⟩ (Basis.sof_stdSpace _)
      ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
      hsvb hev'
  have hsout : SValid Gamma (.tprod (.dual (.img s0 s1 e)) s1) :=
    .tprod (.dual (.img hs0 hs1 he)) hs1
  have hsvout : C.Space Gamma Psi (.tprod (.dual (.img s0 s1 e)) s1)
      (.tprod svi sv1) :=
    .tprod ⟨hsout⟩ (.dual ⟨.dual (.img hs0 hs1 he)⟩ himg) hsv1
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType ∅ Gamma (.embed (.img s0 s1 e))
      (Basis.tof (.tprod
        (.dual (.proj (.img s0 s1 e) (Basis.stdSpace s0) (Basis.stdSpace s1)))
        (Basis.stdSpace s1)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Gamma (.embed (.img s0 s1 e))
        (.space (.tprod (.dual (.img s0 s1 e)) s1))) from
        ⟨.embed (.sub_img hs0 hs1 he)⟩)
  have hstep := C.Term.embed_img
    (b₀ := Basis.stdSpace s0) (b₁ := Basis.stdSpace s1)
    (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    ht (Basis.stdSpace_valid _ hsout) hout
    (checked_inner_at hs0 hsv0) (checked_inner_at hs1 hsv1) hev'
  exact ⟨_, _, by
    simpa only [svi, Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_sub_coimg_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {e : Term} {s0 s1 : Space}
      (hs0 : SValid Gamma s0) (hs1 : SValid Gamma s1)
      (he : HasType ∅ Gamma e (.space (.tprod (.dual s0) s1))),
      cMotiveSWorld W Gamma s0 → cMotiveSWorld W Gamma s1 →
      cMotiveHWorld W ∅ Gamma e (.space (.tprod (.dual s0) s1)) →
      cMotiveSubWorld W Gamma (.coimg s0 s1 e) s1 := by
  intro Gamma e s0 s1 hs0 hs1 he ihs0 ihs1 ihe Psi hW hP hcov hwf
  obtain ⟨sv0, hsv0⟩ := ihs0 Psi hW hP hcov hwf
  obtain ⟨sv1, hsv1⟩ := ihs1 Psi hW hP hcov hwf
  obtain ⟨v, tauv, hev⟩ := ihe Psi hW hP hcov hwf
  obtain ⟨v', hsvb, hev'⟩ :=
    checked_ffs_witness_world hs0 hs1 hsv0 hsv1 hev
  let svi : ValSpace :=
    .ffs .coimage (.tprod sv0 sv1) (.reshapBase v' (.tprod sv0 sv1))
  have hcoimg : C.Space Gamma Psi (.coimg s0 s1 e) svi :=
    .coimg ⟨.coimg hs0 hs1 he⟩ (Basis.sof_stdSpace _)
      ⟨Basis.stdSpace s0, Basis.stdSpace s1, rfl⟩
      hsvb hev'
  have hsout : SValid Gamma (.tprod (.dual (.coimg s0 s1 e)) s1) :=
    .tprod (.dual (.coimg hs0 hs1 he)) hs1
  have hsvout : C.Space Gamma Psi (.tprod (.dual (.coimg s0 s1 e)) s1)
      (.tprod svi sv1) :=
    .tprod ⟨hsout⟩ (.dual ⟨.dual (.coimg hs0 hs1 he)⟩ hcoimg) hsv1
  have hout := checked_tyAt_space hsout hsvout
  have ht : Nonempty (HasType ∅ Gamma (.embed (.coimg s0 s1 e))
      (Basis.tof (.tprod
        (.dual (.proj (.coimg s0 s1 e) (Basis.stdSpace s0) (Basis.stdSpace s1)))
        (Basis.stdSpace s1)))) := by
    simpa only [Basis.sof_stdSpace, Basis.tof, Basis.sof] using
      (show Nonempty (HasType ∅ Gamma (.embed (.coimg s0 s1 e))
        (.space (.tprod (.dual (.coimg s0 s1 e)) s1))) from
        ⟨.embed (.sub_coimg hs0 hs1 he)⟩)
  have hstep := C.Term.embed_coimg
    (b₀ := Basis.stdSpace s0) (b₁ := Basis.stdSpace s1)
    (Basis.sof_stdSpace s0) (Basis.sof_stdSpace s1)
    ht (Basis.stdSpace_valid _ hsout) hout
    (checked_inner_at hs0 hsv0) (checked_inner_at hs1 hsv1) hev'
  exact ⟨_, _, by
    simpa only [svi, Basis.std, Basis.stdSpace, Basis.sof_stdSpace] using hstep⟩

theorem checked_arm_embed_world (W : EvalCtx → Prop) :
    ∀ {Gamma : NLCtx} {s0 s1 : Space} (hsub : SubType Gamma s0 s1),
      cMotiveSubWorld W Gamma s0 s1 →
      cMotiveHWorld W ∅ Gamma (.embed s0)
        (.space (.tprod (.dual s0) s1)) := by
  intro Gamma s0 s1 hsub ih Psi hW hP hcov hwf
  exact ih Psi hW hP hcov hwf

end RawCertifiedWorldProgressArms
end GLang
