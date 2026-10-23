import GLang.Proofs.Progress.CheckedErasure
import GLang.Proofs.Adequacy.Raw.Context.RawConsistent

namespace GLang
namespace RawCertifiedOperational

open Basis (BasisValid)

/-! ## Source-context transport along `NLCtxIncl` -/

/-- `NLCtxIncl` is exactly the pointwise inclusion used by the graded
type-context bridge. -/
theorem nlCtxIncl_asTypeCtx {Gamma Gamma' : NLCtx}
    (h : NLCtxIncl Gamma Gamma') :
    Graded.SubMap (Graded.asTypeCtx Gamma) (Graded.asTypeCtx Gamma') :=
  h

/-- Source space formation weakens under nonlinear name-and-type inclusion. -/
noncomputable def svalid_mono_nl {Gamma Gamma' : NLCtx} {s : GLang.Space}
    (h : SValid Gamma s) (hle : NLCtxIncl Gamma Gamma') :
    SValid Gamma' s :=
  Graded.svalidBwd
    (Graded.gsvalid_wk (Graded.svalidBridge h) (nlCtxIncl_asTypeCtx hle))
    (fun _ _ hx => hx)

/-- Source type formation weakens under nonlinear name-and-type inclusion. -/
noncomputable def tvalid_mono_nl {Gamma Gamma' : NLCtx} {tau : Ty} {k : Kind}
    (h : TValid Gamma tau k) (hle : NLCtxIncl Gamma Gamma') :
    TValid Gamma' tau k :=
  Graded.tvalidBwd
    (Graded.gtvalid_wk (Graded.tvalidBridge h) (nlCtxIncl_asTypeCtx hle))
    (fun _ _ hx => hx)

/-- Inserting the same binder on both sides preserves nonlinear inclusion. -/
theorem NLCtxIncl.insert_same {Gamma Gamma' : NLCtx}
    (hle : NLCtxIncl Gamma Gamma') (y : Name) (tau : Ty) :
    NLCtxIncl (Finmap.insert y tau Gamma) (Finmap.insert y tau Gamma') := by
  intro x tau' hx
  by_cases hxy : x = y
  · subst x
    simpa only [Finmap.lookup_insert] using hx
  · rw [Finmap.lookup_insert_of_ne _ hxy] at hx ⊢
    exact hle x tau' hx

/-- Source term typing weakens at a fixed linear context.  Target
disjointness is necessary: `NLCtxIncl` alone permits adding a nonlinear
binding at a name already owned by the linear context. -/
theorem hasType_mono_nl_checked
    {Delta : LCtx} {Gamma Gamma' : NLCtx} {e : Term} {tau : Ty}
    (h : Nonempty (HasType Delta Gamma e tau))
    (hle : NLCtxIncl Gamma Gamma')
    (hdisj : Graded.CtxDisj Delta Gamma') :
    Nonempty (HasType Delta Gamma' e tau) := by
  obtain ⟨h⟩ := h
  have hdisj0 : Graded.CtxDisj Delta Gamma := by
    intro x hxDelta hxGamma
    obtain ⟨tauX, hxLookup⟩ := Finmap.mem_iff.mp hxGamma
    exact hdisj x hxDelta
      (Finmap.mem_of_lookup_eq_some
        (hle x tauX hxLookup))
  refine ⟨Graded.hasTypeBridgeBwd hdisj
    (Graded.gradeWeaken (Graded.hasTypeBridge hdisj0 h) ?_)⟩
  intro x
  simp only [Graded.tr]
  cases hxDelta : Delta.lookup x with
  | some s =>
      exact ⟨rfl, Graded.GGrade.Wk.refl _⟩
  | none =>
      cases hx : Gamma.lookup x with
      | none =>
          cases hx' : Gamma'.lookup x with
          | none => trivial
          | some tau' =>
              exact (by decide : Graded.GGrade.omega ≠ Graded.GGrade.one)
      | some tau' =>
          have hx' : Gamma'.lookup x = some tau' := hle x tau' hx
          rw [hx']
          exact ⟨rfl, Graded.GGrade.Wk.refl _⟩

/-! ## Promote-node context surgery -/

/-- Erase a list of keys from a non-linear context. -/
private def eraseList (l : List Name) (m : NLCtx) : NLCtx :=
  l.foldr Finmap.erase m

private theorem lookup_eraseList (l : List Name) (m : NLCtx) (x : Name) :
    (eraseList l m).lookup x = if x ∈ l then none else m.lookup x := by
  induction l with
  | nil => simp [eraseList]
  | cons a l ih =>
      unfold eraseList at ih ⊢
      simp only [List.foldr_cons]
      by_cases hxa : x = a
      · subst x; simp [Finmap.lookup_erase]
      · rw [Finmap.lookup_erase_ne hxa, ih]
        simp only [List.mem_cons, hxa, false_or]

/-- When the enlarged world `Γt` includes the node context `lin.toNL ∪ Γ₀`, it
decomposes as `lin.toNL ∪ Γrest` with `Γrest` (the `lin`-keys erased from `Γt`)
disjoint from `lin.toNL` and still including `Γ₀`. -/
theorem promote_split_exists {lin : LCtx} {Γ₀ Γt : NLCtx}
    (hd0 : Finmap.Disjoint lin.toNL Γ₀)
    (hincl : NLCtxIncl (lin.toNL ∪ Γ₀) Γt) :
    ∃ Γrest : NLCtx, Γt = lin.toNL ∪ Γrest ∧
      Finmap.Disjoint lin.toNL Γrest ∧ NLCtxIncl Γ₀ Γrest := by
  have hbridge : ∀ x, x ∈ lin.keys.toList ↔ x ∈ lin.toNL := by
    intro x
    rw [Finset.mem_toList, Finmap.mem_keys, LCtx.mem_toNL_iff]
  refine ⟨eraseList lin.keys.toList Γt, ?_, ?_, ?_⟩
  · apply Finmap.ext_lookup
    intro x
    by_cases hx : x ∈ lin.toNL
    · rw [Finmap.lookup_union_left hx]
      obtain ⟨s, hs⟩ := Finmap.mem_iff.mp hx
      have : (lin.toNL ∪ Γ₀).lookup x = some s := by
        rw [Finmap.lookup_union_left hx]; exact hs
      rw [hincl x s this, hs]
    · rw [Finmap.lookup_union_right hx, lookup_eraseList,
        if_neg (fun h => hx ((hbridge x).mp h))]
  · intro x hx
    have : (eraseList lin.keys.toList Γt).lookup x = none := by
      rw [lookup_eraseList, if_pos ((hbridge x).mpr hx)]
    exact Finmap.lookup_eq_none.mp this
  · intro x τ hx
    have hxnl : x ∉ lin.toNL := fun hmem => hd0 x hmem (Finmap.mem_of_lookup_eq_some hx)
    have hnode : (lin.toNL ∪ Γ₀).lookup x = some τ := by
      rw [Finmap.lookup_union_right hxnl]; exact hx
    rw [lookup_eraseList, if_neg (fun h => hxnl ((hbridge x).mp h))]
    exact hincl x τ hnode

/-- Linear-context disjointness survives inserting a name fresh for `Γ`. -/
private theorem ctxDisj_insert {Δ : LCtx} {Γ : NLCtx} {y : Name} {s : GLang.Space}
    (hd : Graded.CtxDisj Δ Γ) (hy : y ∉ Γ) :
    Graded.CtxDisj (Finmap.insert y s Δ) Γ := by
  intro x hx
  rcases Finmap.mem_insert.mp hx with rfl | hxΔ
  · exact hy
  · exact hd x hxΔ

/-! ## The mutual weakening lemma (checked judgments)

`C.Term.weaken` also carries `Graded.CtxDisj Δ Γ'`, the only fact
`hasType_mono_nl_checked` needs; the other four judgments call it at `Δ = ∅`.
Only the `llam` binders (which extend `Δ`) enlarge the cofinite set, by the
target's keys.  The derivation is matched FIRST so that the `promote` case's
compound conclusion index `lin.toNL ∪ Γ''` (which names the explicit field
`lin`) is refined before the inclusion hypotheses are introduced. -/

mutual

theorem C.Space.weaken :
    ∀ {Γ Γ' : NLCtx} {Ψ : EvalCtx} {s : GLang.Space} {sv : ValSpace},
      C.Space Γ Ψ s sv → NLCtxIncl Γ Γ' → C.Space Γ' Ψ s sv
  | _, _, _, _, _, .real, _ => .real
  | _, _, _, _, _, .empty, _ => .empty
  | _, _, _, _, _, .dual hs h, hincl =>
      .dual (hs.map (svalid_mono_nl · hincl)) (C.Space.weaken h hincl)
  | _, _, _, _, _, .ker hs hb hcompat hsvb he, hincl =>
      .ker (hs.map (svalid_mono_nl · hincl)) hb hcompat (C.Space.weaken hsvb hincl)
        (C.Term.weaken he hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, .coker hs hb hcompat hsvb he, hincl =>
      .coker (hs.map (svalid_mono_nl · hincl)) hb hcompat (C.Space.weaken hsvb hincl)
        (C.Term.weaken he hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, .img hs hb hcompat hsvb he, hincl =>
      .img (hs.map (svalid_mono_nl · hincl)) hb hcompat (C.Space.weaken hsvb hincl)
        (C.Term.weaken he hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, .coimg hs hb hcompat hsvb he, hincl =>
      .coimg (hs.map (svalid_mono_nl · hincl)) hb hcompat (C.Space.weaken hsvb hincl)
        (C.Term.weaken he hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, .tprod hs h₀ h₁, hincl =>
      .tprod (hs.map (svalid_mono_nl · hincl)) (C.Space.weaken h₀ hincl)
        (C.Space.weaken h₁ hincl)
  | _, _, _, _, _, .dsum hs h₀ h₁, hincl =>
      .dsum (hs.map (svalid_mono_nl · hincl)) (C.Space.weaken h₀ hincl)
        (C.Space.weaken h₁ hincl)

theorem C.Ty.weaken :
    ∀ {Γ Γ' : NLCtx} {Ψ : EvalCtx} {τ : GLang.Ty} {τv : ValTy},
      C.Ty Γ Ψ τ τv → NLCtxIncl Γ Γ' → C.Ty Γ' Ψ τ τv
  | _, _, _, _, _, .space h, hincl => .space (C.Space.weaken h hincl)
  | _, _, _, _, _, .piTy ht hb hbv h₀ L h₁, hincl =>
      .piTy (ht.map (tvalid_mono_nl · hincl)) hb (raw_basisValid_mono hbv hincl)
        (C.Ty.weaken h₀ hincl) L
        (fun y hy => C.Ty.weaken (h₁ y hy) (NLCtxIncl.insert_same hincl y _))

theorem C.TyAt.weaken :
    ∀ {Γ Γ' : NLCtx} {Ψ : EvalCtx} {b : Basis} {τv : ValTy},
      C.TyAt Γ Ψ b τv → NLCtxIncl Γ Γ' → C.TyAt Γ' Ψ b τv
  | _, _, _, _, _, .space htof hbv hspace, hincl =>
      .space htof (raw_basisValid_mono hbv hincl) (C.Space.weaken hspace hincl)
  | _, _, _, _, _, .frame hbv hdom L hcod, hincl =>
      .frame (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hdom hincl) L
        (fun y hy => C.TyAt.weaken (hcod y hy) (NLCtxIncl.insert_same hincl y _))

theorem C.Cob.weaken :
    ∀ {Γ Γ' : NLCtx} {Ψ : EvalCtx} {b₀ : Basis} {env : ValExpr} {b₁ : Basis},
      C.Cob Γ Ψ b₀ env b₁ → NLCtxIncl Γ Γ' → C.Cob Γ' Ψ b₀ env b₁
  | _, _, _, _, _, _, .inverse hb₀ hb₁ h, hincl =>
      .inverse (raw_basisValid_mono hb₀ hincl) (raw_basisValid_mono hb₁ hincl)
        (C.Cob.weaken h hincl)
  | _, _, _, _, _, _, .trans hb₀ hb₂ h₀ h₁ hsv, hincl =>
      .trans (raw_basisValid_mono hb₀ hincl) (raw_basisValid_mono hb₂ hincl)
        (C.Cob.weaken h₀ hincl) (C.Cob.weaken h₁ hincl) (C.Space.weaken hsv hincl)
  | _, _, _, _, _, _, .tprod hbS hbT h₀ h₁, hincl =>
      .tprod (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        (C.Cob.weaken h₀ hincl) (C.Cob.weaken h₁ hincl)
  | _, _, _, _, _, _, .dsum hbS hbT h₀ h₁, hincl =>
      .dsum (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        (C.Cob.weaken h₀ hincl) (C.Cob.weaken h₁ hincl)
  | _, _, _, _, _, _, .dual_std htof hbS hbT hb₁, hincl =>
      .dual_std htof (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        (C.Cob.weaken hb₁ hincl)
  | _, _, _, _, _, _, .image hbS hbT hcoker h, hincl =>
      .image (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl) hcoker
        (C.Cob.weaken h hincl)
  | _, _, _, _, _, _, .image_svds hbS hbT hs₀ hs₁ hb₀ hb₁ hsvb he, hincl =>
      .image_svds (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        hs₀ hs₁ hb₀ hb₁ (C.Space.weaken hsvb hincl)
        (C.Term.weaken he hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, _,
      .proj_ker_coker hbS hbT hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₀' hcob hembd hproj,
      hincl =>
      .proj_ker_coker (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        hs hsofb₀ hsofb₁ (C.Space.weaken hsv₀ hincl) (C.Space.weaken hsv₁ hincl)
        (C.Space.weaken hsv hincl) (C.Space.weaken hsv' hincl) (C.Space.weaken hsv₀' hincl)
        (C.Cob.weaken hcob hincl)
        (C.Term.weaken hembd hincl (Graded.CtxDisj.empty _))
        (C.Term.weaken hproj hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, _,
      .proj_img_coimg hbS hbT hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₁' hcob hembd hproj,
      hincl =>
      .proj_img_coimg (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        hs hsofb₀ hsofb₁ (C.Space.weaken hsv₀ hincl) (C.Space.weaken hsv₁ hincl)
        (C.Space.weaken hsv hincl) (C.Space.weaken hsv' hincl) (C.Space.weaken hsv₁' hincl)
        (C.Cob.weaken hcob hincl)
        (C.Term.weaken hembd hincl (Graded.CtxDisj.empty _))
        (C.Term.weaken hproj hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, _, .terms_rref hbS hbT hbb hch hsv, hincl =>
      .terms_rref (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        (C.Cob.weaken hbb hincl) (C.Term.weaken hch hincl (Graded.CtxDisj.empty _))
        (C.Space.weaken hsv hincl)
  | _, _, _, _, _, _, .refl hb htof hsv, hincl =>
      .refl (raw_basisValid_mono hb hincl) htof (C.Space.weaken hsv hincl)
  | _, _, _, _, _, _,
      .proj_ker_coker_cod hbS hbT hs hsofb₀ hsofb₁ hsofb₁' hsv₀ hsv hsv' hembd hproj,
      hincl =>
      .proj_ker_coker_cod (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        hs hsofb₀ hsofb₁ hsofb₁' (C.Space.weaken hsv₀ hincl) (C.Space.weaken hsv hincl)
        (C.Space.weaken hsv' hincl)
        (C.Term.weaken hembd hincl (Graded.CtxDisj.empty _))
        (C.Term.weaken hproj hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, _,
      .proj_img_coimg_dom hbS hbT hs hsofb₀ hsofb₁ hsofb₀' hsv₁ hsv hsv' hembd hproj,
      hincl =>
      .proj_img_coimg_dom (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        hs hsofb₀ hsofb₁ hsofb₀' (C.Space.weaken hsv₁ hincl) (C.Space.weaken hsv hincl)
        (C.Space.weaken hsv' hincl)
        (C.Term.weaken hembd hincl (Graded.CtxDisj.empty _))
        (C.Term.weaken hproj hincl (Graded.CtxDisj.empty _))

theorem C.Term.weaken :
    ∀ {Δ : LCtx} {Γ Γ' : NLCtx} {Ψ : EvalCtx} {e : GLang.Term} {b : Basis}
      {v : ValExpr} {τv : ValTy},
      C.Term Δ Γ Ψ e b v τv → NLCtxIncl Γ Γ' → Graded.CtxDisj Δ Γ' →
      C.Term Δ Γ' Ψ e b v τv
  | _, _, _, _, _, _, _, _, .var_lin h htof hbv hτv, hincl, _ =>
      .var_lin h htof (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
  | _, _, _, _, _, _, _, _, .var_nlin h hΓ hbv hτv, hincl, _ =>
      .var_nlin h (hincl _ _ hΓ) (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
  | _, _, Γt, _, _, _, _, _, .promote lin hdΔ hdΓ hfr hle ht hbv hτv h, hincl, hdisj => by
      obtain ⟨Γrest, rfl, hdrest, hinclrest⟩ := promote_split_exists hdΓ hincl
      exact C.Term.promote lin hdΔ hdrest hfr (hle.trans hinclrest)
        (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (C.TyAt.weaken hτv hincl) h
  | _, _, _, _, _, _, _, _, .cob htof₀ htof₁ ht hbv hτv he hbb hes, hincl, hdisj =>
      .cob htof₀ htof₁ (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (C.TyAt.weaken hτv hincl) (C.Term.weaken he hincl hdisj) (C.Cob.weaken hbb hincl)
        (C.Space.weaken hes hincl)
  | _, _, _, _, _, _, _, _, .reshape_cob ht hbv hτv he, hincl, hdisj =>
      .reshape_cob (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (C.TyAt.weaken hτv hincl) (C.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .scale hdisjΔ htof ht hbv hτv he₀ he₁, hincl, hdisj =>
      .scale hdisjΔ htof (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken he₀ hincl (Graded.CtxDisj.of_union_left hdisj))
        (C.Term.weaken he₁ hincl (Graded.CtxDisj.of_union_right hdisj))
  | _, _, _, _, _, _, _, _, .add htof ht hbv hτv he₀ he₁, hincl, hdisj =>
      .add htof (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (C.TyAt.weaken hτv hincl) (C.Term.weaken he₀ hincl hdisj) (C.Term.weaken he₁ hincl hdisj)
  | _, _, _, _, _, _, _, _, .dsumE htof₀ htof₁ ht hbv hτv he₀ he₁, hincl, hdisj =>
      .dsumE htof₀ htof₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken he₀ hincl hdisj) (C.Term.weaken he₁ hincl hdisj)
  | _, _, _, _, _, _, _, _, .tprodE hdisjΔ htof₀ htof₁ ht hbv hτv he₀ he₁, hincl, hdisj =>
      .tprodE hdisjΔ htof₀ htof₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken he₀ hincl (Graded.CtxDisj.of_union_left hdisj))
        (C.Term.weaken he₁ hincl (Graded.CtxDisj.of_union_right hdisj))
  | _, _, _, _, _, _, _, _, .pinvT_std hb₀ hb₁ ht hbv hτv he, hincl, hdisj =>
      .pinvT_std hb₀ hb₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .pinvT_gpinv ht hbv hτv he hi₀ hi₁, hincl, hdisj =>
      .pinvT_gpinv (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (C.TyAt.weaken hτv hincl) (C.Term.weaken he hincl hdisj)
        (C.Term.weaken hi₀ hincl hdisj) (C.Term.weaken hi₁ hincl hdisj)
  | _, _, _, _, _, _, _, _, .pinvD_std hsofb₀ hb₀ hb₁ ht hbv hτv he, hincl, hdisj =>
      .pinvD_std hsofb₀ hb₀ hb₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .pinvD_gpinv hsofb₀ hb₀ ht hbv hτv he hi₀ hi₁, hincl, hdisj =>
      .pinvD_gpinv hsofb₀ hb₀ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken he hincl hdisj) (C.Term.weaken hi₀ hincl hdisj)
        (C.Term.weaken hi₁ hincl hdisj)
  | _, _, _, _, _, _, _, _, .inner_std hb₀ hsof ht hbv hτv hsv, hincl, hdisj =>
      .inner_std hb₀ hsof (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl) (C.Space.weaken hsv hincl)
  | _, _, _, _, _, _, _, _, .embed_ker hs₀ hs₁ ht hbv hτv hi₀ hi₁ he, hincl, hdisj =>
      .embed_ker hs₀ hs₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken hi₀ hincl hdisj) (C.Term.weaken hi₁ hincl hdisj)
        (C.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .embed_coker hs₀ hs₁ ht hbv hτv hi₀ hi₁ he, hincl, hdisj =>
      .embed_coker hs₀ hs₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken hi₀ hincl hdisj) (C.Term.weaken hi₁ hincl hdisj)
        (C.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .embed_img hs₀ hs₁ ht hbv hτv hi₀ hi₁ he, hincl, hdisj =>
      .embed_img hs₀ hs₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken hi₀ hincl hdisj) (C.Term.weaken hi₁ hincl hdisj)
        (C.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .embed_coimg hs₀ hs₁ ht hbv hτv hi₀ hi₁ he, hincl, hdisj =>
      .embed_coimg hs₀ hs₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken hi₀ hincl hdisj) (C.Term.weaken hi₁ hincl hdisj)
        (C.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .appL_lin hdisjΔ htof₁ ht hbv hsv hτv h₀ h₁, hincl, hdisj =>
      .appL_lin hdisjΔ htof₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.Space.weaken hsv hincl) (C.TyAt.weaken hτv hincl)
        (C.Term.weaken h₀ hincl (Graded.CtxDisj.of_union_left hdisj))
        (C.Term.weaken h₁ hincl (Graded.CtxDisj.of_union_right hdisj))
  | _, _, _, _, _, _, _, _, .appI_lin hdisjΔ ht hsv hτv h₀ h₁, hincl, hdisj =>
      .appI_lin hdisjΔ (hasType_mono_nl_checked ht hincl hdisj) (C.Space.weaken hsv hincl)
        (C.TyAt.weaken hτv hincl)
        (C.Term.weaken h₀ hincl (Graded.CtxDisj.of_union_left hdisj))
        (C.Term.weaken h₁ hincl (Graded.CtxDisj.of_union_right hdisj))
  | _, _, _, _, _, _, _, _, .nllam hb₀ hb₁ ht hbv hτv h₀ L he h₁, hincl, hdisj =>
      .nllam hb₀ hb₁ (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (C.TyAt.weaken hτv hincl) (C.TyAt.weaken h₀ hincl) L
        (fun y hy => C.Term.weaken (he y hy) (NLCtxIncl.insert_same hincl y _)
          (Graded.CtxDisj.empty _))
        (fun y hy => C.TyAt.weaken (h₁ y hy) (NLCtxIncl.insert_same hincl y _))
  | _, _, _, _, _, _, _, _, .appN_val ht hbv hτv h₀ h₁, hincl, hdisj =>
      .appN_val (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (C.TyAt.weaken hτv hincl) (C.Term.weaken h₀ hincl hdisj) (C.Term.weaken h₁ hincl hdisj)
  | _, _, _, _, _, _, _, _,
      .frame_reanchor htof ht hbv hτv h₀ hfn hdom L hx hcod, hincl, hdisj =>
      .frame_reanchor htof (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl) (C.TyAt.weaken h₀ hincl)
        (C.Term.weaken hfn hincl hdisj) (C.TyAt.weaken hdom hincl) L
        (fun y hy => C.Term.weaken (hx y hy) (NLCtxIncl.insert_same hincl y _)
          (Graded.CtxDisj.empty _))
        (fun y hy => C.TyAt.weaken (hcod y hy) (NLCtxIncl.insert_same hincl y _))
  | _, _, _, _, _, _, _, _, .frame_eta ht hbv hτv h₀ L he h₁, hincl, hdisj =>
      .frame_eta (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (C.TyAt.weaken hτv hincl) (C.TyAt.weaken h₀ hincl) L
        (fun y hy => C.Term.weaken (he y hy) (NLCtxIncl.insert_same hincl y _)
          (Graded.CtxDisj.empty _))
        (fun y hy => C.TyAt.weaken (h₁ y hy) (NLCtxIncl.insert_same hincl y _))
  | _, _, Γt, _, _, _, _, _, .llam_assemble htof' ht hbv hτv hsv' hsv L hfam, hincl, hdisj =>
      .llam_assemble htof' (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Space.weaken hsv' hincl) (C.Space.weaken hsv hincl) (L ∪ Γt.keys)
        (fun y hy i => C.Term.weaken (hfam y (fun hm => hy (Finset.mem_union_left _ hm)) i)
          hincl
          (ctxDisj_insert hdisj (fun hm => hy (Finset.mem_union_right _ (Finmap.mem_keys.mpr hm)))))
  | _, _, Γt, _, _, _, _, _, .llam_assemble_real htof' ht hbv hτv hsv' L hfam, hincl, hdisj =>
      .llam_assemble_real htof' (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (C.TyAt.weaken hτv hincl)
        (C.Space.weaken hsv' hincl) (L ∪ Γt.keys)
        (fun y hy i => C.Term.weaken (hfam y (fun hm => hy (Finset.mem_union_left _ hm)) i)
          hincl
          (ctxDisj_insert hdisj (fun hm => hy (Finset.mem_union_right _ (Finmap.mem_keys.mpr hm)))))
  | _, _, _, _, _, _, _, _, .zero htof ht hbv hτv hsv, hincl, hdisj =>
      .zero htof (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (C.TyAt.weaken hτv hincl) (C.Space.weaken hsv hincl)
  | _, _, _, _, _, _, _, _, .rlit r ht hτv, hincl, hdisj =>
      .rlit r (hasType_mono_nl_checked ht hincl hdisj) (C.TyAt.weaken hτv hincl)

end

/-! ### The strengthened twins -/

mutual

theorem S.Space.weaken :
    ∀ {Γ Γ' : NLCtx} {Ψ : EvalCtx} {s : GLang.Space} {sv : ValSpace},
      S.Space Γ Ψ s sv → NLCtxIncl Γ Γ' → S.Space Γ' Ψ s sv
  | _, _, _, _, _, .real, _ => .real
  | _, _, _, _, _, .empty, _ => .empty
  | _, _, _, _, _, .dual hs h, hincl =>
      .dual (hs.map (svalid_mono_nl · hincl)) (S.Space.weaken h hincl)
  | _, _, _, _, _, .ker hs hb hcompat hsvb he, hincl =>
      .ker (hs.map (svalid_mono_nl · hincl)) hb hcompat (S.Space.weaken hsvb hincl)
        (S.Term.weaken he hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, .coker hs hb hcompat hsvb he, hincl =>
      .coker (hs.map (svalid_mono_nl · hincl)) hb hcompat (S.Space.weaken hsvb hincl)
        (S.Term.weaken he hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, .img hs hb hcompat hsvb he, hincl =>
      .img (hs.map (svalid_mono_nl · hincl)) hb hcompat (S.Space.weaken hsvb hincl)
        (S.Term.weaken he hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, .coimg hs hb hcompat hsvb he, hincl =>
      .coimg (hs.map (svalid_mono_nl · hincl)) hb hcompat (S.Space.weaken hsvb hincl)
        (S.Term.weaken he hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, .tprod hs h₀ h₁, hincl =>
      .tprod (hs.map (svalid_mono_nl · hincl)) (S.Space.weaken h₀ hincl)
        (S.Space.weaken h₁ hincl)
  | _, _, _, _, _, .dsum hs h₀ h₁, hincl =>
      .dsum (hs.map (svalid_mono_nl · hincl)) (S.Space.weaken h₀ hincl)
        (S.Space.weaken h₁ hincl)

theorem S.Ty.weaken :
    ∀ {Γ Γ' : NLCtx} {Ψ : EvalCtx} {τ : GLang.Ty} {τv : ValTy},
      S.Ty Γ Ψ τ τv → NLCtxIncl Γ Γ' → S.Ty Γ' Ψ τ τv
  | _, _, _, _, _, .space h, hincl => .space (S.Space.weaken h hincl)
  | _, _, _, _, _, .piTy ht hb hbv h₀ L h₁, hincl =>
      .piTy (ht.map (tvalid_mono_nl · hincl)) hb (raw_basisValid_mono hbv hincl)
        (S.Ty.weaken h₀ hincl) L
        (fun y hy => S.Ty.weaken (h₁ y hy) (NLCtxIncl.insert_same hincl y _))

theorem S.TyAt.weaken :
    ∀ {Γ Γ' : NLCtx} {Ψ : EvalCtx} {b : Basis} {τv : ValTy},
      S.TyAt Γ Ψ b τv → NLCtxIncl Γ Γ' → S.TyAt Γ' Ψ b τv
  | _, _, _, _, _, .space htof hbv hspace, hincl =>
      .space htof (raw_basisValid_mono hbv hincl) (S.Space.weaken hspace hincl)
  | _, _, _, _, _, .frame hbv hdom L hcod, hincl =>
      .frame (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hdom hincl) L
        (fun y hy => S.TyAt.weaken (hcod y hy) (NLCtxIncl.insert_same hincl y _))

theorem S.Cob.weaken :
    ∀ {Γ Γ' : NLCtx} {Ψ : EvalCtx} {b₀ : Basis} {env : ValExpr} {b₁ : Basis},
      S.Cob Γ Ψ b₀ env b₁ → NLCtxIncl Γ Γ' → S.Cob Γ' Ψ b₀ env b₁
  | _, _, _, _, _, _, .inverse hb₀ hb₁ h, hincl =>
      .inverse (raw_basisValid_mono hb₀ hincl) (raw_basisValid_mono hb₁ hincl)
        (S.Cob.weaken h hincl)
  | _, _, _, _, _, _, .trans hb₀ hb₂ h₀ h₁ hsv, hincl =>
      .trans (raw_basisValid_mono hb₀ hincl) (raw_basisValid_mono hb₂ hincl)
        (S.Cob.weaken h₀ hincl) (S.Cob.weaken h₁ hincl) (S.Space.weaken hsv hincl)
  | _, _, _, _, _, _, .tprod hbS hbT h₀ h₁, hincl =>
      .tprod (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        (S.Cob.weaken h₀ hincl) (S.Cob.weaken h₁ hincl)
  | _, _, _, _, _, _, .dsum hbS hbT h₀ h₁, hincl =>
      .dsum (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        (S.Cob.weaken h₀ hincl) (S.Cob.weaken h₁ hincl)
  | _, _, _, _, _, _, .dual_std htof hbS hbT hb₁, hincl =>
      .dual_std htof (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        (S.Cob.weaken hb₁ hincl)
  | _, _, _, _, _, _, .image hbS hbT hcoker h, hincl =>
      .image (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl) hcoker
        (S.Cob.weaken h hincl)
  | _, _, _, _, _, _, .image_svds hbS hbT hs₀ hs₁ hb₀ hb₁ hsvb he, hincl =>
      .image_svds (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        hs₀ hs₁ hb₀ hb₁ (S.Space.weaken hsvb hincl)
        (S.Term.weaken he hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, _,
      .proj_ker_coker hbS hbT hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₀' hcob hembd hproj,
      hincl =>
      .proj_ker_coker (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        hs hsofb₀ hsofb₁ (S.Space.weaken hsv₀ hincl) (S.Space.weaken hsv₁ hincl)
        (S.Space.weaken hsv hincl) (S.Space.weaken hsv' hincl) (S.Space.weaken hsv₀' hincl)
        (S.Cob.weaken hcob hincl)
        (S.Term.weaken hembd hincl (Graded.CtxDisj.empty _))
        (S.Term.weaken hproj hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, _,
      .proj_img_coimg hbS hbT hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₁' hcob hembd hproj,
      hincl =>
      .proj_img_coimg (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        hs hsofb₀ hsofb₁ (S.Space.weaken hsv₀ hincl) (S.Space.weaken hsv₁ hincl)
        (S.Space.weaken hsv hincl) (S.Space.weaken hsv' hincl) (S.Space.weaken hsv₁' hincl)
        (S.Cob.weaken hcob hincl)
        (S.Term.weaken hembd hincl (Graded.CtxDisj.empty _))
        (S.Term.weaken hproj hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, _, .terms_rref hbS hbT hbb hch hsv, hincl =>
      .terms_rref (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        (S.Cob.weaken hbb hincl) (S.Term.weaken hch hincl (Graded.CtxDisj.empty _))
        (S.Space.weaken hsv hincl)
  | _, _, _, _, _, _, .refl hb htof hsv, hincl =>
      .refl (raw_basisValid_mono hb hincl) htof (S.Space.weaken hsv hincl)
  | _, _, _, _, _, _,
      .proj_ker_coker_cod hbS hbT hs hsofb₀ hsofb₁ hsofb₁' hsv₀ hsv hsv' hembd hproj,
      hincl =>
      .proj_ker_coker_cod (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        hs hsofb₀ hsofb₁ hsofb₁' (S.Space.weaken hsv₀ hincl) (S.Space.weaken hsv hincl)
        (S.Space.weaken hsv' hincl)
        (S.Term.weaken hembd hincl (Graded.CtxDisj.empty _))
        (S.Term.weaken hproj hincl (Graded.CtxDisj.empty _))
  | _, _, _, _, _, _,
      .proj_img_coimg_dom hbS hbT hs hsofb₀ hsofb₁ hsofb₀' hsv₁ hsv hsv' hembd hproj,
      hincl =>
      .proj_img_coimg_dom (raw_basisValid_mono hbS hincl) (raw_basisValid_mono hbT hincl)
        hs hsofb₀ hsofb₁ hsofb₀' (S.Space.weaken hsv₁ hincl) (S.Space.weaken hsv hincl)
        (S.Space.weaken hsv' hincl)
        (S.Term.weaken hembd hincl (Graded.CtxDisj.empty _))
        (S.Term.weaken hproj hincl (Graded.CtxDisj.empty _))

theorem S.Term.weaken :
    ∀ {Δ : LCtx} {Γ Γ' : NLCtx} {Ψ : EvalCtx} {e : GLang.Term} {b : Basis}
      {v : ValExpr} {τv : ValTy},
      S.Term Δ Γ Ψ e b v τv → NLCtxIncl Γ Γ' → Graded.CtxDisj Δ Γ' →
      S.Term Δ Γ' Ψ e b v τv
  | _, _, _, _, _, _, _, _, .var_lin h htof hbv hτv, hincl, _ =>
      .var_lin h htof (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
  | _, _, _, _, _, _, _, _, .var_nlin h hΓ hbv hτv, hincl, _ =>
      .var_nlin h (hincl _ _ hΓ) (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
  | _, _, Γt, _, _, _, _, _, .promote lin hdΔ hdΓ hfr hle ht hbv hτv h, hincl, hdisj => by
      obtain ⟨Γrest, rfl, hdrest, hinclrest⟩ := promote_split_exists hdΓ hincl
      exact S.Term.promote lin hdΔ hdrest hfr (hle.trans hinclrest)
        (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (S.TyAt.weaken hτv hincl) h
  | _, _, _, _, _, _, _, _, .cob htof₀ htof₁ ht hbv hτv he hbb hes, hincl, hdisj =>
      .cob htof₀ htof₁ (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (S.TyAt.weaken hτv hincl) (S.Term.weaken he hincl hdisj) (S.Cob.weaken hbb hincl)
        (S.Space.weaken hes hincl)
  | _, _, _, _, _, _, _, _, .reshape_cob ht hbv hτv he, hincl, hdisj =>
      .reshape_cob (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (S.TyAt.weaken hτv hincl) (S.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .scale hdisjΔ htof ht hbv hτv he₀ he₁, hincl, hdisj =>
      .scale hdisjΔ htof (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken he₀ hincl (Graded.CtxDisj.of_union_left hdisj))
        (S.Term.weaken he₁ hincl (Graded.CtxDisj.of_union_right hdisj))
  | _, _, _, _, _, _, _, _, .add htof ht hbv hτv he₀ he₁, hincl, hdisj =>
      .add htof (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (S.TyAt.weaken hτv hincl) (S.Term.weaken he₀ hincl hdisj) (S.Term.weaken he₁ hincl hdisj)
  | _, _, _, _, _, _, _, _, .dsumE htof₀ htof₁ ht hbv hτv he₀ he₁, hincl, hdisj =>
      .dsumE htof₀ htof₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken he₀ hincl hdisj) (S.Term.weaken he₁ hincl hdisj)
  | _, _, _, _, _, _, _, _, .tprodE hdisjΔ htof₀ htof₁ ht hbv hτv he₀ he₁, hincl, hdisj =>
      .tprodE hdisjΔ htof₀ htof₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken he₀ hincl (Graded.CtxDisj.of_union_left hdisj))
        (S.Term.weaken he₁ hincl (Graded.CtxDisj.of_union_right hdisj))
  | _, _, _, _, _, _, _, _, .pinvT_std hb₀ hb₁ ht hbv hτv he, hincl, hdisj =>
      .pinvT_std hb₀ hb₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .pinvT_gpinv ht hbv hτv he hi₀ hi₁, hincl, hdisj =>
      .pinvT_gpinv (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (S.TyAt.weaken hτv hincl) (S.Term.weaken he hincl hdisj)
        (S.Term.weaken hi₀ hincl hdisj) (S.Term.weaken hi₁ hincl hdisj)
  | _, _, _, _, _, _, _, _, .pinvD_std hsofb₀ hb₀ hb₁ ht hbv hτv he, hincl, hdisj =>
      .pinvD_std hsofb₀ hb₀ hb₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .pinvD_gpinv hsofb₀ hb₀ ht hbv hτv he hi₀ hi₁, hincl, hdisj =>
      .pinvD_gpinv hsofb₀ hb₀ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken he hincl hdisj) (S.Term.weaken hi₀ hincl hdisj)
        (S.Term.weaken hi₁ hincl hdisj)
  | _, _, _, _, _, _, _, _, .inner_std hb₀ hsof ht hbv hτv hsv, hincl, hdisj =>
      .inner_std hb₀ hsof (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl) (S.Space.weaken hsv hincl)
  | _, _, _, _, _, _, _, _, .embed_ker hs₀ hs₁ ht hbv hτv hi₀ hi₁ he, hincl, hdisj =>
      .embed_ker hs₀ hs₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken hi₀ hincl hdisj) (S.Term.weaken hi₁ hincl hdisj)
        (S.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .embed_coker hs₀ hs₁ ht hbv hτv hi₀ hi₁ he, hincl, hdisj =>
      .embed_coker hs₀ hs₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken hi₀ hincl hdisj) (S.Term.weaken hi₁ hincl hdisj)
        (S.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .embed_img hs₀ hs₁ ht hbv hτv hi₀ hi₁ he, hincl, hdisj =>
      .embed_img hs₀ hs₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken hi₀ hincl hdisj) (S.Term.weaken hi₁ hincl hdisj)
        (S.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .embed_coimg hs₀ hs₁ ht hbv hτv hi₀ hi₁ he, hincl, hdisj =>
      .embed_coimg hs₀ hs₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken hi₀ hincl hdisj) (S.Term.weaken hi₁ hincl hdisj)
        (S.Term.weaken he hincl hdisj)
  | _, _, _, _, _, _, _, _, .appL_lin hdisjΔ htof₁ ht hbv hsv hτv h₀ h₁, hincl, hdisj =>
      .appL_lin hdisjΔ htof₁ (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.Space.weaken hsv hincl) (S.TyAt.weaken hτv hincl)
        (S.Term.weaken h₀ hincl (Graded.CtxDisj.of_union_left hdisj))
        (S.Term.weaken h₁ hincl (Graded.CtxDisj.of_union_right hdisj))
  | _, _, _, _, _, _, _, _, .appI_lin hdisjΔ ht hsv hτv h₀ h₁, hincl, hdisj =>
      .appI_lin hdisjΔ (hasType_mono_nl_checked ht hincl hdisj) (S.Space.weaken hsv hincl)
        (S.TyAt.weaken hτv hincl)
        (S.Term.weaken h₀ hincl (Graded.CtxDisj.of_union_left hdisj))
        (S.Term.weaken h₁ hincl (Graded.CtxDisj.of_union_right hdisj))
  | _, _, _, _, _, _, _, _, .nllam hb₀ hb₁ ht hbv hτv h₀ L he h₁, hincl, hdisj =>
      .nllam hb₀ hb₁ (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (S.TyAt.weaken hτv hincl) (S.TyAt.weaken h₀ hincl) L
        (fun y hy => S.Term.weaken (he y hy) (NLCtxIncl.insert_same hincl y _)
          (Graded.CtxDisj.empty _))
        (fun y hy => S.TyAt.weaken (h₁ y hy) (NLCtxIncl.insert_same hincl y _))
  | _, _, _, _, _, _, _, _, .appN_val ht hbv hτv h₀ h₁, hincl, hdisj =>
      .appN_val (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (S.TyAt.weaken hτv hincl) (S.Term.weaken h₀ hincl hdisj) (S.Term.weaken h₁ hincl hdisj)
  | _, _, _, _, _, _, _, _,
      .frame_reanchor htof ht hbv hτv h₀ hfn hdom L hx hcod, hincl, hdisj =>
      .frame_reanchor htof (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl) (S.TyAt.weaken h₀ hincl)
        (S.Term.weaken hfn hincl hdisj) (S.TyAt.weaken hdom hincl) L
        (fun y hy => S.Term.weaken (hx y hy) (NLCtxIncl.insert_same hincl y _)
          (Graded.CtxDisj.empty _))
        (fun y hy => S.TyAt.weaken (hcod y hy) (NLCtxIncl.insert_same hincl y _))
  | _, _, _, _, _, _, _, _, .frame_eta ht hbv hτv h₀ L he h₁, hincl, hdisj =>
      .frame_eta (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (S.TyAt.weaken hτv hincl) (S.TyAt.weaken h₀ hincl) L
        (fun y hy => S.Term.weaken (he y hy) (NLCtxIncl.insert_same hincl y _)
          (Graded.CtxDisj.empty _))
        (fun y hy => S.TyAt.weaken (h₁ y hy) (NLCtxIncl.insert_same hincl y _))
  | _, _, Γt, _, _, _, _, _, .llam_assemble htof' ht hbv hτv hsv' hsv L hfam, hincl, hdisj =>
      .llam_assemble htof' (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Space.weaken hsv' hincl) (S.Space.weaken hsv hincl) (L ∪ Γt.keys)
        (fun y hy i => S.Term.weaken (hfam y (fun hm => hy (Finset.mem_union_left _ hm)) i)
          hincl
          (ctxDisj_insert hdisj (fun hm => hy (Finset.mem_union_right _ (Finmap.mem_keys.mpr hm)))))
  | _, _, Γt, _, _, _, _, _, .llam_assemble_real htof' ht hbv hτv hsv' L hfam, hincl, hdisj =>
      .llam_assemble_real htof' (hasType_mono_nl_checked ht hincl hdisj)
        (raw_basisValid_mono hbv hincl) (S.TyAt.weaken hτv hincl)
        (S.Space.weaken hsv' hincl) (L ∪ Γt.keys)
        (fun y hy i => S.Term.weaken (hfam y (fun hm => hy (Finset.mem_union_left _ hm)) i)
          hincl
          (ctxDisj_insert hdisj (fun hm => hy (Finset.mem_union_right _ (Finmap.mem_keys.mpr hm)))))
  | _, _, _, _, _, _, _, _, .zero htof ht hbv hτv hsv, hincl, hdisj =>
      .zero htof (hasType_mono_nl_checked ht hincl hdisj) (raw_basisValid_mono hbv hincl)
        (S.TyAt.weaken hτv hincl) (S.Space.weaken hsv hincl)
  | _, _, _, _, _, _, _, _, .rlit r ht hτv, hincl, hdisj =>
      .rlit r (hasType_mono_nl_checked ht hincl hdisj) (S.TyAt.weaken hτv hincl)

end

end RawCertifiedOperational
end GLang
