

import GLang.Proofs.Progress.Supporting.ProgressCobHelpers

set_option maxHeartbeats 1000000

namespace GLang.V2

/-! ## Small adapters -/

/-- Space realization from a (`Nonempty`-packaged) `SValid`, under the master
    induction's internal currency — the `EvalS` entry point of
    `progress_master_std` (companion of `opStep_of_hasType_std`). -/
theorem evalS_of_svalid {Ψ : EvalCtx} {Γ : NLCtx} {s : Space}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ)
    (hs : Nonempty (SValid Γ s)) : ∃ sv, ValSpace.EvalS Ψ s sv := by
  obtain ⟨hs⟩ := hs
  exact progress_master_std.1 hs Ψ hP hcov

/-- Restrict a covering to the empty linear context (the `Δ := ∅` clause is
    vacuous: `∅.lookup` never hits). Bridges `varsCovered_of`'s output to the
    `VarsCovered ∅ Γ Ψ` currency the P6 kit consumes. -/
theorem VarsCovered.drop_lin {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    (h : VarsCovered Δ Γ Ψ) : VarsCovered ∅ Γ Ψ := by
  refine ⟨fun x s hx => ?_, h.2⟩
  rw [Finmap.lookup_empty] at hx
  cases hx

/-- Re-target a P6c induction hypothesis (`Basis.std (tof b)` form) to the
    kit's `stdSpace`-at-a-named-space form. -/
theorem conv_of_ih {Ψ : EvalCtx} {b : Basis} {s : Space}
    (hsb : Basis.IsSpaceBasis b) (hsof : Basis.sof b = s)
    (ih : ∃ env, Basis.EvalBB Ψ b env (Basis.std (Basis.tof b))) :
    ∃ env, Basis.EvalBB Ψ b env (Basis.stdSpace s) := by
  subst hsof
  obtain ⟨env, h⟩ := ih
  exact ⟨env, evalBB_stdSpace_of_std_tof hsb.tof_eq h⟩

/-- The standard basis converts to ITSELF (`EvalBB.refl` packaged in the
    kit's `stdSpace` currency) — the trivial component conversion the proj
    arms feed for already-std sides. -/
theorem conv_refl_std {Ψ : EvalCtx} {s : Space}
    (hes : ∃ sv, ValSpace.EvalS Ψ s sv) :
    ∃ env, Basis.EvalBB Ψ (Basis.stdSpace s) env (Basis.stdSpace s) := by
  obtain ⟨sv, hes⟩ := hes
  exact ⟨_, .refl (Basis.htof_stdSpace s) ((Basis.sof_stdSpace s).symm ▸ hes)⟩

/-- Composed conversion-to-std of a dual-tensor basis `a* ⊗ c` (the basis of
    every linear-map witness in the proj/image arms): the `a`-side passes
    through `evalBB_dual_of_std`, then `EvalBB.tprod` (premises aligned with
    the conclusion, erratum G3-E1) composes the pair. -/
theorem conv_tprod_dual {Ψ : EvalCtx} {a c : Basis} {sa sc : Space}
    (htofa : Basis.tof a = .space (Basis.sof a))
    (hsofa : Basis.sof a = sa) (hsofc : Basis.sof c = sc)
    (ha : ∃ env, Basis.EvalBB Ψ a env (Basis.stdSpace sa))
    (hc : ∃ env, Basis.EvalBB Ψ c env (Basis.stdSpace sc)) :
    ∃ env, Basis.EvalBB Ψ (.tprod (.dual a) c) env
      (.tprod (.dual (Basis.stdSpace sa)) (Basis.stdSpace sc)) := by
  subst hsofa; subst hsofc
  obtain ⟨enva, ha⟩ := ha
  obtain ⟨envc, hc⟩ := hc
  have hd : Basis.EvalBB Ψ (.dual a) (.vtrans (.inv enva))
      (.dual (Basis.stdSpace (Basis.sof a))) :=
    evalBB_dual_of_std htofa (evalBB_std_tof_of_stdSpace htofa ha)
  exact ⟨_, .tprod hd hc⟩

/-- Realize a well-typed space term at ANY basis that converts to the
    standard basis of its space — `opStep_of_hasType_std` (the `lem:progA`
    re-entry) + the kit's closing COB move, packaged on existentials. The
    workhorse of the proj arms (witness terms at mixed bases, `lproj` at
    mixed bases). -/
theorem opStep_at_basis {Ψ : EvalCtx} {Γ : NLCtx} {e : Term} {t : Space}
    {B : Basis}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ)
    (ht : Nonempty (HasType ∅ Γ e (.space t)))
    (htof : Basis.tof B = .space (Basis.sof B))
    (hsof : Basis.sof B = t)
    (hconv : ∃ env, Basis.EvalBB Ψ B env (Basis.stdSpace t))
    (hes : ∃ sv, ValSpace.EvalS Ψ t sv) :
    ∃ v, ValExpr.OpStep Ψ e B v := by
  obtain ⟨env, hconv⟩ := hconv
  obtain ⟨sv, hes⟩ := hes
  obtain ⟨v, hv⟩ := opStep_of_hasType_std hP hcov ht
  exact opStep_cob_of_std htof hsof hv hconv hes

/-! ## The `embed_*` dispatchers (one per proj side family).

`Basis.BasisValid` has one constructor per FFS shape but the proj
CONVERSION rules quantify over the side pair (`hs : s = Ker ∨ s = CoKer`,
resp. Img/CoImg), so the embed realizations dispatch on the disjunct. -/

theorem opStep_embed_domside {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term}
    {s : Space} {c₀ c₁ : Basis} {env₀ env₁ v : ValExpr}
    (hsOr : s = Space.ker s₀ s₁ e ∨ s = Space.coker s₀ s₁ e)
    (hs₀ : Basis.sof c₀ = s₀) (hs₁ : Basis.sof c₁ = s₁)
    (hi₀ : ValExpr.OpStep Ψ (.inner s₀) (.tprod (.dual c₀) (.dual c₀)) env₀)
    (hi₁ : ValExpr.OpStep Ψ (.inner s₁) (.tprod (.dual c₁) (.dual c₁)) env₁)
    (he : ValExpr.OpStep Ψ e (.tprod (.dual c₀) c₁) v) :
    ∃ w, ValExpr.OpStep Ψ (.embed s)
      (.tprod (.dual (.proj s c₀ c₁)) c₀) w := by
  rcases hsOr with rfl | rfl
  · exact ⟨_, .embed_ker hs₀ hs₁ hi₀ hi₁ he⟩
  · exact ⟨_, .embed_coker hs₀ hs₁ hi₀ hi₁ he⟩

theorem opStep_embed_codside {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term}
    {s : Space} {c₀ c₁ : Basis} {env₀ env₁ v : ValExpr}
    (hsOr : s = Space.img s₀ s₁ e ∨ s = Space.coimg s₀ s₁ e)
    (hs₀ : Basis.sof c₀ = s₀) (hs₁ : Basis.sof c₁ = s₁)
    (hi₀ : ValExpr.OpStep Ψ (.inner s₀) (.tprod (.dual c₀) (.dual c₀)) env₀)
    (hi₁ : ValExpr.OpStep Ψ (.inner s₁) (.tprod (.dual c₁) (.dual c₁)) env₁)
    (he : ValExpr.OpStep Ψ e (.tprod (.dual c₀) c₁) v) :
    ∃ w, ValExpr.OpStep Ψ (.embed s)
      (.tprod (.dual (.proj s c₀ c₁)) c₁) w := by
  rcases hsOr with rfl | rfl
  · exact ⟨_, .embed_img hs₀ hs₁ hi₀ hi₁ he⟩
  · exact ⟨_, .embed_coimg hs₀ hs₁ hi₀ hi₁ he⟩

theorem progress_cob_proj_dom {Ψ : EvalCtx} {Γ : NLCtx}
    {s₀ s₁ : Space} {e : Term} {s : Space} {b₀ b₁ : Basis}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ)
    (hsOr : s = Space.ker s₀ s₁ e ∨ s = Space.coker s₀ s₁ e)
    (hsof₀ : Basis.sof b₀ = s₀) (hsof₁ : Basis.sof b₁ = s₁)
    (hsb₀ : Basis.IsSpaceBasis b₀) (hsb₁ : Basis.IsSpaceBasis b₁)
    (hw : Nonempty (HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))))
    (hv₀ : Nonempty (SValid Γ s₀)) (hv₁ : Nonempty (SValid Γ s₁))
    (hvS : Nonempty (SValid Γ s))
    (hsub : Nonempty (SubType Γ s s₀))
    (ihc₀ : ∃ env, Basis.EvalBB Ψ b₀ env (Basis.stdSpace s₀))
    (ihc₁ : ∃ env, Basis.EvalBB Ψ b₁ env (Basis.stdSpace s₁)) :
    ∃ env, Basis.EvalBB Ψ (.proj s b₀ b₁) env
      (.proj s (Basis.stdSpace s₀) (Basis.stdSpace s₁)) := by
  -- the std basis of `s` is the all-std projected basis (per disjunct)
  have hstd_s : Basis.stdSpace s
      = .proj s (Basis.stdSpace s₀) (Basis.stdSpace s₁) := by
    rcases hsOr with rfl | rfl <;> rfl
  -- SValid stock (unpacked) + realizations
  obtain ⟨v₀⟩ := hv₀
  obtain ⟨v₁⟩ := hv₁
  obtain ⟨vS⟩ := hvS
  obtain ⟨hsubW⟩ := hsub
  obtain ⟨sv₀, es₀⟩ := evalS_of_svalid hP hcov ⟨v₀⟩
  obtain ⟨sv₁, es₁⟩ := evalS_of_svalid hP hcov ⟨v₁⟩
  obtain ⟨svS, esS⟩ := evalS_of_svalid hP hcov ⟨vS⟩
  obtain ⟨c₀env, hc₀⟩ := ihc₀
  obtain ⟨c₁env, hc₁⟩ := ihc₁
  -- inner products at the component bases (kit) and at the std bases
  obtain ⟨i₀, hi₀⟩ := inner_at_basis hsb₀.tof_eq hsof₀ hc₀ es₀
  obtain ⟨i₁, hi₁⟩ := inner_at_basis hsb₁.tof_eq hsof₁ hc₁ es₁
  have hi₀std : ValExpr.OpStep Ψ (.inner s₀)
      (.tprod (.dual (Basis.stdSpace s₀)) (.dual (Basis.stdSpace s₀)))
      (.idelta sv₀) :=
    .inner_std (Basis.isStd_stdSpace s₀) es₀ (Basis.sof_stdSpace s₀)
  have hi₁std : ValExpr.OpStep Ψ (.inner s₁)
      (.tprod (.dual (Basis.stdSpace s₁)) (.dual (Basis.stdSpace s₁)))
      (.idelta sv₁) :=
    .inner_std (Basis.isStd_stdSpace s₁) es₁ (Basis.sof_stdSpace s₁)
  -- the witness `e` at the three bases it is needed at
  obtain ⟨wv, hwv⟩ : ∃ v, ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v :=
    opStep_at_basis hP hcov hw rfl
      (by simp only [Basis.sof]; rw [hsof₀, hsof₁])
      (conv_tprod_dual hsb₀.tof_eq hsof₀ hsof₁ ⟨_, hc₀⟩ ⟨_, hc₁⟩)
      (evalS_of_svalid hP hcov ⟨.tprod (.dual v₀) v₁⟩)
  obtain ⟨wvs, hwvs⟩ : ∃ v, ValExpr.OpStep Ψ e
      (.tprod (.dual b₀) (Basis.stdSpace s₁)) v :=
    opStep_at_basis hP hcov hw rfl
      (by simp only [Basis.sof, Basis.sof_stdSpace]; rw [hsof₀])
      (conv_tprod_dual hsb₀.tof_eq hsof₀ (Basis.sof_stdSpace s₁)
        ⟨_, hc₀⟩ (conv_refl_std ⟨_, es₁⟩))
      (evalS_of_svalid hP hcov ⟨.tprod (.dual v₀) v₁⟩)
  obtain ⟨wstd, hwstd⟩ := opStep_of_hasType_std hP hcov hw
  -- realization-at-`sof` recasts (the rules' premise shapes)
  have es₀' : ValSpace.EvalS Ψ (Basis.sof b₀) sv₀ := hsof₀.symm ▸ es₀
  have es₀std : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s₀)) sv₀ :=
    (Basis.sof_stdSpace s₀).symm ▸ es₀
  have es₁std : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s₁)) sv₁ :=
    (Basis.sof_stdSpace s₁).symm ▸ es₁
  -- ===== step 1: the ALL-STD projection witness (self-contained) =====
  obtain ⟨em3, hem3⟩ := opStep_embed_domside hsOr (Basis.sof_stdSpace s₀)
    (Basis.sof_stdSpace s₁) hi₀std hi₁std hwstd
  have hpstd := ValExpr.OpStep.pinvT_std hem3 (Basis.isStd_stdSpace s₀)
    ⟨Basis.isStd_stdSpace s₀, Basis.isStd_stdSpace s₁⟩
  -- ===== step 2 (C2): `P_s{b₀,std₁} ⟷ P_s{std₀,std₁}` =====
  obtain ⟨em2, hem2⟩ := opStep_embed_domside hsOr hsof₀
    (Basis.sof_stdSpace s₁) hi₀ hi₁std hwvs
  have hC2 : ∃ W, Basis.EvalBB Ψ (.proj s b₀ (Basis.stdSpace s₁)) W
      (.proj s (Basis.stdSpace s₀) (Basis.stdSpace s₁)) :=
    ⟨_, .proj_ker_coker hsOr hsof₀ (Basis.sof_stdSpace s₁) es₀' es₁std
      esS esS es₀std hc₀ hem2 hpstd⟩
  obtain ⟨W₂, hW₂⟩ := hC2
  -- ===== step 3 (C1): `P_s{b₀,b₁} ⟷ P_s{b₀,std₁}` =====
  -- its `hproj` lives at the MIXED basis: the std `lproj` COB'd across
  -- `b₀* ⊗ (C2's source→target conversion)`
  obtain ⟨em1, hem1⟩ := opStep_embed_domside hsOr hsof₀ hsof₁ hi₀ hi₁ hwv
  have hpmix : ∃ v, ValExpr.OpStep Ψ (Term.lproj s (Basis.sof b₀))
      (.tprod (.dual b₀) (.proj s b₀ (Basis.stdSpace s₁))) v := by
    rw [hsof₀]
    exact opStep_at_basis hP hcov ⟨HasType.lproj vS v₀ hsubW⟩ rfl
      (by simp only [Basis.sof]; rw [hsof₀])
      (conv_tprod_dual hsb₀.tof_eq hsof₀ rfl ⟨_, hc₀⟩
        (by rw [hstd_s]; exact ⟨_, hW₂⟩))
      (evalS_of_svalid hP hcov ⟨.tprod (.dual v₀) vS⟩)
  obtain ⟨pm, hpm⟩ := hpmix
  have hC1 : ∃ W, Basis.EvalBB Ψ (.proj s b₀ b₁) W
      (.proj s b₀ (Basis.stdSpace s₁)) :=
    ⟨_, .proj_ker_coker_cod hsOr hsof₀ hsof₁ (Basis.sof_stdSpace s₁)
      es₀' esS esS hem1 hpm⟩
  obtain ⟨W₁, hW₁⟩ := hC1
  exact ⟨_, .trans hW₁ hW₂ esS⟩

theorem progress_cob_proj_cod {Ψ : EvalCtx} {Γ : NLCtx}
    {s₀ s₁ : Space} {e : Term} {s : Space} {b₀ b₁ : Basis}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ)
    (hsOr : s = Space.img s₀ s₁ e ∨ s = Space.coimg s₀ s₁ e)
    (hsof₀ : Basis.sof b₀ = s₀) (hsof₁ : Basis.sof b₁ = s₁)
    (hsb₀ : Basis.IsSpaceBasis b₀) (hsb₁ : Basis.IsSpaceBasis b₁)
    (hw : Nonempty (HasType ∅ Γ e (.space (.tprod (.dual s₀) s₁))))
    (hv₀ : Nonempty (SValid Γ s₀)) (hv₁ : Nonempty (SValid Γ s₁))
    (hvS : Nonempty (SValid Γ s))
    (hsub : Nonempty (SubType Γ s s₁))
    (ihc₀ : ∃ env, Basis.EvalBB Ψ b₀ env (Basis.stdSpace s₀))
    (ihc₁ : ∃ env, Basis.EvalBB Ψ b₁ env (Basis.stdSpace s₁)) :
    ∃ env, Basis.EvalBB Ψ (.proj s b₀ b₁) env
      (.proj s (Basis.stdSpace s₀) (Basis.stdSpace s₁)) := by
  have hstd_s : Basis.stdSpace s
      = .proj s (Basis.stdSpace s₀) (Basis.stdSpace s₁) := by
    rcases hsOr with rfl | rfl <;> rfl
  obtain ⟨v₀⟩ := hv₀
  obtain ⟨v₁⟩ := hv₁
  obtain ⟨vS⟩ := hvS
  obtain ⟨hsubW⟩ := hsub
  obtain ⟨sv₀, es₀⟩ := evalS_of_svalid hP hcov ⟨v₀⟩
  obtain ⟨sv₁, es₁⟩ := evalS_of_svalid hP hcov ⟨v₁⟩
  obtain ⟨svS, esS⟩ := evalS_of_svalid hP hcov ⟨vS⟩
  obtain ⟨c₀env, hc₀⟩ := ihc₀
  obtain ⟨c₁env, hc₁⟩ := ihc₁
  obtain ⟨i₀, hi₀⟩ := inner_at_basis hsb₀.tof_eq hsof₀ hc₀ es₀
  obtain ⟨i₁, hi₁⟩ := inner_at_basis hsb₁.tof_eq hsof₁ hc₁ es₁
  have hi₀std : ValExpr.OpStep Ψ (.inner s₀)
      (.tprod (.dual (Basis.stdSpace s₀)) (.dual (Basis.stdSpace s₀)))
      (.idelta sv₀) :=
    .inner_std (Basis.isStd_stdSpace s₀) es₀ (Basis.sof_stdSpace s₀)
  have hi₁std : ValExpr.OpStep Ψ (.inner s₁)
      (.tprod (.dual (Basis.stdSpace s₁)) (.dual (Basis.stdSpace s₁)))
      (.idelta sv₁) :=
    .inner_std (Basis.isStd_stdSpace s₁) es₁ (Basis.sof_stdSpace s₁)
  -- the witness `e` at the three bases it is needed at
  obtain ⟨wv, hwv⟩ : ∃ v, ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v :=
    opStep_at_basis hP hcov hw rfl
      (by simp only [Basis.sof]; rw [hsof₀, hsof₁])
      (conv_tprod_dual hsb₀.tof_eq hsof₀ hsof₁ ⟨_, hc₀⟩ ⟨_, hc₁⟩)
      (evalS_of_svalid hP hcov ⟨.tprod (.dual v₀) v₁⟩)
  obtain ⟨wvs, hwvs⟩ : ∃ v, ValExpr.OpStep Ψ e
      (.tprod (.dual (Basis.stdSpace s₀)) b₁) v :=
    opStep_at_basis hP hcov hw rfl
      (by simp only [Basis.sof, Basis.sof_stdSpace]; rw [hsof₁])
      (conv_tprod_dual (Basis.htof_stdSpace s₀) (Basis.sof_stdSpace s₀)
        hsof₁ (conv_refl_std ⟨_, es₀⟩) ⟨_, hc₁⟩)
      (evalS_of_svalid hP hcov ⟨.tprod (.dual v₀) v₁⟩)
  obtain ⟨wstd, hwstd⟩ := opStep_of_hasType_std hP hcov hw
  have es₁' : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁ := hsof₁.symm ▸ es₁
  have es₀std : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s₀)) sv₀ :=
    (Basis.sof_stdSpace s₀).symm ▸ es₀
  have es₁std : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s₁)) sv₁ :=
    (Basis.sof_stdSpace s₁).symm ▸ es₁
  -- ===== step 1: the ALL-STD projection witness =====
  obtain ⟨em3, hem3⟩ := opStep_embed_codside hsOr (Basis.sof_stdSpace s₀)
    (Basis.sof_stdSpace s₁) hi₀std hi₁std hwstd
  have hpstd := ValExpr.OpStep.pinvT_std hem3 (Basis.isStd_stdSpace s₁)
    ⟨Basis.isStd_stdSpace s₀, Basis.isStd_stdSpace s₁⟩
  -- ===== step 2 (C2'): `P_s{std₀,b₁} ⟷ P_s{std₀,std₁}` =====
  obtain ⟨em2, hem2⟩ := opStep_embed_codside hsOr (Basis.sof_stdSpace s₀)
    hsof₁ hi₀std hi₁ hwvs
  have hC2 : ∃ W, Basis.EvalBB Ψ (.proj s (Basis.stdSpace s₀) b₁) W
      (.proj s (Basis.stdSpace s₀) (Basis.stdSpace s₁)) :=
    ⟨_, .proj_img_coimg hsOr (Basis.sof_stdSpace s₀) hsof₁ es₀std es₁'
      esS esS es₁std hc₁ hem2 hpstd⟩
  obtain ⟨W₂, hW₂⟩ := hC2
  -- ===== step 3 (C1'): `P_s{b₀,b₁} ⟷ P_s{std₀,b₁}` =====
  obtain ⟨em1, hem1⟩ := opStep_embed_codside hsOr hsof₀ hsof₁ hi₀ hi₁ hwv
  have hpmix : ∃ v, ValExpr.OpStep Ψ (Term.lproj s (Basis.sof b₁))
      (.tprod (.dual b₁) (.proj s (Basis.stdSpace s₀) b₁)) v := by
    rw [hsof₁]
    exact opStep_at_basis hP hcov ⟨HasType.lproj vS v₁ hsubW⟩ rfl
      (by simp only [Basis.sof]; rw [hsof₁])
      (conv_tprod_dual hsb₁.tof_eq hsof₁ rfl ⟨_, hc₁⟩
        (by rw [hstd_s]; exact ⟨_, hW₂⟩))
      (evalS_of_svalid hP hcov ⟨.tprod (.dual v₁) vS⟩)
  obtain ⟨pm, hpm⟩ := hpmix
  have hC1 : ∃ W, Basis.EvalBB Ψ (.proj s b₀ b₁) W
      (.proj s (Basis.stdSpace s₀) b₁) :=
    ⟨_, .proj_img_coimg_dom hsOr hsof₀ hsof₁ (Basis.sof_stdSpace s₀)
      es₁' esS esS hem1 hpm⟩
  obtain ⟨W₁, hW₁⟩ := hC1
  exact ⟨_, .trans hW₁ hW₂ esS⟩

/-- **`lem:cobProg`, std-complete master form**: under the master induction's
    internal currency, every `BasisValid` hereditary SPACE basis converts to
    the standard basis of its type. Induction on the `BasisValid` derivation;
    `Ψ`, `hP` are fixed throughout, and the covering is threaded UNCHANGED
    (the only binder-extending arm, `frame`, is vacuous under
    `Basis.IsSpaceBasis`). -/
theorem progress_cob_master {Ψ : EvalCtx} {Γ : NLCtx}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ) :
    ∀ {b : Basis}, Basis.BasisValid Γ b → Basis.IsSpaceBasis b →
      ∃ env, Basis.EvalBB Ψ b env (Basis.std (Basis.tof b)) := by
  intro b hb
  revert hcov
  induction hb with
  | empty =>
      -- `std (tof ⊥) = ⊥`: identity conversion (`EvalBB.refl`).
      exact fun _ _ => ⟨_, .refl rfl .empty⟩
  | one =>
      exact fun _ _ => ⟨_, .refl rfl .real⟩
  | @dual ε b hb htof ih =>
      intro hcov hsb
      have hsbb : Basis.IsSpaceBasis b := hsb
      obtain ⟨env, h⟩ := ih hcov hsbb
      exact ⟨_, .dual_std hsbb.tof_eq h⟩
  | @dsum ε b₀ b₁ hb₀ hb₁ htof₀ htof₁ ih₀ ih₁ =>
      intro hcov hsb
      obtain ⟨hsb₀, hsb₁⟩ := hsb
      obtain ⟨e₀, h₀⟩ := conv_of_ih hsb₀ rfl (ih₀ hcov hsb₀)
      obtain ⟨e₁, h₁⟩ := conv_of_ih hsb₁ rfl (ih₁ hcov hsb₁)
      exact ⟨_, evalBB_std_tof_of_stdSpace rfl (evalBB_dsum_to_std h₀ h₁)⟩
  | @tprod ε b₀ b₁ hb₀ hb₁ htof₀ htof₁ ih₀ ih₁ =>
      intro hcov hsb
      obtain ⟨hsb₀, hsb₁⟩ := hsb
      obtain ⟨e₀, h₀⟩ := conv_of_ih hsb₀ rfl (ih₀ hcov hsb₀)
      obtain ⟨e₁, h₁⟩ := conv_of_ih hsb₁ rfl (ih₁ hcov hsb₁)
      exact ⟨_, evalBB_std_tof_of_stdSpace rfl (evalBB_tprod_to_std h₀ h₁)⟩
  | @proj_ker ε s₀ s₁ e b₀ b₁ hb₀ hb₁ htof₀ htof₁ hw ih₀ ih₁ =>
      intro hcov hsb
      have hsof₀ : Basis.sof b₀ = s₀ := Basis.sof_eq_of_tof_eq_space htof₀
      have hsof₁ : Basis.sof b₁ = s₁ := Basis.sof_eq_of_tof_eq_space htof₁
      obtain ⟨hsb₀, hsb₁⟩ := hsb
      obtain ⟨v₀'⟩ := hb₀.sof_valid
      obtain ⟨v₁'⟩ := hb₁.sof_valid
      have v₀ : SValid ε s₀ := hsof₀ ▸ v₀'
      have v₁ : SValid ε s₁ := hsof₁ ▸ v₁'
      have hvS : Nonempty (SValid ε (.ker s₀ s₁ e)) := by
        obtain ⟨w⟩ := hw; exact ⟨.ker v₀ v₁ w⟩
      have hsub : Nonempty (SubType ε (.ker s₀ s₁ e) s₀) := by
        obtain ⟨w⟩ := hw; exact ⟨.sub_ker v₀ v₁ w⟩
      exact progress_cob_proj_dom hP hcov (Or.inl rfl) hsof₀ hsof₁ hsb₀ hsb₁
        hw ⟨v₀⟩ ⟨v₁⟩ hvS hsub
        (conv_of_ih hsb₀ hsof₀ (ih₀ hcov hsb₀))
        (conv_of_ih hsb₁ hsof₁ (ih₁ hcov hsb₁))
  | @proj_coker ε s₀ s₁ e b₀ b₁ hb₀ hb₁ htof₀ htof₁ hw ih₀ ih₁ =>
      intro hcov hsb
      have hsof₀ : Basis.sof b₀ = s₀ := Basis.sof_eq_of_tof_eq_space htof₀
      have hsof₁ : Basis.sof b₁ = s₁ := Basis.sof_eq_of_tof_eq_space htof₁
      obtain ⟨hsb₀, hsb₁⟩ := hsb
      obtain ⟨v₀'⟩ := hb₀.sof_valid
      obtain ⟨v₁'⟩ := hb₁.sof_valid
      have v₀ : SValid ε s₀ := hsof₀ ▸ v₀'
      have v₁ : SValid ε s₁ := hsof₁ ▸ v₁'
      have hvS : Nonempty (SValid ε (.coker s₀ s₁ e)) := by
        obtain ⟨w⟩ := hw; exact ⟨.coker v₀ v₁ w⟩
      have hsub : Nonempty (SubType ε (.coker s₀ s₁ e) s₀) := by
        obtain ⟨w⟩ := hw; exact ⟨.sub_coker v₀ v₁ w⟩
      exact progress_cob_proj_dom hP hcov (Or.inr rfl) hsof₀ hsof₁ hsb₀ hsb₁
        hw ⟨v₀⟩ ⟨v₁⟩ hvS hsub
        (conv_of_ih hsb₀ hsof₀ (ih₀ hcov hsb₀))
        (conv_of_ih hsb₁ hsof₁ (ih₁ hcov hsb₁))
  | @proj_img ε s₀ s₁ e b₀ b₁ hb₀ hb₁ htof₀ htof₁ hw ih₀ ih₁ =>
      intro hcov hsb
      have hsof₀ : Basis.sof b₀ = s₀ := Basis.sof_eq_of_tof_eq_space htof₀
      have hsof₁ : Basis.sof b₁ = s₁ := Basis.sof_eq_of_tof_eq_space htof₁
      obtain ⟨hsb₀, hsb₁⟩ := hsb
      obtain ⟨v₀'⟩ := hb₀.sof_valid
      obtain ⟨v₁'⟩ := hb₁.sof_valid
      have v₀ : SValid ε s₀ := hsof₀ ▸ v₀'
      have v₁ : SValid ε s₁ := hsof₁ ▸ v₁'
      have hvS : Nonempty (SValid ε (.img s₀ s₁ e)) := by
        obtain ⟨w⟩ := hw; exact ⟨.img v₀ v₁ w⟩
      have hsub : Nonempty (SubType ε (.img s₀ s₁ e) s₁) := by
        obtain ⟨w⟩ := hw; exact ⟨.sub_img v₀ v₁ w⟩
      exact progress_cob_proj_cod hP hcov (Or.inl rfl) hsof₀ hsof₁ hsb₀ hsb₁
        hw ⟨v₀⟩ ⟨v₁⟩ hvS hsub
        (conv_of_ih hsb₀ hsof₀ (ih₀ hcov hsb₀))
        (conv_of_ih hsb₁ hsof₁ (ih₁ hcov hsb₁))
  | @proj_coimg ε s₀ s₁ e b₀ b₁ hb₀ hb₁ htof₀ htof₁ hw ih₀ ih₁ =>
      intro hcov hsb
      have hsof₀ : Basis.sof b₀ = s₀ := Basis.sof_eq_of_tof_eq_space htof₀
      have hsof₁ : Basis.sof b₁ = s₁ := Basis.sof_eq_of_tof_eq_space htof₁
      obtain ⟨hsb₀, hsb₁⟩ := hsb
      obtain ⟨v₀'⟩ := hb₀.sof_valid
      obtain ⟨v₁'⟩ := hb₁.sof_valid
      have v₀ : SValid ε s₀ := hsof₀ ▸ v₀'
      have v₁ : SValid ε s₁ := hsof₁ ▸ v₁'
      have hvS : Nonempty (SValid ε (.coimg s₀ s₁ e)) := by
        obtain ⟨w⟩ := hw; exact ⟨.coimg v₀ v₁ w⟩
      have hsub : Nonempty (SubType ε (.coimg s₀ s₁ e) s₁) := by
        obtain ⟨w⟩ := hw; exact ⟨.sub_coimg v₀ v₁ w⟩
      exact progress_cob_proj_cod hP hcov (Or.inr rfl) hsof₀ hsof₁ hsb₀ hsb₁
        hw ⟨v₀⟩ ⟨v₁⟩ hvS hsub
        (conv_of_ih hsb₀ hsof₀ (ih₀ hcov hsb₀))
        (conv_of_ih hsb₁ hsof₁ (ih₁ hcov hsb₁))
  | @image ε b s₀ s₁ e hb hsof hw ih =>

      intro hcov hsb
      have hsbb : Basis.IsSpaceBasis b := hsb
      obtain ⟨cenv, hc⟩ := conv_of_ih hsbb hsof (ih hcov hsbb)
      -- step (i): `I(b) ⟷ I(P_{CoKer}{std₀,std₁})`
      have hstep1 : Basis.EvalBB Ψ (.image b) cenv
          (.image (.proj (.coker s₀ s₁ e)
            (Basis.stdSpace s₀) (Basis.stdSpace s₁))) :=
        .image ⟨s₀, s₁, e, hsof⟩ hc
      -- SValid stock from the carried `sof b = CoKer(e)`
      obtain ⟨vc⟩ := hb.sof_valid
      rw [hsof] at vc
      cases vc with
      | coker v₀ v₁ w' =>
        obtain ⟨w⟩ := hw
        obtain ⟨svI, esI⟩ := evalS_of_svalid hP hcov ⟨SValid.img v₀ v₁ w⟩
        obtain ⟨svT, esT⟩ := evalS_of_svalid hP hcov
          ⟨SValid.tprod (SValid.dual v₀) v₁⟩
        obtain ⟨wstd, hwstd⟩ := opStep_of_hasType_std hP hcov ⟨w⟩
        have hsvb : ValSpace.EvalS Ψ
            (Basis.sof (.tprod (.dual (Basis.stdSpace s₀))
              (Basis.stdSpace s₁))) svT := by
          have heq : Basis.sof (Basis.tprod (.dual (Basis.stdSpace s₀))
              (Basis.stdSpace s₁)) = .tprod (.dual s₀) s₁ := by
            simp only [Basis.sof, Basis.sof_stdSpace]
          rw [heq]; exact esT
        -- step (ii): `image_svds` at the all-std proj
        have hstep2 : ∃ V, Basis.EvalBB Ψ
            (.image (.proj (.coker s₀ s₁ e)
              (Basis.stdSpace s₀) (Basis.stdSpace s₁))) V
            (.proj (.img s₀ s₁ e)
              (Basis.stdSpace s₀) (Basis.stdSpace s₁)) :=
          ⟨_, .image_svds (Basis.sof_stdSpace s₀) (Basis.sof_stdSpace s₁)
            (Basis.isStd_stdSpace s₀) (Basis.isStd_stdSpace s₁) hwstd hsvb⟩
        obtain ⟨V, hstep2⟩ := hstep2
        have himg : Basis.sof (Basis.image b) = .img s₀ s₁ e := by
          simp only [Basis.sof, hsof]
        have esI' : ValSpace.EvalS Ψ (Basis.sof (.image b)) svI :=
          himg.symm ▸ esI
        have htr := Basis.EvalBB.trans hstep1 hstep2 esI'
        have htgt : Basis.std (Basis.tof (Basis.image b))
            = .proj (.img s₀ s₁ e)
              (Basis.stdSpace s₀) (Basis.stdSpace s₁) := by
          rw [Basis.std_tof_eq_stdSpace rfl, himg]
          rfl
        rw [htgt]
        exact ⟨_, htr⟩
  | @terms ε s es b hb htof hsv hesAll hvalidNonempty ih =>

      intro hcov hsb
      have hsof : Basis.sof b = s := Basis.sof_eq_of_tof_eq_space htof
      obtain ⟨hne, hsbb⟩ := hsb
      obtain ⟨e₀, es', rfl⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨cenv, hc⟩ := conv_of_ih hsbb hsof (ih hcov hsbb)
      obtain ⟨sv, esS⟩ := evalS_of_svalid hP hcov hsv
      obtain ⟨chv, hch⟩ := opStep_dsumChain_at_chain hP hcov hsbb.tof_eq hsof
        hc esS hsv hesAll
      have hWsv : ValSpace.EvalS Ψ (Basis.sof (Basis.stdSpace s)) sv :=
        (Basis.sof_stdSpace s).symm ▸ esS
      have hW : ∃ R, Basis.EvalBB Ψ (Basis.stdSpace s) R
          (.terms (Basis.sof b) (e₀ :: es') b) :=
        ⟨_, .terms_rref (.inverse hc) hch hWsv⟩
      obtain ⟨R, hW⟩ := hW
      rw [hsof] at hW
      have htgt : Basis.std (Basis.tof (Basis.terms s (e₀ :: es') b))
          = Basis.stdSpace s := by
        rw [Basis.std_tof_eq_stdSpace rfl]
        show Basis.stdSpace (Basis.sof b) = Basis.stdSpace s
        rw [hsof]
      rw [htgt]
      exact ⟨_, .inverse hW⟩
  | frame L hb₀ hbody ih₀ ihbody =>
      -- Vacuous: `IsSpaceBasis` identifies a top-level space basis, not a frame.
      exact fun _ hsb => absurd hsb Basis.isSpaceBasis_frame

/-! ## The boundary theorem (closes the `ValueProgress.lean` stub). -/

theorem progress_cob_std
    {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {b : Basis} {s : Space}
    (hwfΔΓ : CtxWF' Δ Γ) (hwfΨ : EvalCtxValid Ψ) (hwflc : EvalCtxLc Ψ)
    (hanch : EvalCtxLamAnchored Ψ) (hΓΨ : TypingImplyEval Δ Γ Ψ)
    (hstd : StdComplete Ψ)
    (hb : Basis.BasisValid Γ b) (hsb : Basis.IsSpaceBasis b)
    (htof : Basis.tof b = .space s) :
    ∃ env, Basis.EvalBB Ψ b env (Basis.std (Basis.tof b)) :=
  progress_cob_master (pCarrier_of hwfΨ hwflc hanch hstd)
    (varsCovered_of hΓΨ).drop_lin hb hsb

end GLang.V2
