import GLang.Proofs.Adequacy.Foundations.Foundations

namespace GLang

open Basis (BasisValid)

/-! ## Inversions of the live judgments used by the erasure -/

/-- `EvalT` at a space value type comes from `EvalS` on a space type. -/
theorem ValTy.EvalT.space_inv {Ψ : EvalCtx} {τ : GLang.Ty} {sv : ValSpace}
    (h : ValTy.EvalT Ψ τ (.space sv)) : ∃ s, τ = .space s ∧ ValSpace.EvalS Ψ s sv := by
  cases h with
  | space hs => exact ⟨_, rfl, hs⟩

/-- `EvalT Ψ (tof b) (.space sv)` realizes `sof b` (the `hsv` premise of `OpStep.appL_lin`). -/
theorem ValSpace.EvalS.sof_of_evalT_tof {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
    (h : ValTy.EvalT Ψ (Basis.tof b) (.space sv)) : ValSpace.EvalS Ψ (Basis.sof b) sv := by
  obtain ⟨s, hs, hsv⟩ := ValTy.EvalT.space_inv h
  rw [Basis.sof_of_tof_space hs]; exact hsv

/-- `EvalS` on a dual space is `EvalS` on the space (the dual forgets its star). -/
theorem ValSpace.EvalS.dual_inv {Ψ : EvalCtx} {s : GLang.Space} {sv : ValSpace}
    (h : ValSpace.EvalS Ψ (.dual s) sv) : ValSpace.EvalS Ψ s sv := by
  cases h with
  | dual h => exact h

structure ErasureErrataArms : Prop where
  /-- E1+E2 (`S.Term.embed_ker`): `GSVDUI`, transposed. -/
  embed_ker : ∀ {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : GLang.Term} {v env₀ env₁ : ValExpr}
      {s₀ s₁ : GLang.Space},
    Basis.sof b₀ = s₀ → Basis.sof b₁ = s₁ →
    ValExpr.OpStep Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀ →
    ValExpr.OpStep Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁ →
    ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v →
    ValExpr.OpStep Ψ (.embed (Space.ker s₀ s₁ e))
      (.tprod (.dual (.proj (.ker s₀ s₁ e) b₀ b₁)) b₀) (.vtrans (.gsvdUI v env₀ env₁))
  /-- E1+E2 (`S.Term.embed_coker`): `GSVDU`, transposed. -/
  embed_coker : ∀ {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : GLang.Term} {v env₀ env₁ : ValExpr}
      {s₀ s₁ : GLang.Space},
    Basis.sof b₀ = s₀ → Basis.sof b₁ = s₁ →
    ValExpr.OpStep Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀ →
    ValExpr.OpStep Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁ →
    ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v →
    ValExpr.OpStep Ψ (.embed (Space.coker s₀ s₁ e))
      (.tprod (.dual (.proj (.coker s₀ s₁ e) b₀ b₁)) b₀) (.vtrans (.gsvdU v env₀ env₁))
  /-- E2 (`S.Term.embed_img`): `GSVDV`, transposed. -/
  embed_img : ∀ {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : GLang.Term} {v env₀ env₁ : ValExpr}
      {s₀ s₁ : GLang.Space},
    Basis.sof b₀ = s₀ → Basis.sof b₁ = s₁ →
    ValExpr.OpStep Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀ →
    ValExpr.OpStep Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁ →
    ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v →
    ValExpr.OpStep Ψ (.embed (Space.img s₀ s₁ e))
      (.tprod (.dual (.proj (.img s₀ s₁ e) b₀ b₁)) b₁) (.vtrans (.gsvdV v env₀ env₁))
  /-- E2 (`S.Term.embed_coimg`): `GSVDVI`, transposed. -/
  embed_coimg : ∀ {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : GLang.Term} {v env₀ env₁ : ValExpr}
      {s₀ s₁ : GLang.Space},
    Basis.sof b₀ = s₀ → Basis.sof b₁ = s₁ →
    ValExpr.OpStep Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀ →
    ValExpr.OpStep Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁ →
    ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v →
    ValExpr.OpStep Ψ (.embed (Space.coimg s₀ s₁ e))
      (.tprod (.dual (.proj (.coimg s₀ s₁ e) b₀ b₁)) b₁) (.vtrans (.gsvdVI v env₀ env₁))
  /-- E3 (`S.Term.pinvT_gpinv`): Gram slots domain-first, `.gpinv v env₁ env₀`. -/
  pinvT_gpinv : ∀ {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : GLang.Term} {v env₀ env₁ : ValExpr},
    ValExpr.OpStep Ψ e (.tprod (.dual b₁) b₀) v →
    ValExpr.OpStep Ψ (.inner (Basis.sof b₀)) (.tprod (.dual b₀) (.dual b₀)) env₀ →
    ValExpr.OpStep Ψ (.inner (Basis.sof b₁)) (.tprod (.dual b₁) (.dual b₁)) env₁ →
    ValExpr.OpStep Ψ (.pinvT (Basis.sof b₁) (Basis.sof b₀) e)
      (.tprod (.dual b₀) b₁) (.gpinv v env₁ env₀)
  /-- E7 (`S.Term.pinvD_std`): the dual operand is reshaped to the tprod `sv₁ ⊗ ℝ`. The
      realization `sv₁` of `sof b₁` is supplied (erased from the operand's `hτv`). -/
  pinvD_std : ∀ {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : GLang.Term} {v : ValExpr} {sv₁ : ValSpace},
    Basis.sof b₀ = .real → Basis.isStd b₀ → Basis.isStd b₁ →
    ValExpr.OpStep Ψ e (.dual b₁) v →
    ValSpace.EvalS Ψ (Basis.sof b₁) sv₁ →
    ValExpr.OpStep Ψ (.pinvD (Basis.sof b₁) e) (.tprod (.dual b₀) b₁)
      (.pinv (.reshap v (.space (.tprod sv₁ .real)) (.space sv₁)))
  /-- E3+E4 (`S.Term.pinvD_gpinv`): reshaped operand, domain-first Gram slots. -/
  pinvD_gpinv : ∀ {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : GLang.Term} {v env₀ env₁ : ValExpr}
      {sv₁ : ValSpace},
    Basis.sof b₀ = .real →
    Basis.isStd b₀ →
    ValExpr.OpStep Ψ e (.dual b₁) v →
    ValSpace.EvalS Ψ (Basis.sof b₁) sv₁ →
    ValExpr.OpStep Ψ (.inner (Basis.sof b₀)) (.tprod (.dual b₀) (.dual b₀)) env₀ →
    ValExpr.OpStep Ψ (.inner (Basis.sof b₁)) (.tprod (.dual b₁) (.dual b₁)) env₁ →
    ValExpr.OpStep Ψ (.pinvD (Basis.sof b₁) e) (.tprod (.dual b₀) b₁)
      (.gpinv (.reshap v (.space (.tprod sv₁ .real)) (.space sv₁)) env₁ env₀)
  /-- E7 (`S.Term.appI_lin`): the functional is reshaped to `sv ⊗ ℝ`. -/
  appI_lin : ∀ {Ψ : EvalCtx} {b₀ : Basis} {n₀ n₁ : GLang.Term} {env₀ env₁ : ValExpr}
      {sv : ValSpace},
    ValExpr.OpStep Ψ n₀ (.dual b₀) env₀ →
    ValSpace.EvalS Ψ (Basis.sof b₀) sv →
    ValExpr.OpStep Ψ n₁ b₀ env₁ →
    ValExpr.OpStep Ψ (.appI (Basis.sof b₀) n₀ n₁) .one
      (.ttv sv (.reshap env₀ (.space (.tprod sv .real)) (.space sv)) env₁)
  /-- COB-`tprod` (G3-E1, `S.Cob.tprod`): premises aligned with `dsum`. -/
  cob_tprod : ∀ {Ψ : EvalCtx} {b₀ b₁ b₀' b₁' : Basis} {env₀ env₁ : ValExpr},
    Basis.EvalBB Ψ b₀' env₀ b₀ →
    Basis.EvalBB Ψ b₁' env₁ b₁ →
    Basis.EvalBB Ψ (.tprod b₀' b₁') (.vkrn env₀ env₁) (.tprod b₀ b₁)

theorem ErasureErrataArms.holds : ErasureErrataArms where
  embed_ker := fun hs₀ hs₁ hi₀ hi₁ he => .embed_ker hs₀ hs₁ hi₀ hi₁ he
  embed_coker := fun hs₀ hs₁ hi₀ hi₁ he => .embed_coker hs₀ hs₁ hi₀ hi₁ he
  embed_img := fun hs₀ hs₁ hi₀ hi₁ he => .embed_img hs₀ hs₁ hi₀ hi₁ he
  embed_coimg := fun hs₀ hs₁ hi₀ hi₁ he => .embed_coimg hs₀ hs₁ hi₀ hi₁ he
  pinvT_gpinv := fun he hi₀ hi₁ => .pinvT_gpinv he hi₀ hi₁
  pinvD_std := fun hsofb₀ hb₀ hb₁ he hsv₁ => .pinvD_std he hsofb₀ hb₀ hb₁ hsv₁
  pinvD_gpinv := fun hsofb₀ hb₀ he hsv₁ hi₀ hi₁ =>
    .pinvD_gpinv he hsofb₀ hb₀ hi₀ hi₁ hsv₁
  appI_lin := fun h₀ hsv h₁ => .appI_lin h₀ hsv h₁
  cob_tprod := fun h₀ h₁ => .tprod h₀ h₁

/-! ## The erasure -/

mutual

/-- Erasure `S.Space → ValSpace.EvalS` (rule for rule). -/
theorem S.Space.erase (E : ErasureErrataArms) :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {s : GLang.Space} {sv : ValSpace},
      S.Space Γ Ψ s sv → ValSpace.EvalS Ψ s sv
  | _, _, _, _, .real => .real
  | _, _, _, _, .empty => .empty
  | _, _, _, _, .dual _ h => .dual (S.Space.erase E h)
  | _, _, _, _, .ker _ hb hcompat hsvb he =>
      .ker (S.Term.erase E he).1 hb hcompat (S.Space.erase E hsvb)
  | _, _, _, _, .coker _ hb hcompat hsvb he =>
      .coker (S.Term.erase E he).1 hb hcompat (S.Space.erase E hsvb)
  | _, _, _, _, .img _ hb hcompat hsvb he =>
      .img (S.Term.erase E he).1 hb hcompat (S.Space.erase E hsvb)
  | _, _, _, _, .coimg _ hb hcompat hsvb he =>
      .coimg (S.Term.erase E he).1 hb hcompat (S.Space.erase E hsvb)
  | _, _, _, _, .tprod _ h₀ h₁ => .tprod (S.Space.erase E h₀) (S.Space.erase E h₁)
  | _, _, _, _, .dsum _ h₀ h₁ => .dsum (S.Space.erase E h₀) (S.Space.erase E h₁)

/-- Erasure `S.Ty → ValTy.EvalT` (rule for rule; the Π rule keeps its cofinite set). -/
theorem S.Ty.erase (E : ErasureErrataArms) :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {τ : GLang.Ty} {τv : ValTy},
      S.Ty Γ Ψ τ τv → ValTy.EvalT Ψ τ τv
  | _, _, _, _, .space h => .space (S.Space.erase E h)
  | _, _, _, _, .piTy _ hb _ h₀ L h₁ =>
      .piTy (S.Ty.erase E h₀) hb L (fun y hy => S.Ty.erase E (h₁ y hy))

/-- Erasure of the exact-basis type certificate.  The frame arm retains its
    recorded domain basis as the binder chosen by `EvalT.piTy`; the codomain
    basis is forgotten only after its recursively aligned proof is erased. -/
theorem S.TyAt.erase (E : ErasureErrataArms) :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {b : Basis} {τv : ValTy},
      S.TyAt Γ Ψ b τv → ValTy.EvalT Ψ (Basis.tof b) τv
  | _, _, _, _, .space htof _ hspace => by
      rw [htof]
      exact .space (S.Space.erase E hspace)
  | _, _, _, _, .frame _ hdom L hcod => by
      simp only [Basis.tof]
      exact .piTy (S.TyAt.erase E hdom) rfl L (fun y hy => by
        simpa only [Basis.openVar, Basis.tof_openRec] using
          S.TyAt.erase E (hcod y hy))

/-- Erasure `S.Cob → Basis.EvalBB` (rule for rule; `tprod` through `E.cob_tprod`). -/
theorem S.Cob.erase (E : ErasureErrataArms) :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {b₀ b₁ : Basis} {env : ValExpr},
      S.Cob Γ Ψ b₀ env b₁ → Basis.EvalBB Ψ b₀ env b₁
  | _, _, _, _, _, .inverse _ _ h => .inverse (S.Cob.erase E h)
  | _, _, _, _, _, .trans _ _ h₀ h₁ hsv =>
      .trans (S.Cob.erase E h₀) (S.Cob.erase E h₁) (S.Space.erase E hsv)
  | _, _, _, _, _, .tprod _ _ h₀ h₁ => E.cob_tprod (S.Cob.erase E h₀) (S.Cob.erase E h₁)
  | _, _, _, _, _, .dsum _ _ h₀ h₁ => .dsum (S.Cob.erase E h₀) (S.Cob.erase E h₁)
  | _, _, _, _, _, .dual_std htof _ _ hb₁ => .dual_std htof (S.Cob.erase E hb₁)
  | _, _, _, _, _, .image _ _ hcoker h => .image hcoker (S.Cob.erase E h)
  | _, _, _, _, _, .image_svds _ _ hs₀ hs₁ hb₀ hb₁ hsvb he =>
      .image_svds hs₀ hs₁ hb₀ hb₁ (S.Term.erase E he).1 (S.Space.erase E hsvb)
  | _, _, _, _, _, .proj_ker_coker _ _ hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₀' hcob hembd
      hproj =>
      .proj_ker_coker hs hsofb₀ hsofb₁ (S.Space.erase E hsv₀) (S.Space.erase E hsv₁)
        (S.Space.erase E hsv) (S.Space.erase E hsv') (S.Space.erase E hsv₀')
        (S.Cob.erase E hcob) (S.Term.erase E hembd).1 (S.Term.erase E hproj).1
  | _, _, _, _, _, .proj_img_coimg _ _ hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₁' hcob hembd
      hproj =>
      .proj_img_coimg hs hsofb₀ hsofb₁ (S.Space.erase E hsv₀) (S.Space.erase E hsv₁)
        (S.Space.erase E hsv) (S.Space.erase E hsv') (S.Space.erase E hsv₁')
        (S.Cob.erase E hcob) (S.Term.erase E hembd).1 (S.Term.erase E hproj).1
  | _, _, _, _, _, .terms_rref _ _ hbb hch hsv =>
      .terms_rref (S.Cob.erase E hbb) (S.Term.erase E hch).1 (S.Space.erase E hsv)
  | _, _, _, _, _, .refl _ htof hsv => .refl htof (S.Space.erase E hsv)
  | _, _, _, _, _, .proj_ker_coker_cod _ _ hs hsofb₀ hsofb₁ hsofb₁' hsv₀ hsv hsv' hembd hproj =>
      .proj_ker_coker_cod hs hsofb₀ hsofb₁ hsofb₁' (S.Space.erase E hsv₀)
        (S.Space.erase E hsv) (S.Space.erase E hsv')
        (S.Term.erase E hembd).1 (S.Term.erase E hproj).1
  | _, _, _, _, _, .proj_img_coimg_dom _ _ hs hsofb₀ hsofb₁ hsofb₀' hsv₁ hsv hsv' hembd hproj =>
      .proj_img_coimg_dom hs hsofb₀ hsofb₁ hsofb₀' (S.Space.erase E hsv₁)
        (S.Space.erase E hsv) (S.Space.erase E hsv')
        (S.Term.erase E hembd).1 (S.Term.erase E hproj).1

theorem S.Term.erase (E : ErasureErrataArms) :
    ∀ {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {e : GLang.Term} {b : Basis} {v : ValExpr}
      {τv : ValTy},
      S.Term Δ Γ Ψ e b v τv → ValExpr.OpStep Ψ e b v ∧ ValTy.EvalT Ψ (Basis.tof b) τv
  | _, _, _, _, _, _, _, .var_lin h _ _ hτv => ⟨.var h, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .var_nlin h _ _ hτv => ⟨.var h, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .promote _ _ _ _ _ _ _ hτv h =>
      ⟨(S.Term.erase E h).1, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .cob htof₀ htof₁ _ _ hτv he hbb hes =>
      ⟨.cob htof₀ htof₁ (S.Term.erase E he).1 (S.Cob.erase E hbb) (S.Space.erase E hes),
       S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .reshape_cob _ _ hτv he =>
      ⟨.reshape_cob (S.Term.erase E he).1 (S.Term.erase E he).2 (S.TyAt.erase E hτv),
       S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .scale _ _ _ _ hτv he₀ he₁ =>
      ⟨.scale (S.Term.erase E he₀).1 (S.Term.erase E he₁).1, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .add htof _ _ hτv he₀ he₁ =>
      let hτ := S.TyAt.erase E hτv
      ⟨.add htof (ValSpace.EvalS.sof_of_evalT_tof hτ)
        (S.Term.erase E he₀).1 (S.Term.erase E he₁).1, hτ⟩
  | _, _, _, _, _, _, _, .dsumE htof₀ htof₁ _ _ hτv he₀ he₁ =>
      ⟨.dsumE (S.Term.erase E he₀).1 (S.Term.erase E he₁).1 htof₀ htof₁, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .tprodE _ htof₀ htof₁ _ _ hτv he₀ he₁ =>
      ⟨.tprodE (S.Term.erase E he₀).1 (S.Term.erase E he₁).1 htof₀ htof₁, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .pinvT_std hb₀ hb₁ _ _ hτv he =>
      ⟨.pinvT_std (S.Term.erase E he).1 hb₀ hb₁, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .pinvT_gpinv _ _ hτv he hi₀ hi₁ =>
      ⟨E.pinvT_gpinv (S.Term.erase E he).1 (S.Term.erase E hi₀).1 (S.Term.erase E hi₁).1,
       S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .pinvD_std hsofb₀ hb₀ hb₁ _ _ hτv he =>
      ⟨E.pinvD_std hsofb₀ hb₀ hb₁ (S.Term.erase E he).1
        (ValSpace.EvalS.dual_inv (ValSpace.EvalS.sof_of_evalT_tof (S.Term.erase E he).2)),
       S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .pinvD_gpinv hsofb₀ hb₀ _ _ hτv he hi₀ hi₁ =>
      ⟨E.pinvD_gpinv hsofb₀ hb₀ (S.Term.erase E he).1
        (ValSpace.EvalS.dual_inv (ValSpace.EvalS.sof_of_evalT_tof (S.Term.erase E he).2))
        (S.Term.erase E hi₀).1 (S.Term.erase E hi₁).1,
       S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .inner_std hb₀ hsof _ _ hτv hsv =>
      ⟨.inner_std hb₀ (S.Space.erase E hsv) hsof, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .embed_ker hs₀ hs₁ _ _ hτv hi₀ hi₁ he =>
      ⟨E.embed_ker hs₀ hs₁ (S.Term.erase E hi₀).1 (S.Term.erase E hi₁).1
        (S.Term.erase E he).1, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .embed_coker hs₀ hs₁ _ _ hτv hi₀ hi₁ he =>
      ⟨E.embed_coker hs₀ hs₁ (S.Term.erase E hi₀).1 (S.Term.erase E hi₁).1
        (S.Term.erase E he).1, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .embed_img hs₀ hs₁ _ _ hτv hi₀ hi₁ he =>
      ⟨E.embed_img hs₀ hs₁ (S.Term.erase E hi₀).1 (S.Term.erase E hi₁).1
        (S.Term.erase E he).1, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .embed_coimg hs₀ hs₁ _ _ hτv hi₀ hi₁ he =>
      ⟨E.embed_coimg hs₀ hs₁ (S.Term.erase E hi₀).1 (S.Term.erase E hi₁).1
        (S.Term.erase E he).1, S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .appL_lin _ htof₁ _ _ hsv hτv h₀ h₁ =>
      ⟨.appL_lin (S.Term.erase E h₀).1
        (S.Space.erase E hsv) (S.Term.erase E h₁).1
        (ValSpace.EvalS.sof_of_evalT_tof (S.TyAt.erase E hτv)) htof₁,
       S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .appI_lin _ _ hsv hτv h₀ h₁ =>
      ⟨E.appI_lin (S.Term.erase E h₀).1
        (S.Space.erase E hsv) (S.Term.erase E h₁).1,
       S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .nllam hb₀ hb₁ _ _ hτv h₀ L he h₁ =>
      ⟨.nllam hb₀ hb₁ (by simpa only [hb₀] using S.TyAt.erase E h₀) L
        (fun y hy => (S.Term.erase E (he y hy)).1)
        (fun y hy => by
          simpa only [Basis.openVar, Basis.tof_openRec, hb₁] using S.TyAt.erase E (h₁ y hy)),
        S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .appN_val _ _ hτv h₀ h₁ =>
      ⟨.appN_val (S.Term.erase E h₀).1 (S.Term.erase E h₁).1 (S.TyAt.erase E hτv),
       S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .frame_reanchor htof _ _ hτv h₀ hfn hdom L hx hcod =>
      ⟨.frame_reanchor (S.TyAt.erase E h₀) htof (S.Term.erase E hfn).1
        (S.TyAt.erase E hdom) L
        (fun y hy => (S.Term.erase E (hx y hy)).1) (fun y hy => by
          simpa only [Basis.openVar, Basis.tof_openRec] using S.TyAt.erase E (hcod y hy)),
       S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .frame_eta _ _ hτv h₀ L he h₁ =>
      ⟨.frame_eta (S.TyAt.erase E h₀) L (fun y hy => (S.Term.erase E (he y hy)).1)
        (fun y hy => by
          simpa only [Basis.openVar, Basis.tof_openRec] using S.TyAt.erase E (h₁ y hy)),
        S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .llam_assemble htof' _ _ hτv hsv' hsv L hfam =>
      ⟨.llam_assemble htof' (S.Space.erase E hsv') (S.Space.erase E hsv) L
        (fun y hy i => (S.Term.erase E (hfam y hy i)).1), S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .llam_assemble_real htof' _ _ hτv hsv' L hfam =>
      ⟨.llam_assemble_real htof' (S.Space.erase E hsv') L
        (fun y hy i => (S.Term.erase E (hfam y hy i)).1), S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .zero htof _ _ hτv hsv =>
      ⟨.zero htof (S.Space.erase E hsv), S.TyAt.erase E hτv⟩
  | _, _, _, _, _, _, _, .rlit r _ hτv => ⟨.rlit r, S.TyAt.erase E hτv⟩

end

/-! ## The unconditional erasure theorems (`ErasureErrataArms.holds`) -/

theorem S.Space.toEvalS {Γ : NLCtx} {Ψ : EvalCtx} {s : GLang.Space} {sv : ValSpace}
    (h : S.Space Γ Ψ s sv) : ValSpace.EvalS Ψ s sv :=
  S.Space.erase ErasureErrataArms.holds h

/-- Erasure `S.Ty → ValTy.EvalT` (unconditional). -/
theorem S.Ty.toEvalT {Γ : NLCtx} {Ψ : EvalCtx} {τ : GLang.Ty} {τv : ValTy}
    (h : S.Ty Γ Ψ τ τv) : ValTy.EvalT Ψ τ τv :=
  S.Ty.erase ErasureErrataArms.holds h

/-- Erase an exact-basis strengthened type certificate while retaining its
    source type as `tof b`. -/
theorem S.TyAt.toEvalT {Γ : NLCtx} {Ψ : EvalCtx} {b : Basis} {τv : ValTy}
    (h : S.TyAt Γ Ψ b τv) : ValTy.EvalT Ψ (Basis.tof b) τv :=
  S.TyAt.erase ErasureErrataArms.holds h

/-- Erasure `S.Cob → Basis.EvalBB` (unconditional). -/
theorem S.Cob.toEvalBB {Γ : NLCtx} {Ψ : EvalCtx} {b₀ b₁ : Basis} {env : ValExpr}
    (h : S.Cob Γ Ψ b₀ env b₁) : Basis.EvalBB Ψ b₀ env b₁ :=
  S.Cob.erase ErasureErrataArms.holds h

/-- Erasure `S.Term → ValExpr.OpStep` (unconditional; the first conjunct of `S.Term.erase`). -/
theorem S.Term.toOpStep {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {τv : ValTy} (h : S.Term Δ Γ Ψ e b v τv) :
    ValExpr.OpStep Ψ e b v :=
  (S.Term.erase ErasureErrataArms.holds h).1

/-- Erasure of the produced type's realization: `S.Term → EvalT Ψ (tof b) τv`
    (unconditional; the second conjunct of `S.Term.erase`). -/
theorem S.Term.toEvalT {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {τv : ValTy} (h : S.Term Δ Γ Ψ e b v τv) :
    ValTy.EvalT Ψ (Basis.tof b) τv :=
  (S.Term.erase ErasureErrataArms.holds h).2

end GLang
