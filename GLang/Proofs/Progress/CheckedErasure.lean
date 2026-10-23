import GLang.Operational.Checked

/-! Structural erasure and typing projections of checked evaluation. -/
namespace GLang
namespace RawCertifiedOperational
open Basis (BasisValid)

theorem C.TyAt.isTyBasis :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {b : Basis} {τv : ValTy},
      C.TyAt Γ Ψ b τv → Basis.IsTyBasis b
  | _, _, _, _, .space _ hb _ => hb.isTyBasis
  | _, _, _, _, .frame hb _ _ _ => hb.isTyBasis

/-- Exact type realization retains validity of its indexed basis. -/
theorem C.TyAt.basisValid :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {b : Basis} {τv : ValTy},
      C.TyAt Γ Ψ b τv → BasisValid Γ b
  | _, _, _, _, .space _ hbv _ => hbv
  | _, _, _, _, .frame hbv _ _ _ => hbv

/-! ## Literal erasure and checked-node projections -/

/-! ## Direct mutual erasure

Each certificate erases without consulting the strengthened semantics.  The
term erasure also returns its exact ordinary type evaluation; several live
ordinary constructors consume that component when reconstructing an EvalS
premise. -/

mutual

/-- Erasure `C.Space → ValSpace.EvalS` (rule for rule). -/
theorem C.Space.eraseJoint (E : ErasureErrataArms) :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {s : GLang.Space} {sv : ValSpace},
      C.Space Γ Ψ s sv → ValSpace.EvalS Ψ s sv
  | _, _, _, _, .real => .real
  | _, _, _, _, .empty => .empty
  | _, _, _, _, .dual _ h => .dual (C.Space.eraseJoint E h)
  | _, _, _, _, .ker _ hb hcompat hsvb he =>
      .ker (C.Term.eraseJoint E he).1 hb hcompat (C.Space.eraseJoint E hsvb)
  | _, _, _, _, .coker _ hb hcompat hsvb he =>
      .coker (C.Term.eraseJoint E he).1 hb hcompat (C.Space.eraseJoint E hsvb)
  | _, _, _, _, .img _ hb hcompat hsvb he =>
      .img (C.Term.eraseJoint E he).1 hb hcompat (C.Space.eraseJoint E hsvb)
  | _, _, _, _, .coimg _ hb hcompat hsvb he =>
      .coimg (C.Term.eraseJoint E he).1 hb hcompat (C.Space.eraseJoint E hsvb)
  | _, _, _, _, .tprod _ h₀ h₁ => .tprod (C.Space.eraseJoint E h₀) (C.Space.eraseJoint E h₁)
  | _, _, _, _, .dsum _ h₀ h₁ => .dsum (C.Space.eraseJoint E h₀) (C.Space.eraseJoint E h₁)

/-- Erasure `C.Ty → ValTy.EvalT` (rule for rule; the Π rule keeps its cofinite set). -/
theorem C.Ty.eraseJoint (E : ErasureErrataArms) :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {τ : GLang.Ty} {τv : ValTy},
      C.Ty Γ Ψ τ τv → ValTy.EvalT Ψ τ τv
  | _, _, _, _, .space h => .space (C.Space.eraseJoint E h)
  | _, _, _, _, .piTy _ hb _ h₀ L h₁ =>
      .piTy (C.Ty.eraseJoint E h₀) hb L (fun y hy => C.Ty.eraseJoint E (h₁ y hy))

/-- Erasure of the exact-basis type certificate.  The frame arm retains its
    recorded domain basis as the binder chosen by `EvalT.piTy`; the codomain
    basis is forgotten only after its recursively aligned proof is erased. -/
theorem C.TyAt.eraseJoint (E : ErasureErrataArms) :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {b : Basis} {τv : ValTy},
      C.TyAt Γ Ψ b τv → ValTy.EvalT Ψ (Basis.tof b) τv
  | _, _, _, _, .space htof _ hspace => by
      rw [htof]
      exact .space (C.Space.eraseJoint E hspace)
  | _, _, _, _, .frame _ hdom L hcod => by
      simp only [Basis.tof]
      exact .piTy (C.TyAt.eraseJoint E hdom) rfl L (fun y hy => by
        simpa only [Basis.openVar, Basis.tof_openRec] using
          C.TyAt.eraseJoint E (hcod y hy))

/-- Erasure `C.Cob → Basis.EvalBB` (rule for rule; `tprod` through `E.cob_tprod`). -/
theorem C.Cob.eraseJoint (E : ErasureErrataArms) :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {b₀ b₁ : Basis} {env : ValExpr},
      C.Cob Γ Ψ b₀ env b₁ → Basis.EvalBB Ψ b₀ env b₁
  | _, _, _, _, _, .inverse _ _ h => .inverse (C.Cob.eraseJoint E h)
  | _, _, _, _, _, .trans _ _ h₀ h₁ hsv =>
      .trans (C.Cob.eraseJoint E h₀) (C.Cob.eraseJoint E h₁) (C.Space.eraseJoint E hsv)
  | _, _, _, _, _, .tprod _ _ h₀ h₁ => E.cob_tprod (C.Cob.eraseJoint E h₀) (C.Cob.eraseJoint E h₁)
  | _, _, _, _, _, .dsum _ _ h₀ h₁ => .dsum (C.Cob.eraseJoint E h₀) (C.Cob.eraseJoint E h₁)
  | _, _, _, _, _, .dual_std htof _ _ hb₁ => .dual_std htof (C.Cob.eraseJoint E hb₁)
  | _, _, _, _, _, .image _ _ hcoker h => .image hcoker (C.Cob.eraseJoint E h)
  | _, _, _, _, _, .image_svds _ _ hs₀ hs₁ hb₀ hb₁ hsvb he =>
      .image_svds hs₀ hs₁ hb₀ hb₁ (C.Term.eraseJoint E he).1 (C.Space.eraseJoint E hsvb)
  | _, _, _, _, _, .proj_ker_coker _ _ hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₀' hcob hembd
      hproj =>
      .proj_ker_coker hs hsofb₀ hsofb₁ (C.Space.eraseJoint E hsv₀) (C.Space.eraseJoint E hsv₁)
        (C.Space.eraseJoint E hsv) (C.Space.eraseJoint E hsv') (C.Space.eraseJoint E hsv₀')
        (C.Cob.eraseJoint E hcob) (C.Term.eraseJoint E hembd).1 (C.Term.eraseJoint E hproj).1
  | _, _, _, _, _, .proj_img_coimg _ _ hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₁' hcob hembd
      hproj =>
      .proj_img_coimg hs hsofb₀ hsofb₁ (C.Space.eraseJoint E hsv₀) (C.Space.eraseJoint E hsv₁)
        (C.Space.eraseJoint E hsv) (C.Space.eraseJoint E hsv') (C.Space.eraseJoint E hsv₁')
        (C.Cob.eraseJoint E hcob) (C.Term.eraseJoint E hembd).1 (C.Term.eraseJoint E hproj).1
  | _, _, _, _, _, .terms_rref _ _ hbb hch hsv =>
      .terms_rref (C.Cob.eraseJoint E hbb) (C.Term.eraseJoint E hch).1 (C.Space.eraseJoint E hsv)
  | _, _, _, _, _, .refl _ htof hsv => .refl htof (C.Space.eraseJoint E hsv)
  | _, _, _, _, _, .proj_ker_coker_cod _ _ hs hsofb₀ hsofb₁ hsofb₁' hsv₀ hsv hsv' hembd hproj =>
      .proj_ker_coker_cod hs hsofb₀ hsofb₁ hsofb₁' (C.Space.eraseJoint E hsv₀)
        (C.Space.eraseJoint E hsv) (C.Space.eraseJoint E hsv')
        (C.Term.eraseJoint E hembd).1 (C.Term.eraseJoint E hproj).1
  | _, _, _, _, _, .proj_img_coimg_dom _ _ hs hsofb₀ hsofb₁ hsofb₀' hsv₁ hsv hsv' hembd hproj =>
      .proj_img_coimg_dom hs hsofb₀ hsofb₁ hsofb₀' (C.Space.eraseJoint E hsv₁)
        (C.Space.eraseJoint E hsv) (C.Space.eraseJoint E hsv')
        (C.Term.eraseJoint E hembd).1 (C.Term.eraseJoint E hproj).1

theorem C.Term.eraseJoint (E : ErasureErrataArms) :
    ∀ {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {e : GLang.Term} {b : Basis} {v : ValExpr}
      {τv : ValTy},
      C.Term Δ Γ Ψ e b v τv → ValExpr.OpStep Ψ e b v ∧ ValTy.EvalT Ψ (Basis.tof b) τv
  | _, _, _, _, _, _, _, .var_lin h _ _ hτv => ⟨.var h, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .var_nlin h _ _ hτv => ⟨.var h, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .promote _ _ _ _ _ _ _ hτv h =>
      ⟨(C.Term.eraseJoint E h).1, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .cob htof₀ htof₁ _ _ hτv he hbb hes =>
      ⟨.cob htof₀ htof₁ (C.Term.eraseJoint E he).1 (C.Cob.eraseJoint E hbb) (C.Space.eraseJoint E hes),
       C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .reshape_cob _ _ hτv he =>
      ⟨.reshape_cob (C.Term.eraseJoint E he).1 (C.Term.eraseJoint E he).2 (C.TyAt.eraseJoint E hτv),
       C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .scale _ _ _ _ hτv he₀ he₁ =>
      ⟨.scale (C.Term.eraseJoint E he₀).1 (C.Term.eraseJoint E he₁).1, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .add htof _ _ hτv he₀ he₁ =>
      let hτ := C.TyAt.eraseJoint E hτv
      ⟨.add htof (ValSpace.EvalS.sof_of_evalT_tof hτ)
        (C.Term.eraseJoint E he₀).1 (C.Term.eraseJoint E he₁).1, hτ⟩
  | _, _, _, _, _, _, _, .dsumE htof₀ htof₁ _ _ hτv he₀ he₁ =>
      ⟨.dsumE (C.Term.eraseJoint E he₀).1 (C.Term.eraseJoint E he₁).1 htof₀ htof₁, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .tprodE _ htof₀ htof₁ _ _ hτv he₀ he₁ =>
      ⟨.tprodE (C.Term.eraseJoint E he₀).1 (C.Term.eraseJoint E he₁).1 htof₀ htof₁, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .pinvT_std hb₀ hb₁ _ _ hτv he =>
      ⟨.pinvT_std (C.Term.eraseJoint E he).1 hb₀ hb₁, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .pinvT_gpinv _ _ hτv he hi₀ hi₁ =>
      ⟨E.pinvT_gpinv (C.Term.eraseJoint E he).1 (C.Term.eraseJoint E hi₀).1 (C.Term.eraseJoint E hi₁).1,
       C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .pinvD_std hsofb₀ hb₀ hb₁ _ _ hτv he =>
      ⟨E.pinvD_std hsofb₀ hb₀ hb₁ (C.Term.eraseJoint E he).1
        (ValSpace.EvalS.dual_inv (ValSpace.EvalS.sof_of_evalT_tof (C.Term.eraseJoint E he).2)),
       C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .pinvD_gpinv hsofb₀ hb₀ _ _ hτv he hi₀ hi₁ =>
      ⟨E.pinvD_gpinv hsofb₀ hb₀ (C.Term.eraseJoint E he).1
        (ValSpace.EvalS.dual_inv (ValSpace.EvalS.sof_of_evalT_tof (C.Term.eraseJoint E he).2))
        (C.Term.eraseJoint E hi₀).1 (C.Term.eraseJoint E hi₁).1,
       C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .inner_std hb₀ hsof _ _ hτv hsv =>
      ⟨.inner_std hb₀ (C.Space.eraseJoint E hsv) hsof, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .embed_ker hs₀ hs₁ _ _ hτv hi₀ hi₁ he =>
      ⟨E.embed_ker hs₀ hs₁ (C.Term.eraseJoint E hi₀).1 (C.Term.eraseJoint E hi₁).1
        (C.Term.eraseJoint E he).1, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .embed_coker hs₀ hs₁ _ _ hτv hi₀ hi₁ he =>
      ⟨E.embed_coker hs₀ hs₁ (C.Term.eraseJoint E hi₀).1 (C.Term.eraseJoint E hi₁).1
        (C.Term.eraseJoint E he).1, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .embed_img hs₀ hs₁ _ _ hτv hi₀ hi₁ he =>
      ⟨E.embed_img hs₀ hs₁ (C.Term.eraseJoint E hi₀).1 (C.Term.eraseJoint E hi₁).1
        (C.Term.eraseJoint E he).1, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .embed_coimg hs₀ hs₁ _ _ hτv hi₀ hi₁ he =>
      ⟨E.embed_coimg hs₀ hs₁ (C.Term.eraseJoint E hi₀).1 (C.Term.eraseJoint E hi₁).1
        (C.Term.eraseJoint E he).1, C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .appL_lin _ htof₁ _ _ hsv hτv h₀ h₁ =>
      ⟨.appL_lin (C.Term.eraseJoint E h₀).1
        (C.Space.eraseJoint E hsv) (C.Term.eraseJoint E h₁).1
        (ValSpace.EvalS.sof_of_evalT_tof (C.TyAt.eraseJoint E hτv)) htof₁,
       C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .appI_lin _ _ hsv hτv h₀ h₁ =>
      ⟨E.appI_lin (C.Term.eraseJoint E h₀).1
        (C.Space.eraseJoint E hsv) (C.Term.eraseJoint E h₁).1,
       C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .nllam hb₀ hb₁ _ _ hτv h₀ L he h₁ =>
      ⟨.nllam hb₀ hb₁ (by simpa only [hb₀] using C.TyAt.eraseJoint E h₀) L
        (fun y hy => (C.Term.eraseJoint E (he y hy)).1)
        (fun y hy => by
          simpa only [Basis.openVar, Basis.tof_openRec, hb₁] using C.TyAt.eraseJoint E (h₁ y hy)),
        C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .appN_val _ _ hτv h₀ h₁ =>
      ⟨.appN_val (C.Term.eraseJoint E h₀).1 (C.Term.eraseJoint E h₁).1 (C.TyAt.eraseJoint E hτv),
       C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .frame_reanchor htof _ _ hτv h₀ hfn hdom L hx hcod =>
      ⟨.frame_reanchor (C.TyAt.eraseJoint E h₀) htof (C.Term.eraseJoint E hfn).1
        (C.TyAt.eraseJoint E hdom) L
        (fun y hy => (C.Term.eraseJoint E (hx y hy)).1) (fun y hy => by
          simpa only [Basis.openVar, Basis.tof_openRec] using C.TyAt.eraseJoint E (hcod y hy)),
       C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .frame_eta _ _ hτv h₀ L he h₁ =>
      ⟨.frame_eta (C.TyAt.eraseJoint E h₀) L (fun y hy => (C.Term.eraseJoint E (he y hy)).1)
        (fun y hy => by
          simpa only [Basis.openVar, Basis.tof_openRec] using C.TyAt.eraseJoint E (h₁ y hy)),
        C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .llam_assemble htof' _ _ hτv hsv' hsv L hfam =>
      ⟨.llam_assemble htof' (C.Space.eraseJoint E hsv') (C.Space.eraseJoint E hsv) L
        (fun y hy i => (C.Term.eraseJoint E (hfam y hy i)).1), C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .llam_assemble_real htof' _ _ hτv hsv' L hfam =>
      ⟨.llam_assemble_real htof' (C.Space.eraseJoint E hsv') L
        (fun y hy i => (C.Term.eraseJoint E (hfam y hy i)).1), C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .zero htof _ _ hτv hsv =>
      ⟨.zero htof (C.Space.eraseJoint E hsv), C.TyAt.eraseJoint E hτv⟩
  | _, _, _, _, _, _, _, .rlit r _ hτv => ⟨.rlit r, C.TyAt.eraseJoint E hτv⟩

end

/-! ## Public projections -/

theorem C.Space.erase
    (h : C.Space Gamma Psi s sv) : ValSpace.EvalS Psi s sv :=
  C.Space.eraseJoint ErasureErrataArms.holds h

theorem C.Ty.erase
    (h : C.Ty Gamma Psi tau tauv) : ValTy.EvalT Psi tau tauv :=
  C.Ty.eraseJoint ErasureErrataArms.holds h

theorem C.TyAt.erase
    (h : C.TyAt Gamma Psi b tauv) :
    ValTy.EvalT Psi (Basis.tof b) tauv :=
  C.TyAt.eraseJoint ErasureErrataArms.holds h

theorem C.Cob.erase
    (h : C.Cob Gamma Psi b0 env b1) : Basis.EvalBB Psi b0 env b1 :=
  C.Cob.eraseJoint ErasureErrataArms.holds h

/-- Literal term erasure: source, basis, and produced value are unchanged. -/
theorem C.Term.erase
    (h : C.Term Delta Gamma Psi e b v tauv) :
    ValExpr.OpStep Psi e b v :=
  (C.Term.eraseJoint ErasureErrataArms.holds h).1

theorem C.Term.toEvalT
    (h : C.Term Delta Gamma Psi e b v tauv) :
    ValTy.EvalT Psi (Basis.tof b) tauv :=
  (C.Term.eraseJoint ErasureErrataArms.holds h).2

/-- Every checked term node carries the source typing of its conclusion. -/
theorem C.Term.hasType
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {e : GLang.Term}
    {b : Basis} {v : ValExpr} {tauv : ValTy}
    (h : C.Term Delta Gamma Psi e b v tauv) :
    Nonempty (HasType Delta Gamma e (Basis.tof b)) := by
  cases h with
  | var_lin _ htof _ _ => rw [htof]; exact ⟨.var_lin⟩
  | var_nlin _ hGamma _ _ => exact ⟨.var_nlin hGamma⟩
  | promote _ _ _ _ _ ht _ _ _ => exact ht
  | cob _ _ ht _ _ _ _ _ => exact ht
  | reshape_cob ht _ _ _ => exact ht
  | scale _ _ ht _ _ _ _ => exact ht
  | add _ ht _ _ _ _ => exact ht
  | dsumE _ _ ht _ _ _ _ => exact ht
  | tprodE _ _ _ ht _ _ _ _ => exact ht
  | pinvT_std _ _ ht _ _ _ => exact ht
  | pinvT_gpinv ht _ _ _ _ _ => exact ht
  | pinvD_std _ _ _ ht _ _ _ => exact ht
  | pinvD_gpinv _ _ ht _ _ _ _ _ => exact ht
  | inner_std _ _ ht _ _ _ => exact ht
  | embed_ker _ _ ht _ _ _ _ _ => exact ht
  | embed_coker _ _ ht _ _ _ _ _ => exact ht
  | embed_img _ _ ht _ _ _ _ _ => exact ht
  | embed_coimg _ _ ht _ _ _ _ _ => exact ht
  | appL_lin _ _ ht _ _ _ _ _ => exact ht
  | appI_lin _ ht _ _ _ _ => exact ht
  | nllam _ _ ht _ _ _ _ _ _ => exact ht
  | appN_val ht _ _ _ _ => exact ht
  | frame_reanchor _ ht _ _ _ _ _ _ _ _ => exact ht
  | frame_eta ht _ _ _ _ _ _ => exact ht
  | llam_assemble _ ht _ _ _ _ _ _ => exact ht
  | llam_assemble_real _ ht _ _ _ _ _ => exact ht
  | zero _ ht _ _ _ => exact ht
  | rlit _ ht _ => exact ht

/-- Every checked term node carries validity of its conclusion basis. -/
theorem C.Term.basisValid
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {e : GLang.Term}
    {b : Basis} {v : ValExpr} {tauv : ValTy}
    (h : C.Term Delta Gamma Psi e b v tauv) : BasisValid Gamma b := by
  cases h with
  | var_lin _ _ hbv _ => exact hbv
  | var_nlin _ _ hbv _ => exact hbv
  | promote _ _ _ _ _ _ hbv _ _ => exact hbv
  | cob _ _ _ hbv _ _ _ _ => exact hbv
  | reshape_cob _ hbv _ _ => exact hbv
  | scale _ _ _ hbv _ _ _ => exact hbv
  | add _ _ hbv _ _ _ => exact hbv
  | dsumE _ _ _ hbv _ _ _ => exact hbv
  | tprodE _ _ _ _ hbv _ _ _ => exact hbv
  | pinvT_std _ _ _ hbv _ _ => exact hbv
  | pinvT_gpinv _ hbv _ _ _ _ => exact hbv
  | pinvD_std _ _ _ _ hbv _ _ => exact hbv
  | pinvD_gpinv _ _ _ hbv _ _ _ _ => exact hbv
  | inner_std _ _ _ hbv _ _ => exact hbv
  | embed_ker _ _ _ hbv _ _ _ _ => exact hbv
  | embed_coker _ _ _ hbv _ _ _ _ => exact hbv
  | embed_img _ _ _ hbv _ _ _ _ => exact hbv
  | embed_coimg _ _ _ hbv _ _ _ _ => exact hbv
  | appL_lin _ _ _ hbv _ _ _ _ => exact hbv
  | appI_lin _ _ _ _ _ _ => exact .one
  | nllam _ _ _ hbv _ _ _ _ _ => exact hbv
  | appN_val _ hbv _ _ _ => exact hbv
  | frame_reanchor _ _ hbv _ _ _ _ _ _ _ => exact hbv
  | frame_eta _ hbv _ _ _ _ _ => exact hbv
  | llam_assemble _ _ hbv _ _ _ _ _ => exact hbv
  | llam_assemble_real _ _ hbv _ _ _ _ => exact hbv
  | zero _ _ hbv _ _ => exact hbv
  | rlit _ _ _ => exact .one

/-- Exact result-type certificate retained at every checked term node. -/
theorem C.Term.tyAt
    (h : C.Term Delta Gamma Psi e b v tauv) : C.TyAt Gamma Psi b tauv := by
  cases h <;> assumption

end RawCertifiedOperational
end GLang
