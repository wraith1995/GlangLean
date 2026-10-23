import GLang.Proofs.Adequacy.Foundations.Strengthened

namespace GLang

open Basis (BasisValid)

/-! ## `tof` / `sof` bookkeeping -/

/-- A basis whose type is a space type is a space basis of exactly that space
    (`Basis.tof` is `.space (sof b)` on every non-frame constructor; frames have a Π type). -/
theorem Basis.sof_of_tof_space {b : Basis} {s : GLang.Space}
    (h : Basis.tof b = .space s) : Basis.sof b = s := by
  cases b <;> simp only [Basis.tof, Ty.space.injEq, reduceCtorEq] at h <;> exact h

/-- A basis whose type is a space type has `tof b = .space (sof b)` (the `htof` premise shape
    of the operational rules). -/
theorem Basis.tof_eq_space_sof_of_tof_space {b : Basis} {s : GLang.Space}
    (h : Basis.tof b = .space s) : Basis.tof b = .space (Basis.sof b) := by
  rw [h, Basis.sof_of_tof_space h]

/-! ## Read-off invariants (D2) -/

theorem S.Space.svalid {Γ : NLCtx} {Ψ : EvalCtx} {s : GLang.Space} {sv : ValSpace}
    (h : S.Space Γ Ψ s sv) : Nonempty (SValid Γ s) := by
  cases h with
  | real => exact ⟨.real⟩
  | empty => exact ⟨.empty⟩
  | dual hs _ => exact hs
  | ker hs _ _ _ _ => exact hs
  | coker hs _ _ _ _ => exact hs
  | img hs _ _ _ _ => exact hs
  | coimg hs _ _ _ _ => exact hs
  | tprod hs _ _ => exact hs
  | dsum hs _ _ => exact hs

/-- The part of value-space shape forced by a source tensor product. -/
private def SSpaceShape (s : GLang.Space) (sv : ValSpace) : Prop :=
  match s with
  | .tprod _ _ => ∃ sv₀ sv₁, sv = .tprod sv₀ sv₁
  | _ => True

/-- Shape information retained by strengthened space evaluation.  This is
    stated through the generated mutual recursor because `S.Space` belongs to
    the mutually inductive strengthened family. -/
private theorem S.Space.shape :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {s : GLang.Space} {sv : ValSpace},
      S.Space Γ Ψ s sv → SSpaceShape s sv := by
  intro Γ Ψ s sv h
  refine S.Space.rec
    (motive_1 := fun _ _ s sv _ => SSpaceShape s sv)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
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
    ?termZero ?termRlit h
  case spaceTprod =>
    intros
    simp only [SSpaceShape]
    exact ⟨_, _, rfl⟩
  all_goals intros <;> trivial

/-- A tensor-product source space can only evaluate to a tensor-product value
    space.  Administrative source-world transport preserves the value
    literally, so the shape fact recurses through it unchanged. -/
theorem S.Space.tprod_value_inv {Γ : NLCtx} {Ψ : EvalCtx}
    {s₀ s₁ : GLang.Space} {sv : ValSpace}
    (h : S.Space Γ Ψ (.tprod s₀ s₁) sv) :
    ∃ sv₀ sv₁, sv = .tprod sv₀ sv₁ :=
  S.Space.shape h

/-- `S.Ty` carries `TValid` at some kind (the `.space` arm via `S.Space.svalid`, the `.piTy`
    arm via its `ht` premise). -/
theorem S.Ty.tvalid {Γ : NLCtx} {Ψ : EvalCtx} {τ : GLang.Ty} {τv : ValTy}
    (h : S.Ty Γ Ψ τ τv) : ∃ k, Nonempty (TValid Γ τ k) := by
  cases h with
  | space hs => obtain ⟨v⟩ := S.Space.svalid hs; exact ⟨.base, ⟨.space v⟩⟩
  | piTy ht _ _ _ _ _ => exact ⟨_, ht⟩

/-- Shape information retained by a strengthened type evaluation.  Keeping
    the realized type general makes recursion through administrative
    source-world transports structurally evident to Lean. -/
private def STyShape (Γ : NLCtx) (Ψ : EvalCtx) (τ : GLang.Ty) : ValTy → Prop
  | .space sv => ∃ s, τ = .space s ∧ S.Space Γ Ψ s sv
  | .piTy τv₀ _ => ∃ τ₀ τ₁, τ = .piTy τ₀ τ₁ ∧ S.Ty Γ Ψ τ₀ τv₀

private theorem S.Ty.shape :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {τ : GLang.Ty} {τv : ValTy},
      S.Ty Γ Ψ τ τv → STyShape Γ Ψ τ τv := by
  intro Γ Ψ τ τv h
  refine S.Ty.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Γ Ψ τ τv _ => STyShape Γ Ψ τ τv)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
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
    ?termZero ?termRlit h
  case tySpace =>
    intros
    simp only [STyShape]
    exact ⟨_, rfl, by assumption⟩
  case tyPi =>
    intros
    simp only [STyShape]
    exact ⟨_, _, rfl, by assumption⟩
  all_goals intros <;> trivial

/-- Inversion of `S.Ty` at a space value type: the source type is a space type and the
    realization is an `S.Space` derivation (administrative transports are retained). -/
theorem S.Ty.space_inv {Γ : NLCtx} {Ψ : EvalCtx} {τ : GLang.Ty} {sv : ValSpace}
    (h : S.Ty Γ Ψ τ (.space sv)) : ∃ s, τ = .space s ∧ S.Space Γ Ψ s sv :=
  S.Ty.shape h

/-- Inversion of `S.Ty` at a Π value type. -/
theorem S.Ty.piTy_inv {Γ : NLCtx} {Ψ : EvalCtx} {τ : GLang.Ty} {τv₀ τv₁ : ValTy}
    (h : S.Ty Γ Ψ τ (.piTy τv₀ τv₁)) : ∃ τ₀ τ₁, τ = .piTy τ₀ τ₁ :=
  let ⟨τ₀, τ₁, hτ, _⟩ := S.Ty.shape h
  ⟨τ₀, τ₁, hτ⟩

/-- Source-directed companion to `space_inv`: evaluating a source space type
    always produces a value space, even through administrative transports. -/
theorem S.Ty.source_space_inv {Γ : NLCtx} {Ψ : EvalCtx}
    {s : GLang.Space} {τv : ValTy}
    (h : S.Ty Γ Ψ (.space s) τv) :
    ∃ sv, τv = .space sv ∧ S.Space Γ Ψ s sv := by
  cases τv with
  | space sv =>
      obtain ⟨s', hs, hspace⟩ := S.Ty.space_inv h
      cases hs
      exact ⟨sv, rfl, hspace⟩
  | piTy τv₀ τv₁ =>
      obtain ⟨τ₀, τ₁, hs⟩ := S.Ty.piTy_inv h
      cases hs

/-- Inversion of a function-valued `S.Ty` also retains its domain
    realization through any number of administrative source-world
    transports. -/
theorem S.Ty.piTy_domain {Γ : NLCtx} {Ψ : EvalCtx}
    {τ₀ τ₁ : GLang.Ty} {τv₀ τv₁ : ValTy}
    (h : S.Ty Γ Ψ (.piTy τ₀ τ₁) (.piTy τv₀ τv₁)) :
    S.Ty Γ Ψ τ₀ τv₀ := by
  obtain ⟨τ₀', τ₁', hτ, hdom⟩ := S.Ty.shape h
  cases hτ
  exact hdom

/-- `S.Ty` at a space basis `b` (i.e. `tof b = .space (sof b)`) realizes `sof b`. -/
theorem S.Ty.space_of_tof {Γ : NLCtx} {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
    (h : S.Ty Γ Ψ (Basis.tof b) (.space sv)) : S.Space Γ Ψ (Basis.sof b) sv := by
  obtain ⟨s, hs, hsv⟩ := S.Ty.space_inv h
  rw [Basis.sof_of_tof_space hs]; exact hsv

theorem S.Term.hasType {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {e : GLang.Term} {b : Basis}
    {v : ValExpr} {τv : ValTy} (h : S.Term Δ Γ Ψ e b v τv) :
    Nonempty (HasType Δ Γ e (Basis.tof b)) := by
  cases h with
  | var_lin _ htof _ _ => rw [htof]; exact ⟨.var_lin⟩
  | var_nlin _ hΓ _ _ => exact ⟨.var_nlin hΓ⟩
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

/-- `S.Term` carries the validity of its conclusion basis (D2 read-off; `appI_lin` and `rlit`
    conclude at `.one`, which is valid outright). -/
theorem S.Term.basisValid {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {e : GLang.Term} {b : Basis}
    {v : ValExpr} {τv : ValTy} (h : S.Term Δ Γ Ψ e b v τv) : BasisValid Γ b := by
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

theorem S.Term.ty {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {e : GLang.Term} {b : Basis}
    {v : ValExpr} {τv : ValTy} (h : S.Term Δ Γ Ψ e b v τv) : S.Ty Γ Ψ (Basis.tof b) τv := by
  cases h with
  | var_lin _ _ _ hτv => exact hτv.toTy
  | var_nlin _ _ _ hτv => exact hτv.toTy
  | promote _ _ _ _ _ _ _ hτv _ => exact hτv.toTy
  | cob _ _ _ _ hτv _ _ _ => exact hτv.toTy
  | reshape_cob _ _ hτv _ => exact hτv.toTy
  | scale _ _ _ _ hτv _ _ => exact hτv.toTy
  | add _ _ _ hτv _ _ => exact hτv.toTy
  | dsumE _ _ _ _ hτv _ _ => exact hτv.toTy
  | tprodE _ _ _ _ _ hτv _ _ => exact hτv.toTy
  | pinvT_std _ _ _ _ hτv _ => exact hτv.toTy
  | pinvT_gpinv _ _ hτv _ _ _ => exact hτv.toTy
  | pinvD_std _ _ _ _ _ hτv _ => exact hτv.toTy
  | pinvD_gpinv _ _ _ _ hτv _ _ _ => exact hτv.toTy
  | inner_std _ _ _ _ hτv _ => exact hτv.toTy
  | embed_ker _ _ _ _ hτv _ _ _ => exact hτv.toTy
  | embed_coker _ _ _ _ hτv _ _ _ => exact hτv.toTy
  | embed_img _ _ _ _ hτv _ _ _ => exact hτv.toTy
  | embed_coimg _ _ _ _ hτv _ _ _ => exact hτv.toTy
  | appL_lin _ _ _ _ _ hτv _ _ => exact hτv.toTy
  | appI_lin _ _ _ hτv _ _ => exact hτv.toTy
  | nllam _ _ _ _ hτv _ _ _ _ => exact hτv.toTy
  | appN_val _ _ hτv _ _ => exact hτv.toTy
  | frame_reanchor _ _ _ hτv _ _ _ _ _ _ => exact hτv.toTy
  | frame_eta _ _ hτv _ _ _ _ => exact hτv.toTy
  | llam_assemble _ _ _ hτv _ _ _ _ => exact hτv.toTy
  | llam_assemble_real _ _ _ hτv _ _ _ => exact hτv.toTy
  | zero _ _ _ hτv _ => exact hτv.toTy
  | rlit _ _ hτv => exact hτv.toTy

/-- `S.Cob` carries the validity of its SOURCE basis (position 1; D2 read-off). -/
theorem S.Cob.basisValid_src {Γ : NLCtx} {Ψ : EvalCtx} {b₀ b₁ : Basis} {env : ValExpr}
    (h : S.Cob Γ Ψ b₀ env b₁) : BasisValid Γ b₀ := by
  cases h with
  | inverse hb₀ _ _ => exact hb₀
  | trans hb₀ _ _ _ _ => exact hb₀
  | tprod hbS _ _ _ => exact hbS
  | dsum hbS _ _ _ => exact hbS
  | dual_std _ hbS _ _ => exact hbS
  | image hbS _ _ _ => exact hbS
  | image_svds hbS _ _ _ _ _ _ _ => exact hbS
  | proj_ker_coker hbS _ _ _ _ _ _ _ _ _ _ _ _ => exact hbS
  | proj_img_coimg hbS _ _ _ _ _ _ _ _ _ _ _ _ => exact hbS
  | terms_rref hbS _ _ _ _ => exact hbS
  | refl hb _ _ => exact hb
  | proj_ker_coker_cod hbS _ _ _ _ _ _ _ _ _ _ => exact hbS
  | proj_img_coimg_dom hbS _ _ _ _ _ _ _ _ _ _ => exact hbS

/-- `S.Cob` carries the validity of its TARGET basis (position 3; D2 read-off). -/
theorem S.Cob.basisValid_tgt {Γ : NLCtx} {Ψ : EvalCtx} {b₀ b₁ : Basis} {env : ValExpr}
    (h : S.Cob Γ Ψ b₀ env b₁) : BasisValid Γ b₁ := by
  cases h with
  | inverse _ hb₁ _ => exact hb₁
  | trans _ hb₂ _ _ _ => exact hb₂
  | tprod _ hbT _ _ => exact hbT
  | dsum _ hbT _ _ => exact hbT
  | dual_std _ _ hbT _ => exact hbT
  | image _ hbT _ _ => exact hbT
  | image_svds _ hbT _ _ _ _ _ _ => exact hbT
  | proj_ker_coker _ hbT _ _ _ _ _ _ _ _ _ _ _ => exact hbT
  | proj_img_coimg _ hbT _ _ _ _ _ _ _ _ _ _ _ => exact hbT
  | terms_rref _ hbT _ _ _ => exact hbT
  | refl hb _ _ => exact hb
  | proj_ker_coker_cod _ hbT _ _ _ _ _ _ _ _ _ => exact hbT
  | proj_img_coimg_dom _ hbT _ _ _ _ _ _ _ _ _ => exact hbT

theorem S.Cob.sof_eq :
    ∀ {Γ : NLCtx} {Ψ : EvalCtx} {b₀ b₁ : Basis} {env : ValExpr},
      S.Cob Γ Ψ b₀ env b₁ → Basis.sof b₀ = Basis.sof b₁
  | _, _, _, _, _, .inverse _ _ h => (S.Cob.sof_eq h).symm
  | _, _, _, _, _, .trans _ _ h₀ h₁ _ => (S.Cob.sof_eq h₀).trans (S.Cob.sof_eq h₁)
  | _, _, _, _, _, .tprod _ _ h₀ h₁ => by
      simp only [Basis.sof, S.Cob.sof_eq h₀, S.Cob.sof_eq h₁]
  | _, _, _, _, _, .dsum _ _ h₀ h₁ => by
      simp only [Basis.sof, S.Cob.sof_eq h₀, S.Cob.sof_eq h₁]
  | _, _, _, _, _, .dual_std _ _ _ _ => by
      simp [Basis.sof, Basis.tof, Basis.std, Basis.stdSpace, Basis.sof_stdSpace]
  | _, _, _, _, _, .image _ _ _ h => by simp only [Basis.sof, S.Cob.sof_eq h]
  | _, _, _, _, _, .image_svds .. => rfl
  | _, _, _, _, _, .proj_ker_coker .. => rfl
  | _, _, _, _, _, .proj_img_coimg .. => rfl
  | _, _, _, _, _, .terms_rref _ _ hbb _ _ => by
      simpa only [Basis.sof] using S.Cob.sof_eq hbb
  | _, _, _, _, _, .refl .. => rfl
  | _, _, _, _, _, .proj_ker_coker_cod .. => rfl
  | _, _, _, _, _, .proj_img_coimg_dom .. => rfl

end GLang
