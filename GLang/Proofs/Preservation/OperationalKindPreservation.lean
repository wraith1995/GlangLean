import GLang.Operational.Supporting.OperationalBaseForms

/-! Every raw operational result has its requested basis kind under a regular
operational context. The linear-application output guard is shared with the
checked rule. Source-aligned wrappers remain available for existing callers. -/
namespace GLang.RuntimeValue

/-- Every unchecked result has the kind of its requested basis under a regular
operational environment. -/
theorem operational_kind_of_context
    {Ψ : EvalCtx} {e : Term} {b : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ e b v) :
    V2.EvalCtxValidPlus Ψ →
      (ValExpr.inferType v).structuralKind = (Basis.tof b).sourceKind := by
  refine h.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun Ψ e b v _ => V2.EvalCtxValidPlus Ψ →
      (ValExpr.inferType v).structuralKind = (Basis.tof b).sourceKind)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?oVar ?oCob ?oScale ?oAdd ?oDsum ?oTprod
    ?oPinvT ?oGpinvT ?oPinvD ?oGpinvD ?oInner
    ?oEmbedK ?oEmbedC ?oEmbedI ?oEmbedCI
    ?oAppL ?oAppI ?oNllam ?oAppN ?oReanchor ?oEta
    ?oReshape ?oLlam ?oLlamReal ?oZero ?oReal
  case oVar =>
    intro Ψ x b v hl hc
    exact (hc x b v hl).2.1.structuralKind_eq_sourceKind
  case oScale =>
    intro Ψ e0 e1 b v0 v1 h0 h1 ih0 ih1 hc
    simpa only [ValExpr.inferType,ValExpr.inferTypeCtx] using ih1 hc
  case oAppL =>
    intro Ψ b0 b1 e0 e1 v0 v1 sv0 sv1 h0 hs0 h1 hs1 hb ih0 ihs0 ih1 ihs1 hc
    simpa only [ValExpr.reshapBase,ValExpr.inferType_reshap,hb,ValTy.structuralKind,Ty.sourceKind]
  case oNllam =>
    intro Ψ b0 b1 t0 t1 e d c v hb0 hb1 hd L he hc ihd ihe ihc hctx
    have hdk := hd.structuralKind_eq_sourceKind
    obtain ⟨y,hy⟩ := Infinite.exists_notMem_finset L
    have hck := (hc y hy).structuralKind_eq_sourceKind
    simp only [ValTy.openVar,ValTy.structuralKind_openRec,Ty.openVar,Ty.sourceKind_openRec] at hck
    simpa only [ValExpr.inferType_vlam,ValTy.structuralKind,Basis.tof,Ty.sourceKind,hb0,hb1,hdk,hck]
  case oAppN =>
    intro Ψ b0 b1 e0 e1 v0 v1 out h0 h1 hout ih0 ih1 ihout hc
    exact hout.structuralKind_eq_sourceKind
  case oReanchor =>
    intro Ψ b0 b0' b1 e f a d d' c hd hb hf hd' L hx hcod ihd ihf ihd' ihx ihcod hc
    have hdk := hd.structuralKind_eq_sourceKind
    obtain ⟨y,hy⟩ := Infinite.exists_notMem_finset L
    have hck := (hcod y hy).structuralKind_eq_sourceKind
    simp only [ValTy.openVar,ValTy.structuralKind_openRec,Ty.openVar,Ty.sourceKind_openRec] at hck
    simpa only [ValExpr.inferType_vlam,ValTy.structuralKind,Basis.tof,Ty.sourceKind,hdk,hck]
  case oEta =>
    intro Ψ b0 b1 e d c v hd L he hcod ihd ihe ihcod hc
    have hdk := hd.structuralKind_eq_sourceKind
    obtain ⟨y,hy⟩ := Infinite.exists_notMem_finset L
    have hck := (hcod y hy).structuralKind_eq_sourceKind
    simp only [ValTy.openVar,ValTy.structuralKind_openRec,Ty.openVar,Ty.sourceKind_openRec] at hck
    simpa only [ValExpr.inferType_vlam,ValTy.structuralKind,Basis.tof,Ty.sourceKind,hdk,hck]
  case oReshape =>
    intro Ψ e b v src tgt he hs ht ihe ihs iht hc
    exact ht.structuralKind_eq_sourceKind
  all_goals intros
  all_goals try intro hc
  all_goals first | trivial | (simp_all [ValExpr.inferType,ValExpr.inferTypeCtx,
    ValExpr.reshapBase,ValExpr.sumAt,ValTy.structuralKind,Basis.tof,Ty.sourceKind])

  all_goals repeat (first | assumption | rfl | (split <;> simp_all [ValTy.structuralKind]))

/-- The inferred result and the requested source type have the same kind.
This is a consequence of existing source-aligned preservation, without
identifying independently realized value types or their dimensions. -/
theorem operational_kind {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx}
    {e : Term} {b : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ e b v) (hc : V2.EvalCtxValidPlus Ψ)
    (ht : HasType Δ Γ e (Basis.tof b)) (hb : Basis.BasisValid Γ b) :
    (ValExpr.inferType v).structuralKind = (Basis.tof b).sourceKind := by
  obtain ⟨hs⟩ := hb.sof_valid
  have hrho : V2.RhoValid Ψ Ψ.keyNames := by
    intro x b v _ hl
    obtain ⟨hvfv, hev, htfv, _, _⟩ := hc x b v hl
    exact ⟨⟨_, evalT_valid hev⟩, htfv, hvfv⟩
  obtain ⟨⟨tv,hev,k,⟨hi⟩,⟨hv⟩⟩,_,_⟩ :=
    V2.preservation_master.2.2.2 h Δ Γ Ψ.keyNames hc
      hrho (Finset.Subset.refl _) ht hs
  exact (ValTValidC.kind_eq_structural hi).symm.trans
    ((ValTValidC.kind_eq_structural hv).trans hev.structuralKind_eq_sourceKind)

/-- A source-typed evaluation at a valid frame infers a function type;
its two component kinds are fixed by the frame, not by coordinate choices. -/
theorem operational_frame_type {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx}
    {e : Term} {b₀ b₁ : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ e (.frame b₀ b₁) v) (hc : V2.EvalCtxValidPlus Ψ)
    (ht : HasType Δ Γ e (Basis.tof (.frame b₀ b₁)))
    (hb : Basis.BasisValid Γ (.frame b₀ b₁)) :
    ∃ d c, ValExpr.inferType v = .piTy d c ∧
      d.structuralKind = (Basis.tof b₀).sourceKind ∧
      c.structuralKind = (Basis.tof b₁).sourceKind := by
  have hk := operational_kind h hc ht hb
  cases heq : ValExpr.inferType v with
  | space s => simp [heq,ValTy.structuralKind,Basis.tof,Ty.sourceKind] at hk
  | piTy d c =>
    simp only [heq,ValTy.structuralKind,Basis.tof,Ty.sourceKind,ValKind.arrow.injEq] at hk
    exact ⟨d,c,rfl,hk⟩

/-- Independently compiled function and argument values have matching domain
kinds when each is typed at the source type of its requested basis. -/
theorem operational_application_kinds {Ψ : EvalCtx} {Δ₀ Δ₁ : LCtx} {Γ : NLCtx}
    {f a : Term} {b₀ b₁ : Basis} {vf va : ValExpr}
    (hf : ValExpr.OpStep Ψ f (.frame b₀ b₁) vf)
    (ha : ValExpr.OpStep Ψ a b₀ va) (hc : V2.EvalCtxValidPlus Ψ)
    (htf : HasType Δ₀ Γ f (Basis.tof (.frame b₀ b₁)))
    (hta : HasType Δ₁ Γ a (Basis.tof b₀))
    (hbf : Basis.BasisValid Γ (.frame b₀ b₁)) (hba : Basis.BasisValid Γ b₀) :
    ∃ d c, ValExpr.inferType vf = .piTy d c ∧
      (ValExpr.inferType va).structuralKind = d.structuralKind ∧
      c.structuralKind = (Basis.tof b₁).sourceKind := by
  obtain ⟨d,c,he,hd,hc'⟩ := operational_frame_type hf hc htf hbf
  exact ⟨d,c,he,(operational_kind ha hc hta hba).trans hd.symm,hc'⟩

end GLang.RuntimeValue
