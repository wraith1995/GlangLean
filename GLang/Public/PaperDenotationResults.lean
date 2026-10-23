import GLang.Public.PaperSourceResults
import GLang.Proofs.Adequacy.Raw.RawLlamSource
import GLang.Proofs.Adequacy.Foundations.OpenBridgeCore

namespace GLang.PaperDenotationResults

/-- The tensor-valued linear lambda really applies its body: the internal
linearity test cannot take its default branch under source typing. -/
theorem linearTensor_apply {Δ : LCtx} {ε : NLCtx} {σ : DEnv}
    {s₀ s₁ : Space} {body : Term}
    (hctx : InductiveCtxWF Δ ε)
    (ht : HasType Δ ε (.llam s₀ s₁ body) (.space (.tprod (.dual s₀) s₁)))
    (hσ : EnvWF σ Δ ε) (a : (denotSpace σ s₀).carrier) :
    (denotTerm σ (.llam s₀ s₁ body)).asLinMap
        (denotSpace σ s₀) (denotSpace σ s₁) a =
      (denotTermAux σ [.hil ⟨denotSpace σ s₀, a⟩] body).atSpace
        (denotSpace σ s₁) := by
  rw [denotTerm_llam_non_real ht.llam_tensor_codomain_ne_real,
    asLinMap_llamTensorDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap
    (denot_llam_tensor_body_isLinear ht hctx.toSourceContextWF.scoping hσ) a

/-- The real-codomain specialization denotes the body's linear functional. -/
theorem linearReal_apply {Δ : LCtx} {ε : NLCtx} {σ : DEnv}
    {s : Space} {body : Term}
    (hctx : InductiveCtxWF Δ ε)
    (ht : HasType Δ ε (.llam s .real body) (.space (.dual s)))
    (hσ : EnvWF σ Δ ε) (a : (denotSpace σ s).carrier) :
    (denotTerm σ (.llam s .real body)).atSpace (HSpace.dual (denotSpace σ s)) a =
      (denotTermAux σ [.hil ⟨denotSpace σ s, a⟩] body).atSpace HSpace.real := by
  rw [denotTerm_llam_real, atSpace_llamRealDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap
    (denot_llam_real_body_isLinear ht hctx.toSourceContextWF.scoping hσ) a

theorem nonlinear_apply {σ : DEnv} {d : Ty} {body : Term} {x : Name}
    (hlc : Term.lc (Term.openVar x body)) (hx : x ∉ Term.fv body)
    (a : (denotTy σ d).El) :
    (denotTerm σ (.nllam d body)).applyEl a =
      denotTerm (σ.bind x ((denotTy σ d).embed a)) (Term.openVar x body) := by
  rw [denotTerm_nllam_applyEl, denotTerm_openVar_bind hlc hx]

/-- Each dependent-type fiber is interpreted in the same named extension. -/
theorem dependentType_named {σ : DEnv} {d c : Ty} {x : Name}
    (hlc : Ty.lc (Ty.openVar x c)) (hx : x ∉ Ty.fv c) :
    denotTy σ (.piTy d c) =
      HType.sec (denotTy σ d).El (fun a =>
        denotTy (σ.bind x ((denotTy σ d).embed a)) (Ty.openVar x c)) := by
  change HType.sec (denotTy σ d).El
    (fun a => denotTyAux σ [((denotTy σ d).embed a)] c) = _
  congr 1
  funext a
  exact (denotTy_openVar_bind hlc hx).symm

theorem inner_eq_innerOf {σ : DEnv} {ε : NLCtx} {s : Space}
    (hctx : InductiveCtxWF ∅ ε) (hσ : EnvWF σ ∅ ε)
    (hs : SValid ε s) (hfresh : IofFresh ε) :
    (denotTerm σ (.inner s)).asLinMap (denotSpace σ s)
        (HSpace.dual (denotSpace σ s)) =
      (denotTerm σ (Space.iof s)).asLinMap (denotSpace σ s)
        (HSpace.dual (denotSpace σ s)) := by
  change (HSpace.innerTensor (denotSpace σ s) (denotSpace σ s).innerProduct).asLinMap
    (denotSpace σ s) (HSpace.dual (denotSpace σ s)) = _
  rw [asLinMap_innerTensor]
  exact (Space.iof_denot_eq_innerAssign
    (DEnv.IsCanonical_holds σ ε hfresh hσ hctx.toSourceContextWF.scoping) hs).symm

end GLang.PaperDenotationResults
