import GLang.Proofs.Value.Presentation.PaperValueOpenPush
import GLang.Proofs.Value.Presentation.PaperValueMatchedCoherence

namespace GLang.PaperValueDomains
open DirectOracleReshape ValueDependency

/-- The original cofinite lambda rule's semantic induction step. Domain
closure and coherence are the type-induction conclusions; the body premise is
quantified over related declared contexts, not over evaluated body results. -/
theorem matched_lambda_step (ε : ValCtx) (d c : ValTy) (body : ValExpr)
    (L : Finset VName) {k : ValKind} (hd : ValTValid ε d k)
    (hclosed : ValTy.lc d)
    (hbody : ∀ x, x ∉ L → ∀ ρ ρ',
      MatchedContextRelated directOracle (Finmap.insert x d ε) ρ ρ'
        (ValueDependency.exprAnnotations (ValExpr.openVar x d body)) →
      PartialRel (RuntimeRelated directOracle (ValTy.openVar x d c)
        ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
        (denotValB_semS directOracle ρ [] [] (ValExpr.openVar x d body))
        (denotValB_semS directOracle ρ' [] [] (ValExpr.openVar x d body)))
    (ρ ρ' : ValEnvSem) (hctx : MatchedContextRelated directOracle ε ρ ρ'
      (ValueDependency.exprAnnotations (.vlam d c body)))
    (hc : TypeCoherent directOracle d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩) :
    PartialRel (RuntimeRelated directOracle (.piTy d c) ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
      (denotValB_semS directOracle ρ [] [] (.vlam d c body))
      (denotValB_semS directOracle ρ' [] [] (.vlam d c body)) := by
  apply eval_lambda_related
  intro a b hab
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (L ∪ ε.keys ∪ ε.fvSupport ∪ ValTy.fv d ∪ ValTy.fv c ∪ ValExpr.fv body ∪ annotationSupport (exprAnnotations body))
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨⟨hxL, hxε⟩, hxSupport⟩, hxd⟩, hxc⟩, hxe⟩, hxAnn⟩ := hx
  have hv := reify_related directOracle d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ a b hab
  let v := ValValSem.fromEl (denotValTyS directOracle ρ [] [] d) a
  let v' := ValValSem.fromEl (denotValTyS directOracle ρ' [] [] d) b
  have hcb := hctx.mono (xs := exprAnnotations body) (by
    intro q hq; simp only [exprAnnotations, List.mem_append]; exact Or.inr hq)
  have hcd := hctx.coherent.mono (xs := typeAnnotations d) (by
    intro q hq; simp only [exprAnnotations, List.mem_append]; exact Or.inl (Or.inl hq))
  have hctx' := MatchedContextRelated.update_expr_open directOracle_spec.fvIrrel body hcb x d v v' hd
    (by simpa only [Finmap.mem_keys] using hxε) hxSupport hcd hc hv hxe hxAnn hxd
  let W : OpenPushWorld directOracle :=
    { rho := ρ, y := x, sigmaV := d, w := v, G := [], D := [],
      length_eq := rfl, sigma_lc := hclosed, y_sigma := hxd, y_G := by simp }
  let W' : OpenPushWorld directOracle :=
    { rho := ρ', y := x, sigmaV := d, w := v', G := [], D := [],
      length_eq := rfl, sigma_lc := hclosed, y_sigma := hxd, y_G := by simp }
  have hopen := hbody x hxL (ρ.update x v) (ρ'.update x v') hctx'
  have hout := eval_related_openPush c body W W' rfl rfl hxc hxc hxe hxe hopen
  simpa only [W, W', OpenPushWorld.pushedWorld, OpenPushWorld.pushedRho,
    OpenPushWorld.pushedG, OpenPushWorld.pushedD, List.nil_append,
    World.push, World.denot, v, v'] using hout

/-- The original cofinite dependent-function type rule's coherence step. -/
theorem matched_pi_step (ε : ValCtx) (d c : ValTy)
    (L : Finset VName) {k : ValKind} (hd : ValTValid ε d k)
    (hclosed : ValTy.lc d)
    (hcod : ∀ x, x ∉ L → ∀ ρ ρ',
      MatchedContextRelated directOracle (Finmap.insert x d ε) ρ ρ'
        (ValueDependency.typeAnnotations (ValTy.openVar x d c)) →
      TypeCoherent directOracle (ValTy.openVar x d c) ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (ρ ρ' : ValEnvSem) (hctx : MatchedContextRelated directOracle ε ρ ρ'
      (ValueDependency.typeAnnotations (.piTy d c)))
    (hc : TypeCoherent directOracle d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩) :
    TypeCoherent directOracle (.piTy d c) ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ := by
  refine ⟨hc, ?_⟩
  intro a b hab
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (L ∪ ε.keys ∪ ε.fvSupport ∪ ValTy.fv d ∪ ValTy.fv c ∪ annotationSupport (typeAnnotations c))
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨hxL, hxε⟩, hxSupport⟩, hxd⟩, hxc⟩, hxAnn⟩ := hx
  have hv := reify_related directOracle d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ a b hab
  let v := ValValSem.fromEl (denotValTyS directOracle ρ [] [] d) a
  let v' := ValValSem.fromEl (denotValTyS directOracle ρ' [] [] d) b
  have hcb := hctx.mono (xs := typeAnnotations c) (by
    intro q hq; simp only [typeAnnotations, List.mem_append]; exact Or.inr hq)
  have hcd := hctx.coherent.mono (xs := typeAnnotations d) (by
    intro q hq; simp only [typeAnnotations, List.mem_append]; exact Or.inl hq)
  have hctx' := MatchedContextRelated.update_type_open directOracle_spec.fvIrrel c hcb x d v v' hd
    (by simpa only [Finmap.mem_keys] using hxε) hxSupport hcd hc hv hxc hxAnn hxd
  let W : OpenPushWorld directOracle :=
    { rho := ρ, y := x, sigmaV := d, w := v, G := [], D := [],
      length_eq := rfl, sigma_lc := hclosed, y_sigma := hxd, y_G := by simp }
  let W' : OpenPushWorld directOracle :=
    { rho := ρ', y := x, sigmaV := d, w := v', G := [], D := [],
      length_eq := rfl, sigma_lc := hclosed, y_sigma := hxd, y_G := by simp }
  have hopen := hcod x hxL (ρ.update x v) (ρ'.update x v') hctx'
  have hout := typeCoherent_openPush c W W' rfl rfl hxc hxc hopen
  simpa only [W, W', OpenPushWorld.pushedWorld, OpenPushWorld.pushedRho,
    OpenPushWorld.pushedG, OpenPushWorld.pushedD, List.nil_append,
    World.push, World.denot, v, v'] using hout

end GLang.PaperValueDomains
