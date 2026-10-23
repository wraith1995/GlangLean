import GLang.Proofs.Value.Runtime.RuntimeValueMatchedCoherence
import GLang.Proofs.Value.Partial.PartialValueRuntimeCoherence

/-! Cofinite lambda and dependent-type cases for the original partial
value-language logical-relations induction. -/
namespace GLang.RuntimeValue
open PartialValueDomains
open PaperValueDomains ValueDependency

noncomputable abbrev WorldRuntimeRelated (orc : PartialFFSOracleSem) (t : ValTy)
    (w w' : World) := PartialRuntimeRelated t (PartialWorldType orc w t) (PartialWorldType orc w' t)

private theorem eval_lambda_related (orc : PartialFFSOracleSem) (w w' : World)
    (d c : ValTy) (body : ValExpr)
    (hd : PartialCoherent d (PartialWorldType orc w d) (PartialWorldType orc w' d))
    (hb : ∀ a b, PartialRelated d (PartialWorldType orc w d) (PartialWorldType orc w' d) a b →
      PartialRel (WorldRuntimeRelated orc c
        ⟨w.env,d::w.types,d.carrierToVal a::w.values⟩
        ⟨w'.env,d::w'.types,d.carrierToVal b::w'.values⟩)
        (denotValB_partial orc w.env (d::w.types) (d.carrierToVal a::w.values) body)
        (denotValB_partial orc w'.env (d::w'.types) (d.carrierToVal b::w'.values) body)) :
    PartialRel (WorldRuntimeRelated orc (.piTy d c) w w')
      (denotValB_partial orc w.env w.types w.values (.vlam d c body))
      (denotValB_partial orc w'.env w'.types w'.values (.vlam d c body)) := by
  simp only [denotValB_partial,WorldRuntimeRelated,PartialWorldType,denotValTyPartial]
  cases hD : denotValTyPartial orc w.env w.types w.values d <;>
    cases hE : denotValTyPartial orc w'.env w'.types w'.values d
  · trivial
  · simp only [PartialWorldType,hD,hE] at hd
    cases d <;> exact False.elim hd
  · simp only [PartialWorldType,hD,hE] at hd
    cases d <;> exact False.elim hd
  · refine ⟨rfl,rfl,?_⟩
    intro a b hab
    apply hb a b
    simpa only [PartialWorldType,hD,hE] using hab

private theorem eval_related_openPush (t : ValTy) (e : ValExpr)
    (W W' : PartialDirectOpenPush.World PartialDirectOracle.oracle)
    (hG : W.G = W'.G) (hu : W.u = W'.u)
    (ht : W.y ∉ t.fv) (ht' : W'.y ∉ t.fv) (he : W.y ∉ e.fv) (he' : W'.y ∉ e.fv)
    (h : PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle
      (ValTy.openRec W.G.length W.u t)
      ⟨W.namedRho,W.namedG,W.namedD⟩ ⟨W'.namedRho,W'.namedG,W'.namedD⟩)
      (denotValB_partial PartialDirectOracle.oracle W.namedRho W.namedG W.namedD
        (ValExpr.openRec W.G.length W.u e))
      (denotValB_partial PartialDirectOracle.oracle W'.namedRho W'.namedG W'.namedD
        (ValExpr.openRec W.G.length W.u e))) :
    PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle t
      ⟨W.pushedRho,W.pushedG,W.pushedD⟩ ⟨W'.pushedRho,W'.pushedG,W'.pushedD⟩)
      (denotValB_partial PartialDirectOracle.oracle W.pushedRho W.pushedG W.pushedD e)
      (denotValB_partial PartialDirectOracle.oracle W'.pushedRho W'.pushedG W'.pushedD e) := by
  have hT := PartialDirectOpenPush.type_heq PartialDirectOpenPush.oracle_openPush t W ht
  have hT' := PartialDirectOpenPush.type_heq PartialDirectOpenPush.oracle_openPush t W' ht'
  rw [← hG,← hu] at hT'
  have hleft := PartialDirectOpenPush.eval_openPush W.rho W.y W.sigmaV W.w W.G W.D e
    W.length_eq W.sigma_lc W.y_sigma W.y_G he
  have hright := PartialDirectOpenPush.eval_openPush W'.rho W'.y W'.sigmaV W'.w W'.G W'.D e
    W'.length_eq W'.sigma_lc W'.y_sigma W'.y_G he'
  change denotValB_partial _ W.namedRho W.namedG W.namedD
    (ValExpr.openRec W.G.length W.u e) = _ at hleft
  change denotValB_partial _ W'.namedRho W'.namedG W'.namedD
    (ValExpr.openRec W'.G.length W'.u e) = _ at hright
  have hright' : denotValB_partial PartialDirectOracle.oracle W'.namedRho W'.namedG W'.namedD
      (ValExpr.openRec W.G.length W.u e) =
      denotValB_partial PartialDirectOracle.oracle W'.pushedRho W'.pushedG W'.pushedD e := by
    simpa only [hG,hu] using hright
  rw [hleft,hright'] at h
  change PartialRel _ (denotValB_partial PartialDirectOracle.oracle W.pushedRho W.pushedG W.pushedD e)
    (denotValB_partial PartialDirectOracle.oracle W'.pushedRho W'.pushedG W'.pushedD e) at h
  cases hl : denotValB_partial PartialDirectOracle.oracle W.pushedRho W.pushedG W.pushedD e <;>
    cases hr : denotValB_partial PartialDirectOracle.oracle W'.pushedRho W'.pushedG W'.pushedD e <;>
    simp only [hl,hr,PartialRel] at h ⊢
  exact (partialRuntimeRelated_heq (ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u t)
    _ _ _ _ hT hT' _ _).1 h

/-- Original cofinite lambda introduction, using the original body induction
hypothesis and the concrete partial evaluator's proved binder bridge. -/
theorem partial_family_lambda_step (ε : ValCtx) (d c : ValTy) (body : ValExpr)
    (L : Finset VName) {k : ValKind} (hd : ValTValid ε d k) (hclosed : ValTy.lc d)
    (hbody : ∀ x, x ∉ L → ∀ {J : Type} (ρs : J → ValEnvSem),
      (∀ i j, RawMatchedContextRelated PartialDirectOracle.oracle (Finmap.insert x d ε) (ρs i) (ρs j)
        (exprAnnotations (ValExpr.openVar x d body))) →
      ∀ i j, PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle (ValTy.openVar x d c)
        ⟨ρs i,[],[]⟩ ⟨ρs j,[],[]⟩)
        (denotValB_partial PartialDirectOracle.oracle (ρs i) [] [] (ValExpr.openVar x d body))
        (denotValB_partial PartialDirectOracle.oracle (ρs j) [] [] (ValExpr.openVar x d body)))
    (ρ : Bool → ValEnvSem)
    (hctx : ∀ i j, RawMatchedContextRelated PartialDirectOracle.oracle ε (ρ i) (ρ j)
      (exprAnnotations (.vlam d c body)))
    (hc : ∀ i j, PartialRawTypeCoherent PartialDirectOracle.oracle d ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩) :
    PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle (.piTy d c) ⟨ρ false,[],[]⟩ ⟨ρ true,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle (ρ false) [] [] (.vlam d c body))
      (denotValB_partial PartialDirectOracle.oracle (ρ true) [] [] (.vlam d c body)) := by
  apply eval_lambda_related _ _ _ d c body (hc false true |>.toCoherent _ _ _ _)
  intro a b hab
  obtain ⟨x,hx⟩ := Infinite.exists_notMem_finset
    (L ∪ ε.keys ∪ ε.fvSupport ∪ d.fv ∪ c.fv ∪ body.fv ∪ annotationSupport (exprAnnotations body))
  simp only [Finset.mem_union,not_or] at hx
  obtain ⟨⟨⟨⟨⟨⟨hxL,hxε⟩,hxSupport⟩,hxd⟩,hxc⟩,hxe⟩,hxAnn⟩ := hx
  let vs : Bool → ValValSem := fun i => if i then d.carrierToVal b else d.carrierToVal a
  let Ts := fun i => PartialWorldType PartialDirectOracle.oracle ⟨ρ i,[],[]⟩ d
  have laws := partialFamily_laws d Ts (fun i j => (hc i j).toCoherent _ _ _ _)
  have hba := partialRelated_symm d _ _ a b hab
  have haa := laws.trans false true false a b a hab hba
  have hbb := laws.trans true false true b a b hba hab
  have hv : ∀ i j, WorldRuntimeRelated PartialDirectOracle.oracle d ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩ (vs i) (vs j) := by
    intro i j
    cases i <;> cases j
    · exact partial_reify_related d _ _ a a haa
    · exact partial_reify_related d _ _ a b hab
    · exact partial_reify_related d _ _ b a hba
    · exact partial_reify_related d _ _ b b hbb
  have hctx' : ∀ i j, RawMatchedContextRelated PartialDirectOracle.oracle (Finmap.insert x d ε)
      ((ρ i).update x (vs i)) ((ρ j).update x (vs j))
      (exprAnnotations (ValExpr.openVar x d body)) := by
    intro i j
    have hcb := (hctx i j).mono (xs := exprAnnotations body) (by
      intro q hq; simp only [exprAnnotations,List.mem_append]; exact Or.inr hq)
    have hcd := (hctx i j).coherent.mono (xs := typeAnnotations d) (by
      intro q hq; simp only [exprAnnotations,List.mem_append]; exact Or.inl (Or.inl hq))
    exact RawMatchedContextRelated.update_expr_open PartialDirectFv.oracle_fresh body hcb
      x d (vs i) (vs j) hd (by simpa only [Finmap.mem_keys] using hxε) hxSupport
      hcd (hc i j) (hv i j) hxe hxAnn hxd
  let W : PartialDirectOpenPush.World PartialDirectOracle.oracle :=
    ⟨ρ false,x,d,vs false,[],[],rfl,hclosed,hxd,by simp⟩
  let W' : PartialDirectOpenPush.World PartialDirectOracle.oracle :=
    ⟨ρ true,x,d,vs true,[],[],rfl,hclosed,hxd,by simp⟩
  have hopen := hbody x hxL (fun i => (ρ i).update x (vs i)) hctx' false true
  have hout := eval_related_openPush c body W W' rfl rfl hxc hxc hxe hxe hopen
  simpa only [W,W',PartialDirectOpenPush.World.pushedRho,PartialDirectOpenPush.World.pushedG,
    PartialDirectOpenPush.World.pushedD,List.nil_append,vs,Bool.false_eq_true,↓reduceIte] using hout

theorem partial_family_pi_step (ε : ValCtx) (d c : ValTy)
    (L : Finset VName) {k : ValKind} (hd : ValTValid ε d k) (hclosed : ValTy.lc d)
    (hcod : ∀ x, x ∉ L → ∀ {J : Type} (ρs : J → ValEnvSem),
      (∀ i j, RawMatchedContextRelated PartialDirectOracle.oracle (Finmap.insert x d ε) (ρs i) (ρs j)
        (typeAnnotations (ValTy.openVar x d c))) →
      ∀ i j, PartialRawTypeCoherent PartialDirectOracle.oracle (ValTy.openVar x d c) ⟨ρs i, [], []⟩ ⟨ρs j, [], []⟩)
    (ρ : Bool → ValEnvSem)
    (hctx : ∀ i j, RawMatchedContextRelated PartialDirectOracle.oracle ε (ρ i) (ρ j)
      (typeAnnotations (.piTy d c)))
    (hc : ∀ i j, PartialRawTypeCoherent PartialDirectOracle.oracle d ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩) :
    PartialRawTypeCoherent PartialDirectOracle.oracle (.piTy d c) ⟨ρ false, [], []⟩ ⟨ρ true, [], []⟩ := by
  refine ⟨hc false true, ?_⟩
  intro v v' hvv
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (L ∪ ε.keys ∪ ε.fvSupport ∪ d.fv ∪ c.fv ∪ annotationSupport (typeAnnotations c))
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨hxL, hxε⟩, hxSupport⟩, hxd⟩, hxc⟩, hxAnn⟩ := hx
  let vs : Bool → ValValSem := fun i => match i with | false => v | true => v'
  have hco := fun i j => (hc i j).toCoherent PartialDirectOracle.oracle d _ _
  have hsym := partialRuntimeRelated_symm d _ _ v v' hvv
  have hself0 := partialRuntime_family_trans d
    (fun i => PartialWorldType PartialDirectOracle.oracle ⟨ρ i,[],[]⟩ d) hco false true false v v' v hvv hsym
  have hself1 := partialRuntime_family_trans d
    (fun i => PartialWorldType PartialDirectOracle.oracle ⟨ρ i,[],[]⟩ d) hco true false true v' v v' hsym hvv
  have hv : ∀ i j, WorldRuntimeRelated PartialDirectOracle.oracle d ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩ (vs i) (vs j) := by
    intro i j
    cases i <;> cases j
    · exact hself0
    · exact hvv
    · exact hsym
    · exact hself1
  have hctx' : ∀ i j, RawMatchedContextRelated PartialDirectOracle.oracle (Finmap.insert x d ε)
      ((ρ i).update x (vs i)) ((ρ j).update x (vs j))
      (typeAnnotations (ValTy.openVar x d c)) := by
    intro i j
    have hcb := (hctx i j).mono (xs := typeAnnotations c) (by
      intro q hq; simp only [typeAnnotations, List.mem_append]; exact Or.inr hq)
    have hcd := (hctx i j).coherent.mono (xs := typeAnnotations d) (by
      intro q hq; simp only [typeAnnotations, List.mem_append]; exact Or.inl hq)
    exact RawMatchedContextRelated.update_type_open PartialDirectFv.oracle_fresh c hcb
      x d (vs i) (vs j) hd (by simpa only [Finmap.mem_keys] using hxε) hxSupport
      hcd (hc i j) (hv i j) hxc hxAnn hxd
  let W : PartialDirectOpenPush.World PartialDirectOracle.oracle :=
    { rho := ρ false, y := x, sigmaV := d, w := vs false, G := [], D := [],
      length_eq := rfl, sigma_lc := hclosed, y_sigma := hxd, y_G := by simp }
  let W' : PartialDirectOpenPush.World PartialDirectOracle.oracle :=
    { rho := ρ true, y := x, sigmaV := d, w := vs true, G := [], D := [],
      length_eq := rfl, sigma_lc := hclosed, y_sigma := hxd, y_G := by simp }
  have hopen := hcod x hxL (fun i => (ρ i).update x (vs i)) hctx' false true
  have hout := PartialRawTypeCoherent.openPush c W W' rfl rfl hxc hxc hopen
  simpa only [W, W', PartialDirectOpenPush.World.pushedRho,
    PartialDirectOpenPush.World.pushedG, PartialDirectOpenPush.World.pushedD, List.nil_append,
    vs] using hout

end GLang.RuntimeValue
