import GLang.Proofs.Value.Presentation.PaperValueRawMatchedCoherence
import GLang.Proofs.Value.Presentation.PaperValueMixedCodecs
import GLang.Proofs.Value.Presentation.PaperValueCoherentFamily

namespace GLang.PaperValueDomains
open ValueDependency DirectOracleReshape

/-- Two selected related arguments form a supported pairwise family. -/
private theorem reified_pair_family (d : ValTy) (ρ : Bool → ValEnvSem)
    (hc : ∀ i j, TypeCoherent directOracle d ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩)
    (a : (denotValTyS directOracle (ρ false) [] [] d).El)
    (b : (denotValTyS directOracle (ρ true) [] [] d).El)
    (hab : Related directOracle d ⟨ρ false, [], []⟩ ⟨ρ true, [], []⟩ a b) :
    let vs : Bool → ValValSem := fun i => match i with
      | false => ValValSem.fromEl (denotValTyS directOracle (ρ false) [] [] d) a
      | true => ValValSem.fromEl (denotValTyS directOracle (ρ true) [] [] d) b
    ∀ i j, RuntimeRelated directOracle d ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩ (vs i) (vs j) := by
  let laws := coherentFamily_laws directOracle d (fun i => (⟨ρ i, [], []⟩ : World)) hc
  have hba := related_symm directOracle d _ _ _ _ hab
  have haa := laws.trans false true false a b a hab hba
  have hbb := laws.trans true false true b a b hba hab
  intro vs i j
  cases i <;> cases j
  · exact reify_related directOracle d _ _ _ _ haa
  · exact reify_related directOracle d _ _ _ _ hab
  · exact reify_related directOracle d _ _ _ _ hba
  · exact reify_related directOracle d _ _ _ _ hbb

/-- Actual cofinite lambda step for the supported environment-family motive. -/
theorem raw_family_lambda_step (ε : ValCtx) (d c : ValTy) (body : ValExpr)
    (L : Finset VName) {k : ValKind} (hd : ValTValid ε d k) (hclosed : ValTy.lc d)
    (hbody : ∀ x, x ∉ L → ∀ {J : Type} (ρs : J → ValEnvSem),
      (∀ i j, RawMatchedContextRelated directOracle (Finmap.insert x d ε) (ρs i) (ρs j)
        (exprAnnotations (ValExpr.openVar x d body))) →
      ∀ i j, PartialRel (RuntimeRelated directOracle (ValTy.openVar x d c)
        ⟨ρs i, [], []⟩ ⟨ρs j, [], []⟩)
        (denotValB_semS directOracle (ρs i) [] [] (ValExpr.openVar x d body))
        (denotValB_semS directOracle (ρs j) [] [] (ValExpr.openVar x d body)))
    (ρ : Bool → ValEnvSem)
    (hctx : ∀ i j, RawMatchedContextRelated directOracle ε (ρ i) (ρ j)
      (exprAnnotations (.vlam d c body)))
    (hc : ∀ i j, RawTypeCoherent directOracle d ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩) :
    PartialRel (RuntimeRelated directOracle (.piTy d c) ⟨ρ false, [], []⟩ ⟨ρ true, [], []⟩)
      (denotValB_semS directOracle (ρ false) [] [] (.vlam d c body))
      (denotValB_semS directOracle (ρ true) [] [] (.vlam d c body)) := by
  apply eval_lambda_related
  intro a b hab
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (L ∪ ε.keys ∪ ε.fvSupport ∪ d.fv ∪ c.fv ∪ body.fv ∪ annotationSupport (exprAnnotations body))
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨⟨hxL, hxε⟩, hxSupport⟩, hxd⟩, hxc⟩, hxe⟩, hxAnn⟩ := hx
  let vs : Bool → ValValSem := fun i => match i with
    | false => ValValSem.fromEl (denotValTyS directOracle (ρ false) [] [] d) a
    | true => ValValSem.fromEl (denotValTyS directOracle (ρ true) [] [] d) b
  have hv := reified_pair_family d ρ (fun i j => (hc i j).toCoherent directOracle d _ _) a b hab
  have hctx' : ∀ i j, RawMatchedContextRelated directOracle (Finmap.insert x d ε)
      ((ρ i).update x (vs i)) ((ρ j).update x (vs j))
      (exprAnnotations (ValExpr.openVar x d body)) := by
    intro i j
    have hcb := (hctx i j).mono (xs := exprAnnotations body) (by
      intro q hq; simp only [exprAnnotations, List.mem_append]; exact Or.inr hq)
    have hcd := (hctx i j).coherent.mono (xs := typeAnnotations d) (by
      intro q hq; simp only [exprAnnotations, List.mem_append]; exact Or.inl (Or.inl hq))
    exact RawMatchedContextRelated.update_expr_open directOracle_spec.fvIrrel body hcb
      x d (vs i) (vs j) hd (by simpa only [Finmap.mem_keys] using hxε) hxSupport
      hcd (hc i j) (hv i j) hxe hxAnn hxd
  let W : OpenPushWorld directOracle :=
    { rho := ρ false, y := x, sigmaV := d, w := vs false, G := [], D := [],
      length_eq := rfl, sigma_lc := hclosed, y_sigma := hxd, y_G := by simp }
  let W' : OpenPushWorld directOracle :=
    { rho := ρ true, y := x, sigmaV := d, w := vs true, G := [], D := [],
      length_eq := rfl, sigma_lc := hclosed, y_sigma := hxd, y_G := by simp }
  have hopen := hbody x hxL (fun i => (ρ i).update x (vs i)) hctx' false true
  have hout := eval_related_openPush c body W W' rfl rfl hxc hxc hxe hxe hopen
  simpa only [W, W', OpenPushWorld.pushedWorld, OpenPushWorld.pushedRho,
    OpenPushWorld.pushedG, OpenPushWorld.pushedD, List.nil_append,
    World.push, World.denot, vs] using hout

/-- Actual dependent-pi coherence step for the supported family motive. -/
theorem raw_family_pi_step (ε : ValCtx) (d c : ValTy)
    (L : Finset VName) {k : ValKind} (hd : ValTValid ε d k) (hclosed : ValTy.lc d)
    (hcod : ∀ x, x ∉ L → ∀ {J : Type} (ρs : J → ValEnvSem),
      (∀ i j, RawMatchedContextRelated directOracle (Finmap.insert x d ε) (ρs i) (ρs j)
        (typeAnnotations (ValTy.openVar x d c))) →
      ∀ i j, RawTypeCoherent directOracle (ValTy.openVar x d c) ⟨ρs i, [], []⟩ ⟨ρs j, [], []⟩)
    (ρ : Bool → ValEnvSem)
    (hctx : ∀ i j, RawMatchedContextRelated directOracle ε (ρ i) (ρ j)
      (typeAnnotations (.piTy d c)))
    (hc : ∀ i j, RawTypeCoherent directOracle d ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩) :
    RawTypeCoherent directOracle (.piTy d c) ⟨ρ false, [], []⟩ ⟨ρ true, [], []⟩ := by
  refine ⟨hc false true, ?_⟩
  intro v v' hvv
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (L ∪ ε.keys ∪ ε.fvSupport ∪ d.fv ∪ c.fv ∪ annotationSupport (typeAnnotations c))
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨⟨⟨hxL, hxε⟩, hxSupport⟩, hxd⟩, hxc⟩, hxAnn⟩ := hx
  let vs : Bool → ValValSem := fun i => match i with | false => v | true => v'
  have hco := fun i j => (hc i j).toCoherent directOracle d _ _
  have hsym := runtime_related_symm directOracle d _ _ v v' hvv
  have hself0 := coherentFamily_runtime_trans directOracle d
    (fun i => (⟨ρ i, [], []⟩ : World)) hco false true false v v' v hvv hsym
  have hself1 := coherentFamily_runtime_trans directOracle d
    (fun i => (⟨ρ i, [], []⟩ : World)) hco true false true v' v v' hsym hvv
  have hv : ∀ i j, RuntimeRelated directOracle d ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩ (vs i) (vs j) := by
    intro i j
    cases i <;> cases j
    · exact hself0
    · exact hvv
    · exact hsym
    · exact hself1
  have hctx' : ∀ i j, RawMatchedContextRelated directOracle (Finmap.insert x d ε)
      ((ρ i).update x (vs i)) ((ρ j).update x (vs j))
      (typeAnnotations (ValTy.openVar x d c)) := by
    intro i j
    have hcb := (hctx i j).mono (xs := typeAnnotations c) (by
      intro q hq; simp only [typeAnnotations, List.mem_append]; exact Or.inr hq)
    have hcd := (hctx i j).coherent.mono (xs := typeAnnotations d) (by
      intro q hq; simp only [typeAnnotations, List.mem_append]; exact Or.inl hq)
    exact RawMatchedContextRelated.update_type_open directOracle_spec.fvIrrel c hcb
      x d (vs i) (vs j) hd (by simpa only [Finmap.mem_keys] using hxε) hxSupport
      hcd (hc i j) (hv i j) hxc hxAnn hxd
  let W : OpenPushWorld directOracle :=
    { rho := ρ false, y := x, sigmaV := d, w := vs false, G := [], D := [],
      length_eq := rfl, sigma_lc := hclosed, y_sigma := hxd, y_G := by simp }
  let W' : OpenPushWorld directOracle :=
    { rho := ρ true, y := x, sigmaV := d, w := vs true, G := [], D := [],
      length_eq := rfl, sigma_lc := hclosed, y_sigma := hxd, y_G := by simp }
  have hopen := hcod x hxL (fun i => (ρ i).update x (vs i)) hctx' false true
  have hout := rawCoherent_openPush c W W' rfl rfl hxc hxc hopen
  simpa only [W, W', OpenPushWorld.pushedWorld, OpenPushWorld.pushedRho,
    OpenPushWorld.pushedG, OpenPushWorld.pushedD, List.nil_append,
    World.rawPush, World.denot, vs] using hout

end GLang.PaperValueDomains
