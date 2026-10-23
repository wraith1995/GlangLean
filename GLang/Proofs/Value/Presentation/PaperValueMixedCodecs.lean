import GLang.Proofs.Value.Presentation.PaperValueCheckedExtensionality

/-! One-sided codec laws. The runtime representative may change on one side
without changing its behavior on supported inputs, including delayed errors. -/
namespace GLang.PaperValueDomains

private theorem resize_self {a : FlatArray} {n : Nat} (h : a.length = n) :
    a.resize n = a := by
  apply FlatArray.ext h.symm
  intro i
  simp [FlatArray.resize,FlatArray.ofFn,FlatArray.get,h]

theorem runtime_related_symm (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v') :
    RuntimeRelated orc τ w' w v' v := by
  cases τ with
  | space s =>
    cases v <;> cases v' <;> try exact h.elim
    exact related_symm orc _ _ _ _ _ h
  | piTy d c =>
    cases v <;> cases v' <;> try exact h.elim
    obtain ⟨hT,hU,hfg⟩ := h
    refine ⟨hU,hT,?_⟩
    intro a b hab
    exact PartialRel.symm (fun r s hrs => runtime_related_symm orc c _ _ r s hrs)
      (hfg b a (related_symm orc d _ _ _ _ hab))
termination_by sizeOf τ

theorem runtime_normalize_right (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v')
    (b : (w'.denot orc τ).El) (hb : ValValSem.toEl (w'.denot orc τ) v' = .ok b) :
    RuntimeRelated orc τ w w' v (ValValSem.fromEl (w'.denot orc τ) b) := by
  classical
  cases τ with
  | space s =>
    cases v <;> cases v' <;> try exact h.elim
    simp only [World.denot,denotValTyS,ValValSem.toEl,Except.ok.injEq] at hb
    subst b
    simp only [World.denot,denotValTyS,ValValSem.fromEl,resize_self h.2.2]
    exact h
  | piTy d c =>
    cases v <;> cases v' <;> try exact h.elim
    rename_i T f U g
    obtain ⟨hT,hU,hfg⟩ := h
    subst T; subst U
    simp only [World.denot,denotValTyS,ValValSem.toEl,dite_true,Except.ok.injEq] at hb
    subst b
    refine ⟨rfl,rfl,?_⟩
    intro a b hab
    have hout := hfg a b hab
    cases hf : f a <;> cases hg : g b <;> simp only [hf,hg,PartialRel] at hout
    · simp only [World.denot,denotValTyS,ValValSem.fromEl,hf,hg,Except.map,PartialRel]
    · rename_i r s
      obtain ⟨r',s',hr,hs,hrs⟩ := extract_related orc c _ _ r s hout
      have hn := runtime_normalize_right orc c _ _ r s hout s' hs
      simp only [World.denot,World.push] at hs
      simpa only [World.denot,World.push,denotValTyS,ValValSem.fromEl,
        hf,hg,hs,Except.map,PartialRel] using hn
termination_by sizeOf τ

theorem reify_mixed_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (a : (w.denot orc τ).El) (b : (w'.denot orc τ).El)
    (h : Related orc τ w w' a b) :
    PartialRel (RuntimeRelated orc τ w w')
      (.ok (ValValSem.fromEl (w.denot orc τ) a))
      (ValValSem.fromElChecked (w'.denot orc τ) b) := by
  cases τ with
  | space s =>
    simp only [World.denot,denotValTyS,ValValSem.fromEl,resize_self h.2.1,
      ValValSem.fromElChecked_space_of_length _ _ _ h.2.2,PartialRel]
    exact h
  | piTy d c =>
    refine ⟨rfl,rfl,?_⟩
    intro x y hxy
    have hout := h x y hxy
    cases hx : a x <;> cases hy : b y <;> simp only [hx,hy,PartialRel] at hout
    · simp only [ValValSem.fromEl,ValValSem.fromElChecked,hx,hy,Except.map,Except.bind,PartialRel]
    · simpa only [hx,hy,Except.map,Except.bind] using
        reify_mixed_related orc c _ _ _ _ hout
termination_by sizeOf τ

theorem runtime_normalize_left (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v')
    (a : (w.denot orc τ).El) (ha : ValValSem.toEl (w.denot orc τ) v = .ok a) :
    RuntimeRelated orc τ w w' (ValValSem.fromEl (w.denot orc τ) a) v' :=
  runtime_related_symm orc τ _ _ _ _
    (runtime_normalize_right orc τ _ _ v' v (runtime_related_symm orc τ _ _ _ _ h) a ha)

theorem runtime_normalize_domain_right (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v')
    (b : (w'.denot orc τ).El)
    (hb : ValValSem.toElDomainChecked (w'.denot orc τ) v' = .ok b) :
    RuntimeRelated orc τ w w' v (ValValSem.fromEl (w'.denot orc τ) b) := by
  apply runtime_normalize_right orc τ w w' v v' h b
  cases τ with
  | space s =>
    cases v <;> cases v' <;> try exact h.elim
    simpa only [World.denot,denotValTyS,ValValSem.toElDomainChecked,
      ValValSem.toElChecked_space_of_length _ _ _ h.2.2,ValValSem.toEl] using hb
  | piTy d c => exact hb

theorem EnvironmentsRelated.symm {orc : FFSOracleSem} {ε : ValCtx}
    {ρ ρ' : ValEnvSem} (h : EnvironmentsRelated orc ε ρ ρ') :
    EnvironmentsRelated orc ε ρ' ρ :=
  fun x τ hx => runtime_related_symm orc τ _ _ _ _ (h x τ hx)

end GLang.PaperValueDomains
