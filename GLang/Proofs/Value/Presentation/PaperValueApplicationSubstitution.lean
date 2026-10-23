import GLang.Proofs.Value.Presentation.PaperValueRawCoherence
import GLang.Proofs.Value.Presentation.PaperValueNamedSubstitution
import GLang.Proofs.Value.Presentation.PaperValueMixedCodecs

namespace GLang.PaperValueDomains

private noncomputable def applicationArg (orc : FFSOracleSem) (d : ValTy) {I : Type u_1}
    (w : I → World) (v : I → ValValSem) (a : ∀ i, (w i |>.denot orc d).El)
    (p : I × Bool) : ValValSem :=
  if p.2 then ValValSem.fromEl (w p.1 |>.denot orc d) (a p.1) else v p.1

/-- All combinations of raw and decoded/reified arguments remain related.
Neither a callback equality nor equality on malformed inputs is asserted. -/
theorem applicationArg_related (orc : FFSOracleSem) (d : ValTy) {I : Type u_1}
    (w : I → World) (v : I → ValValSem) (a : ∀ i, (w i |>.denot orc d).El)
    (hv : ∀ i j, RuntimeRelated orc d (w i) (w j) (v i) (v j))
    (ha : ∀ i, ValValSem.toElDomainChecked (w i |>.denot orc d) (v i) = .ok (a i))
    (p q : I × Bool) :
    RuntimeRelated orc d (w p.1) (w q.1)
      (applicationArg orc d w v a p) (applicationArg orc d w v a q) := by
  rcases p with ⟨i,bi⟩
  rcases q with ⟨j,bj⟩
  cases bi <;> cases bj <;> simp only [applicationArg, Bool.false_eq_true, ↓reduceIte]
  · exact hv i j
  · exact runtime_normalize_domain_right orc d _ _ _ _ (hv i j) (a j) (ha j)
  · exact runtime_related_symm orc d _ _ _ _
      (runtime_normalize_domain_right orc d _ _ _ _ (hv j i) (a i) (ha i))
  · exact runtime_normalize_domain_right orc d _ _ _ _
      (runtime_related_symm orc d _ _ _ _
        (runtime_normalize_domain_right orc d _ _ _ _ (hv j i) (a i) (ha i)))
      (a j) (ha j)

/-- The genuine dependent application substitution step. Original exact
substitution handles raw argument evaluation; local formation coherence moves
between the raw binding and the decoded/reified function-argument fibre. -/
theorem original_application_substitution {ε : ValCtx} {d c : ValTy} {k : ValKind}
    {u : ValExpr} (hpi : ValTValid ε (.piTy d c) k) (hu : ValHasType ε u d)
    (hctx : ContextLocallyClosed ε) (hvalid : ValCtxValid ε) {I : Type u_1} (ρ : I → ValEnvSem)
    (v : I → ValValSem) (a : ∀ i, (World.mk (ρ i) [] [] |>.denot directOracle d).El)
    (he : ∀ i, denotValB_semS directOracle (ρ i) [] [] u = .ok (v i))
    (ha : ∀ i, ValValSem.toElDomainChecked
      (World.mk (ρ i) [] [] |>.denot directOracle d) (v i) = .ok (a i))
    (hv : ∀ i j, RuntimeRelated directOracle d ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩ (v i) (v j))
    (hc : ∀ i j, RawTypeCoherent directOracle (.piTy d c) ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
    (i j : I) (r r' : ValValSem)
    (hr : RuntimeRelated directOracle c
      ((World.mk (ρ i) [] []).push directOracle d (a i))
      ((World.mk (ρ j) [] []).push directOracle d (a j)) r r') :
    RuntimeRelated directOracle (ValTy.instantiate u c) ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩ r r' := by
  let w : I → World := fun i => ⟨ρ i,[],[]⟩
  let args := applicationArg directOracle d w v a
  let worlds : I × Bool → World := fun p => (w p.1).rawPush d (args p)
  have hworlds : ∀ p q, TypeCoherent directOracle c (worlds p) (worlds q) := by
    intro p q
    exact ((hc p.1 q.1).2 (args p) (args q)
      (applicationArg_related directOracle d w v a hv ha p q)).toCoherent directOracle c _ _
  have hraw : RuntimeRelated directOracle c ⟨ρ i,[d],[v i]⟩ ⟨ρ j,[d],[v j]⟩ r r' :=
    coherentFamily_runtime_transport directOracle c worlds hworlds
      (i,true) (j,true) (i,false) (j,false) r r' hr
  have hi := original_type_instantiation hpi hu hctx hvalid (ρ i) (v i) (he i)
  have hj := original_type_instantiation hpi hu hctx hvalid (ρ j) (v j) (he j)
  have hp := TypePresentation.pair directOracle c (ValTy.instantiate u c)
    (hi.sameShape directOracle _ _ _ _) _ _ _ _
    (hi.toPresentation directOracle _ _ _ _) (hj.toPresentation directOracle _ _ _ _)
  exact runtime_presentation_transport directOracle c (ValTy.instantiate u c)
    (hi.sameShape directOracle _ _ _ _) _ _ _ _ hp r r' hraw

/-- Complete original application arm for a supported family. Every premise is
an ordinary operand/formation IH or an original typing/context judgment. -/
theorem original_application_family {ε : ValCtx} {ef ea : ValExpr} {d c : ValTy}
    {k : ValKind} (hf : ValHasType ε ef (.piTy d c)) (ha : ValHasType ε ea d)
    (hpi : ValTValid ε (.piTy d c) k) (hctx : ContextLocallyClosed ε) (hvalid : ValCtxValid ε)
    {I : Type u_1} (ρ : I → ValEnvSem)
    (ihf : ∀ i j, PartialRel (RuntimeRelated directOracle (.piTy d c)
      ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
      (denotValB_semS directOracle (ρ i) [] [] ef)
      (denotValB_semS directOracle (ρ j) [] [] ef))
    (iha : ∀ i j, PartialRel (RuntimeRelated directOracle d ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
      (denotValB_semS directOracle (ρ i) [] [] ea)
      (denotValB_semS directOracle (ρ j) [] [] ea))
    (hc : ∀ i j, RawTypeCoherent directOracle (.piTy d c) ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
    (i j : I) :
    PartialRel (RuntimeRelated directOracle (ValTy.instantiate ea c)
      ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
      (denotValB_semS directOracle (ρ i) [] [] (.appV ef ea))
      (denotValB_semS directOracle (ρ j) [] [] (.appV ef ea)) := by
  apply original_application_step hf ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩ (ihf i j) (iha i j)
  intro v v' a b he he' hd hd' _ r r' hr
  let ix : Bool → I := fun t => if t then j else i
  let vals : Bool → ValValSem := fun t => if t then v' else v
  let dec : ∀ t : Bool, (World.mk (ρ (ix t)) [] [] |>.denot directOracle d).El :=
    fun t => match t with | false => a | true => b
  have hev : ∀ t, denotValB_semS directOracle (ρ (ix t)) [] [] ea = .ok (vals t) := by
    intro t; cases t
    · exact he
    · exact he'
  have hdec : ∀ t, ValValSem.toElDomainChecked
      (World.mk (ρ (ix t)) [] [] |>.denot directOracle d) (vals t) = .ok (dec t) := by
    intro t; cases t
    · exact hd
    · exact hd'
  have hvals : ∀ t t', RuntimeRelated directOracle d
      ⟨ρ (ix t),[],[]⟩ ⟨ρ (ix t'),[],[]⟩ (vals t) (vals t') := by
    intro t t'
    have ht := iha (ix t) (ix t')
    simpa only [hev t, hev t', PartialRel] using ht
  exact original_application_substitution hpi ha hctx hvalid (fun t => ρ (ix t)) vals dec
    hev hdec hvals (fun t t' => hc (ix t) (ix t')) false true r r' hr

end GLang.PaperValueDomains
