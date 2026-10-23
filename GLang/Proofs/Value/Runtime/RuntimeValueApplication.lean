import GLang.Proofs.Value.Runtime.RuntimeValueFamilyBinders
import GLang.Proofs.Value.Runtime.RuntimeValueSemanticSubstitution
import GLang.Proofs.Value.Partial.PartialValueRuntimeChecks
import GLang.Proofs.Value.Partial.PartialValueApplicationTransport

namespace GLang.RuntimeValue
open PartialValueDomains
open PaperValueDomains

private noncomputable def applicationArg (d : ValTy) {I : Type}
    (v : I → ValValSem) (a : I → d.carrierEl) (p : I × Bool) : ValValSem :=
  if p.2 then d.carrierToVal (a p.1) else v p.1

private theorem applicationArg_related (d : ValTy) {I : Type}
    (T : I → Except DimError (PartialValType d))
    (hc : ∀ i j, PartialCoherent d (T i) (T j))
    (v : I → ValValSem) (a : I → d.carrierEl)
    (hv : ∀ i j, PartialRuntimeRelated d (T i) (T j) (v i) (v j))
    (ha : ∀ i, validate (T i) ((Except.ok (v i)).bind d.carrierFromVal) = .ok (a i))
    (p q : I × Bool) :
    PartialRuntimeRelated d (T p.1) (T q.1)
      (applicationArg d v a p) (applicationArg d v a q) := by
  have mix : ∀ i j, PartialRuntimeRelated d (T i) (T j) (v i) (d.carrierToVal (a j)) := by
    intro i j
    obtain ⟨ai,bj,hai,hbj,hab⟩ := partial_extract_related d _ _ _ _ (hv i j)
    have hvcheck := validate_related_right d (T i) (T j) (hc i j) (.ok ai) (.ok bj) hab
    have haj := ha j
    simp only [Except.bind, hbj] at haj
    rw [haj] at hvcheck
    exact partialRuntime_family_trans d T hc i i j _ _ _
      (partialRuntime_normalize_right d _ _ _ _ (hv i i) ai hai)
      (partial_reify_related d _ _ ai (a j) hvcheck)
  have checks : ∀ i j, PartialRuntimeRelated d (T i) (T j)
      (d.carrierToVal (a i)) (d.carrierToVal (a j)) := by
    intro i j
    exact partialRuntime_family_trans d T hc i i j _ _ _
      (partialRuntimeRelated_symm d _ _ _ _ (mix i i)) (mix i j)
  rcases p with ⟨i,bi⟩; rcases q with ⟨j,bj⟩
  cases bi <;> cases bj <;> simp only [applicationArg,Bool.false_eq_true,↓reduceIte]
  · exact hv i j
  · exact mix i j
  · exact partialRuntimeRelated_symm d _ _ _ _ (mix j i)
  · exact checks i j

/-- Original dependent application: raw substitution and recursive coherence
identify the actual raw argument with its structural representative. -/
theorem partial_original_application_substitution {ε : ValCtx} {d c : ValTy} {k : ValKind}
    {u : ValExpr} (hpi : ValTValid ε (.piTy d c) k) (hu : ValHasType ε u d)
    (hctx : ContextLocallyClosed ε) (hvalid : ValCtxValid ε) {I : Type} (ρ : I → ValEnvSem)
    (v : I → ValValSem) (a : I → d.carrierEl)
    (he : ∀ i, denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] u = .ok (v i))
    (ha : ∀ i, PartialValueEval.checkResult PartialDirectOracle.oracle (ρ i) [] [] d (.ok (v i)) = .ok (a i))
    (hv : ∀ i j, WorldRuntimeRelated PartialDirectOracle.oracle d ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩ (v i) (v j))
    (hc : ∀ i j, PartialRawTypeCoherent PartialDirectOracle.oracle (.piTy d c) ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
    (i j : I) (r r' : ValValSem)
    (hr : WorldRuntimeRelated PartialDirectOracle.oracle c
      ⟨ρ i,[d],[d.carrierToVal (a i)]⟩ ⟨ρ j,[d],[d.carrierToVal (a j)]⟩ r r') :
    WorldRuntimeRelated PartialDirectOracle.oracle (ValTy.instantiate u c) ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩ r r' := by
  let args := applicationArg d v a
  let worlds : I × Bool → World := fun p => ⟨ρ p.1,[d],[args p]⟩
  have hworlds : ∀ p q, PartialCoherent c
      (PartialWorldType PartialDirectOracle.oracle (worlds p) c)
      (PartialWorldType PartialDirectOracle.oracle (worlds q) c) := by
    intro p q
    exact ((hc p.1 q.1).2 (args p) (args q)
      (applicationArg_related d (fun i => PartialWorldType PartialDirectOracle.oracle ⟨ρ i,[],[]⟩ d)
        (fun i j => ((hc i j).1).toCoherent _ _ _ _) v a hv
        (fun i => by rw [← PartialValueEval.checkResult_eq_validate]; exact ha i) p q)).toCoherent _ _ _ _
  have hraw : WorldRuntimeRelated PartialDirectOracle.oracle c ⟨ρ i,[d],[v i]⟩ ⟨ρ j,[d],[v j]⟩ r r' :=
    partialRuntime_family_transport c (fun p => PartialWorldType PartialDirectOracle.oracle (worlds p) c)
      hworlds (i,true) (j,true) (i,false) (j,false) r r' hr
  have hi := NamedSubstitution.partial_original_type_instantiation hpi hu hctx hvalid (ρ i) (v i) (he i)
  have hj := NamedSubstitution.partial_original_type_instantiation hpi hu hctx hvalid (ρ j) (v j) (he j)
  exact (partialRuntimeRelated_heq (ValSoundOfDenot.ValTy.SameShape_openRec 0 u c)
    _ _ _ _ hi hj r r').2 hraw

/-- The original application constructor preserves the full raw recursive
relation for arbitrary supported families. -/
theorem partial_original_application_family {ε : ValCtx} {ef ea : ValExpr} {d c : ValTy}
    {k : ValKind} (hf : ValHasType ε ef (.piTy d c)) (ha : ValHasType ε ea d)
    (hpi : ValTValid ε (.piTy d c) k) (hctx : ContextLocallyClosed ε) (hvalid : ValCtxValid ε)
    {I : Type} (ρ : I → ValEnvSem)
    (ihf : ∀ i j, PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle (.piTy d c)
      ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] ef)
      (denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] ef))
    (iha : ∀ i j, PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle d ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] ea)
      (denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] ea))
    (hc : ∀ i j, PartialRawTypeCoherent PartialDirectOracle.oracle (.piTy d c) ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
    (hout : ∀ i j, PartialRawTypeCoherent PartialDirectOracle.oracle (ValTy.instantiate ea c) ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
    (i j : I) :
    PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle (ValTy.instantiate ea c)
      ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] (.appV ef ea))
      (denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] (.appV ef ea)) := by
  have hfr := ihf i j
  have har := iha i j
  simp only [denotValB_partial, ValExpr.inferTypeCtx_eq_of_typed hf]
  cases hfi : denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] ef <;>
    cases hfj : denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] ef <;>
    simp only [hfi,hfj,PartialRel] at hfr
  · simp only [PartialValueEval.applyDomainChecked,PartialRel]
  rename_i fi fj
  cases hai : denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] ea <;>
    cases haj : denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] ea <;>
    simp only [hai,haj,PartialRel] at har
  · simp only [PartialValueEval.applyDomainChecked,PartialValueEval.checkResult,Except.bind,PartialRel]
  rename_i ai aj
  have hcargs := PartialValueEval.checkResult_related PartialDirectOracle.oracle
    (ρ i) (ρ j) [] [] [] [] d (.ok ai) (.ok aj)
    ((hc i j).1.toCoherent _ _ _ _) har
  simp only [PartialValueEval.applyDomainChecked]
  cases hci : PartialValueEval.checkResult PartialDirectOracle.oracle (ρ i) [] [] d (.ok ai) <;>
    cases hcj : PartialValueEval.checkResult PartialDirectOracle.oracle (ρ j) [] [] d (.ok aj) <;>
    simp only [hci,hcj,PartialRel,Except.bind] at hcargs ⊢
  rename_i xi xj
  have happ := partial_apply_runtime_related PartialDirectOracle.oracle d c
    ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩ fi fj hfr xi xj hcargs
  cases hri : fi.applyTyped xi <;> cases hrj : fj.applyTyped xj <;>
    simp only [hri,hrj,PartialRel] at happ ⊢
  rename_i ri rj
  let pick : Bool → I := fun b => if b then j else i
  let values : Bool → ValValSem := fun b => if b then aj else ai
  let decoded : Bool → d.carrierEl := fun b => if b then xj else xi
  have he : ∀ b, denotValB_partial PartialDirectOracle.oracle (ρ (pick b)) [] [] ea = .ok (values b) := by
    intro b; cases b
    · exact hai
    · exact haj
  have hcheck : ∀ b, PartialValueEval.checkResult PartialDirectOracle.oracle
      (ρ (pick b)) [] [] d (.ok (values b)) = .ok (decoded b) := by
    intro b; cases b
    · exact hci
    · exact hcj
  have hv : ∀ b b', WorldRuntimeRelated PartialDirectOracle.oracle d
      ⟨ρ (pick b),[],[]⟩ ⟨ρ (pick b'),[],[]⟩ (values b) (values b') := by
    intro b b'
    have h := iha (pick b) (pick b')
    simpa only [he b,he b',PartialRel] using h
  exact partial_original_application_substitution hpi ha hctx hvalid (fun b => ρ (pick b))
    values decoded he hcheck hv (fun b b' => hc (pick b) (pick b')) false true ri rj happ

end GLang.RuntimeValue
