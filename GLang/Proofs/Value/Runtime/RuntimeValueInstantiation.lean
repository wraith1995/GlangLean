import GLang.Proofs.Value.Runtime.RuntimeValueSubstitution
import GLang.Proofs.Value.Presentation.PaperValueTypedSubstitution
import GLang.Proofs.Value.Runtime.RuntimeValueMatchedClosure

/-! Beta instantiation for the live value judgments. -/
namespace GLang.RuntimeValue

private theorem erase_insert_fresh (ε : ValCtx) (x : VName) (τ : ValTy)
    (hx : x ∉ ε) : (Finmap.insert x τ ε).erase x = ε := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : y = x
  · subst y
    simp only [Finmap.lookup_erase]
    exact (Finmap.lookup_eq_none.mpr hx).symm
  · rw [Finmap.lookup_erase_ne hy, Finmap.lookup_insert_of_ne _ hy]

/-- The existing substitution derivation data specialized to a fresh binder. -/
noncomputable def ValSubstData.of_fresh {ε : ValCtx} {x : VName} {u : ValExpr}
    {τ : ValTy} (hu : ValHasType ε u τ) (hlc : ValExpr.lc u)
    (hx : x ∉ ε) (hτ : x ∉ ValTy.fv τ)
    (hε : ∀ y σ, ε.lookup y = some σ → x ∉ ValTy.fv σ) :
    ValSubstData x u (Finmap.insert x τ ε) τ where
  lc := hlc
  xτ := by simp
  xfv := hτ
  argTyped := by
    rw [erase_insert_fresh ε x τ hx, ValCtx.substMap_eq_of_fresh ε x u hε]
    exact hu

/-- Runtime dependent type validity is preserved by beta instantiation. -/
noncomputable def ValTValid.instantiate_of_open {ε : ValCtx} {x : VName}
    {u : ValExpr} {d c : ValTy} {k : ValKind}
    (hu : ValHasType ε u d) (hlc : ValExpr.lc u)
    (hx : x ∉ ε) (hd : x ∉ ValTy.fv d) (hc : x ∉ ValTy.fv c)
    (hε : ∀ y σ, ε.lookup y = some σ → x ∉ ValTy.fv σ)
    (ht : ValTValid (Finmap.insert x d ε) (ValTy.openVar x d c) k) :
    ValTValid ε (ValTy.instantiate u c) k := by
  have h := ht.subst (ValSubstData.of_fresh hu hlc hx hd hε)
  rw [erase_insert_fresh ε x d hx, ValCtx.substMap_eq_of_fresh ε x u hε] at h
  simpa only [ValTy.instantiate, ValTy.openVar, ← ValTy.subst_intro x u d c hc 0] using h

/-- Runtime value typing is preserved by beta instantiation, including all
function-valued arguments and dependent result annotations. -/
noncomputable def ValHasType.instantiate_of_open {ε : ValCtx} {x : VName}
    {u body : ValExpr} {d c : ValTy}
    (hu : ValHasType ε u d) (hlc : ValExpr.lc u)
    (hx : x ∉ ε) (hd : x ∉ ValTy.fv d) (hc : x ∉ ValTy.fv c)
    (hb : x ∉ ValExpr.fv body)
    (hε : ∀ y σ, ε.lookup y = some σ → x ∉ ValTy.fv σ)
    (ht : ValHasType (Finmap.insert x d ε)
      (ValExpr.openVar x d body) (ValTy.openVar x d c)) :
    ValHasType ε (ValExpr.instantiate u body) (ValTy.instantiate u c) := by
  have h := ht.subst (ValSubstData.of_fresh hu hlc hx hd hε)
  rw [erase_insert_fresh ε x d hx, ValCtx.substMap_eq_of_fresh ε x u hε] at h
  simpa only [ValTy.instantiate, ValTy.openVar, ValExpr.instantiate, ValExpr.openVar,
    ← ValTy.subst_intro x u d c hc 0, ← ValExpr.subst_intro x u d body hb 0] using h

/-- The substituted codomain is valid under the original context. The local
closure and fresh-name conditions follow from context validity. -/
noncomputable def ValTValid.instantiate {ε : ValCtx} {u : ValExpr}
    {d c : ValTy} {kd kc : ValKind}
    (hctx : ValCtxValid ε) (hu : ValHasType ε u d)
    (hpi : ValTValid ε (.piTy d c) (.arrow kd kc)) :
    ValTValid ε (ValTy.instantiate u c) kc := by
  cases hpi with
  | piTy L hd hb =>
    let avoid := L ∪ ε.keys ∪ ε.fvSupport ∪ d.fv ∪ c.fv
    let x := Classical.choose (Infinite.exists_notMem_finset avoid)
    have hx := Classical.choose_spec (Infinite.exists_notMem_finset avoid)
    change x ∉ avoid at hx
    simp only [avoid, Finset.mem_union, not_or] at hx
    obtain ⟨⟨⟨⟨hxL, hxK⟩, hxS⟩, hxD⟩, hxC⟩ := hx
    exact ValTValid.instantiate_of_open hu (validExpr_lc hctx hu).1
      (fun hm => hxK (Finmap.mem_keys.mpr hm)) hxD hxC
      (fun _ _ hl => ValCtx.not_mem_fv_of_not_mem_support hxS hl) (hb x hxL)

/-- A converted argument can instantiate the dependent result type even when
its original value type is an independent realization of the input space. -/
noncomputable def ValTValid.instantiate_reshaped {ε : ValCtx} {u : ValExpr}
    {a d c : ValTy} {kd kc : ValKind}
    (hctx : ValCtxValid ε) (hu : ValHasType ε u a)
    (ha : ValTValid ε a kd) (hd : ValTValid ε d kd)
    (hpi : ValTValid ε (.piTy d c) (.arrow kd kc)) :
    ValTValid ε (ValTy.instantiate (.reshap u d a) c) kc :=
  hpi.instantiate hctx (.reshap hu ha hd)

/-- Form the result type used by the binary application rule. -/
noncomputable def ValTValid.applyCodomain {ε : ValCtx} {u : ValExpr}
    {d c : ValTy} {kd kc : ValKind}
    (hpi : ValTValid ε (.piTy d c) (.arrow kd kc))
    (hctx : ValCtxValid ε) (hu : ValHasType ε u d) :
    ValTValid ε (ValTy.applyCodomain u c) kc := by
  rw [ValTy.applyCodomain_eq_instantiate (validType_lc hctx hpi)
    (validExpr_lc hctx hu).1]
  exact hpi.instantiate hctx hu

end GLang.RuntimeValue
