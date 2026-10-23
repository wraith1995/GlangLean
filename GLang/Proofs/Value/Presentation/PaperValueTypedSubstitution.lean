import GLang.Proofs.Value.Binding.ValueSubstitution

/-! Beta typing for the original locally nameless value judgments. These
construct actual derivations for instantiated bodies from fresh named ones.
They are syntactic infrastructure, not semantic substitution assumptions. -/
namespace GLang

/-- A substitution fresh for every declared type leaves the context intact. -/
theorem ValCtx.substMap_eq_of_fresh (ε : ValCtx) (x : VName) (u : ValExpr)
    (h : ∀ y τ, ε.lookup y = some τ → x ∉ ValTy.fv τ) :
    ε.substMap x u = ε := by
  apply Finmap.ext_lookup
  intro y
  cases hy : ε.lookup y with
  | none => exact ValCtx.substMap_lookup_none x u ε y hy
  | some τ =>
      rw [ValCtx.substMap_lookup x u ε y τ hy, ValTy.subst_fresh x u τ (h y τ hy)]

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

/-- Original dependent type validity is preserved by beta instantiation. -/
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

/-- Original value typing is preserved by beta instantiation, including all
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

end GLang
