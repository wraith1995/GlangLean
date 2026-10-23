import GLang.Value.Supporting.StrictTyping
import GLang.Proofs.Value.Binding.ValueLN
import GLang.Proofs.Value.Binding.ValueBeta
import GLang.Proofs.Value.Binding.ValueWeaken

namespace GLang

open GLang

/-! ## `ValCtx.substMap` — apply `ValTy.subst x u` to every bound type. -/

/-- Rewrite every bound type of a value context by `ValTy.subst x u`. -/
def ValCtx.substMap (x : VName) (u : ValExpr) (ε : ValCtx) : ValCtx where
  entries := ε.entries.map (fun p : Σ _ : VName, ValTy => ⟨p.1, ValTy.subst x u p.2⟩)
  nodupKeys := by
    have h : (ε.entries.map (fun p : Σ _ : VName, ValTy =>
                (⟨p.1, ValTy.subst x u p.2⟩ : Σ _ : VName, ValTy))).keys
              = ε.entries.keys := by
      show (ε.entries.map _).map Sigma.fst = ε.entries.map Sigma.fst
      rw [Multiset.map_map]; rfl
    rw [← Multiset.nodup_keys, h]
    exact Multiset.nodup_keys.mpr ε.nodupKeys

@[simp] theorem ValCtx.substMap_keys (x : VName) (u : ValExpr) (ε : ValCtx) :
    (ValCtx.substMap x u ε).keys = ε.keys := by
  unfold Finmap.keys ValCtx.substMap
  congr 1
  show (ε.entries.map _).map Sigma.fst = ε.entries.map Sigma.fst
  rw [Multiset.map_map]; rfl

theorem ValCtx.mem_substMap_iff (x : VName) (u : ValExpr) (ε : ValCtx) (z : VName) :
    z ∈ ValCtx.substMap x u ε ↔ z ∈ ε := by
  rw [← Finmap.mem_keys, ← Finmap.mem_keys, ValCtx.substMap_keys]

theorem ValCtx.substMap_lookup (x : VName) (u : ValExpr) (ε : ValCtx) (z : VName) (τ : ValTy)
    (h : ε.lookup z = some τ) :
    (ValCtx.substMap x u ε).lookup z = some (ValTy.subst x u τ) := by
  rw [Finmap.lookup_eq_some_iff] at h ⊢
  show (⟨z, ValTy.subst x u τ⟩ : Σ _ : VName, ValTy) ∈
        ε.entries.map (fun p : Σ _ : VName, ValTy => ⟨p.1, ValTy.subst x u p.2⟩)
  rw [Multiset.mem_map]
  exact ⟨⟨z, τ⟩, h, rfl⟩

theorem ValCtx.substMap_lookup_inv (x : VName) (u : ValExpr) (ε : ValCtx) (z : VName) (τ' : ValTy)
    (h : (ValCtx.substMap x u ε).lookup z = some τ') :
    ∃ τ, ε.lookup z = some τ ∧ τ' = ValTy.subst x u τ := by
  rw [Finmap.lookup_eq_some_iff] at h
  have h' : (⟨z, τ'⟩ : Σ _ : VName, ValTy) ∈
      ε.entries.map (fun p : Σ _ : VName, ValTy => ⟨p.1, ValTy.subst x u p.2⟩) := h
  rw [Multiset.mem_map] at h'
  obtain ⟨⟨z₀, τ₀⟩, hmem, heq⟩ := h'
  obtain ⟨rfl, rfl⟩ := Sigma.mk.inj_iff.mp heq
  exact ⟨τ₀, by rw [Finmap.lookup_eq_some_iff]; exact hmem, rfl⟩

theorem ValCtx.substMap_lookup_none (x : VName) (u : ValExpr) (ε : ValCtx) (z : VName)
    (h : ε.lookup z = none) : (ValCtx.substMap x u ε).lookup z = none := by
  rw [Finmap.lookup_eq_none, ValCtx.mem_substMap_iff, ← Finmap.lookup_eq_none]; exact h

@[simp] theorem ValCtx.substMap_empty (x : VName) (u : ValExpr) :
    ValCtx.substMap x u (∅ : ValCtx) = ∅ := by
  apply Finmap.ext_lookup; intro z
  rw [ValCtx.substMap_lookup_none x u _ z (by simp), Finmap.lookup_empty]

theorem ValCtx.substMap_insert (x : VName) (u : ValExpr) (ε : ValCtx) (y : VName) (σ : ValTy) :
    ValCtx.substMap x u (Finmap.insert y σ ε)
      = Finmap.insert y (ValTy.subst x u σ) (ValCtx.substMap x u ε) := by
  apply Finmap.ext_lookup
  intro z
  by_cases hzy : z = y
  · subst hzy
    rw [ValCtx.substMap_lookup x u _ z σ (by rw [Finmap.lookup_insert]),
        Finmap.lookup_insert]
  · rw [Finmap.lookup_insert_of_ne _ hzy]
    cases hlk : ε.lookup z with
    | none =>
        rw [ValCtx.substMap_lookup_none x u _ z
              (by rw [Finmap.lookup_insert_of_ne _ hzy]; exact hlk),
            ValCtx.substMap_lookup_none x u ε z hlk]
    | some τ =>
        rw [ValCtx.substMap_lookup x u _ z τ (by rw [Finmap.lookup_insert_of_ne _ hzy]; exact hlk),
            ValCtx.substMap_lookup x u ε z τ hlk]

/-- `substMap` commutes with erasing a key. -/
theorem ValCtx.substMap_erase (x : VName) (u : ValExpr) (ε : ValCtx) (z : VName) :
    ValCtx.substMap x u (ε.erase z) = (ValCtx.substMap x u ε).erase z := by
  apply Finmap.ext_lookup
  intro w
  by_cases hwz : w = z
  · subst hwz
    rw [ValCtx.substMap_lookup_none x u _ w (by rw [Finmap.lookup_erase]),
        Finmap.lookup_erase]
  · rw [Finmap.lookup_erase_ne hwz]
    cases hlk : ε.lookup w with
    | none =>
        rw [ValCtx.substMap_lookup_none x u _ w (by rw [Finmap.lookup_erase_ne hwz]; exact hlk),
            ValCtx.substMap_lookup_none x u ε w hlk]
    | some τ =>
        rw [ValCtx.substMap_lookup x u _ w τ (by rw [Finmap.lookup_erase_ne hwz]; exact hlk),
            ValCtx.substMap_lookup x u ε w τ hlk]

/-- Substitution preserves a non-`tprod` head on spaces (the `ttv_real`/`pinv_raw`/
    `inv_raw` discriminators survive `subst`). -/
theorem ValSpace.subst_ne_tprod (x : VName) (u : ValExpr) {s : ValSpace}
    (h : ∀ a b, s ≠ .tprod a b) : ∀ a b, ValSpace.subst x u s ≠ .tprod a b := by
  cases s with
  | tprod a b => exact absurd rfl (h a b)
  | real => intro a b; simp [ValSpace.subst]
  | empty => intro a b; simp [ValSpace.subst]
  | dsum s₀ s₁ => intro a b; simp [ValSpace.subst]
  | ffs p sp leev => intro a b; simp [ValSpace.subst]

/-! ## The value-language substitution metatheorem.

A non-linear variable `x : τx ∈ ε` substituted by `u`. The argument `u` is typed
in the SUBSTITUTED, `x`-erased context `ValCtx.substMap x u (ε.erase x)` (so the
`.var x` leaf reads it off directly). Single context (no `Δ`), no `promote`. -/

/-- `erase` commutes with `insert` at a distinct key. -/
theorem ValCtx.erase_insert_ne {ε : ValCtx} {x y : VName} {τ₀ : ValTy} (hxy : x ≠ y) :
    (Finmap.insert y τ₀ ε).erase x = Finmap.insert y τ₀ (ε.erase x) := by
  apply Finmap.ext_lookup; intro z
  by_cases hzx : z = x
  · rw [hzx, Finmap.lookup_erase, Finmap.lookup_insert_of_ne _ hxy,
      Finmap.lookup_erase]
  · rw [Finmap.lookup_erase_ne hzx]
    by_cases hzy : z = y
    · rw [hzy, Finmap.lookup_insert, Finmap.lookup_insert]
    · rw [Finmap.lookup_insert_of_ne _ hzy, Finmap.lookup_insert_of_ne _ hzy,
        Finmap.lookup_erase_ne hzx]

/-- The constant data threaded through the substitution recursion.
    Fields: `lc` (drives the binder-arm LN commutation), `xτ` (pins the type of
    the substituted variable), `xfv` (a variable does not occur in its own type),
    `argTyped` (the argument's typing in the substituted, `x`-erased context). -/
structure ValSubstData (x : VName) (u : ValExpr) (ε : ValCtx) (τx : ValTy) : Type where
  lc       : ValExpr.lc u
  xτ       : ε.lookup x = some τx
  xfv      : x ∉ ValTy.fv τx
  argTyped : ValHasType (ValCtx.substMap x u (ε.erase x)) u τx

/-- Extend the substitution data across a fresh non-substituted binder `(y, τ₀)`,
    `y ≠ x`, `y ∉ ε`. The argument typing is weakened by the substituted binding
    `(y, τ₀[x↦u])`. -/
def ValSubstData.extend {x : VName} {u : ValExpr} {ε : ValCtx} {τx : ValTy}
    (sd : ValSubstData x u ε τx) {y : VName} (τ₀ : ValTy) (hyx : y ≠ x) (hyε : y ∉ ε) :
    ValSubstData x u (Finmap.insert y τ₀ ε) τx where
  lc := sd.lc
  xτ := by rw [Finmap.lookup_insert_of_ne _ (Ne.symm hyx)]; exact sd.xτ
  xfv := sd.xfv
  argTyped := by
    have hy : y ∉ ValCtx.substMap x u (ε.erase x) := by
      rw [ValCtx.mem_substMap_iff]
      exact fun hmem => hyε (Finmap.mem_erase.mp hmem).2
    have hw := ValHasType.weaken sd.argTyped (y := y) (σ := ValTy.subst x u τ₀) hy
    rw [← ValCtx.substMap_insert, ← ValCtx.erase_insert_ne (Ne.symm hyx)] at hw
    exact hw

set_option maxHeartbeats 1600000 in
mutual

/-- **(ValSValid substitution).** -/
noncomputable def ValSValid.subst {x : VName} {u : ValExpr} {ε : ValCtx} {τx : ValTy} {s : ValSpace}
    (sd : ValSubstData x u ε τx) :
    ValSValid ε s → ValSValid (ValCtx.substMap x u (ε.erase x)) (ValSpace.subst x u s)
  | .real => .real
  | .empty => .empty
  | .dsum h₀ h₁ => .dsum (h₀.subst sd) (h₁.subst sd)
  | .tprod h₀ h₁ => .tprod (h₀.subst sd) (h₁.subst sd)
  | .ffs h₀ h₁ he => .ffs (h₀.subst sd) (h₁.subst sd) (he.subst sd)

/-- **(ValTValid substitution).** -/
noncomputable def ValTValid.subst {x : VName} {u : ValExpr} {ε : ValCtx} {τx : ValTy} {τ : ValTy} {k : ValKind}
    (sd : ValSubstData x u ε τx) :
    ValTValid ε τ k → ValTValid (ValCtx.substMap x u (ε.erase x)) (ValTy.subst x u τ) k
  | .space hs => .space (hs.subst sd)
  | @ValTValid.piTy ε τ₀ τ₁ k₀ k₁ L h₀ hbody => by
      refine ValTValid.piTy (L ∪ {x} ∪ ε.keys) (h₀.subst sd) (fun y hy => ?_)
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
      obtain ⟨⟨hyL, hyx⟩, hyε⟩ := hy
      rw [Finmap.mem_keys] at hyε
      have hrec := (hbody y hyL).subst (sd.extend τ₀ hyx hyε)
      have hsty : ValTy.subst x u (ValTy.openVar y τ₀ τ₁)
          = ValTy.openVar y (ValTy.subst x u τ₀) (ValTy.subst x u τ₁) := by
        simp only [ValTy.openVar, ValTy.subst_openRec x u sd.lc τ₁ 0 (.var y τ₀),
          ValExpr.subst, if_neg hyx]
      rw [hsty, ValCtx.erase_insert_ne (Ne.symm hyx), ValCtx.substMap_insert] at hrec
      exact hrec

/-- **(ValHasType substitution).** -/
noncomputable def ValHasType.subst {x : VName} {u : ValExpr} {ε : ValCtx} {τx : ValTy} {e : ValExpr} {τ : ValTy}
    (sd : ValSubstData x u ε τx) :
    ValHasType ε e τ →
      ValHasType (ValCtx.substMap x u (ε.erase x)) (ValExpr.subst x u e) (ValTy.subst x u τ)
  | @ValHasType.var _ z τ hl => by
      by_cases hzx : z = x
      · simp only [ValExpr.subst, if_pos hzx]
        have h1 := hl
        rw [hzx, sd.xτ] at h1
        have hτeq : τ = τx := (Option.some.inj h1).symm
        rw [hτeq, ValTy.subst_fresh x u τx sd.xfv]
        exact sd.argTyped
      · simp only [ValExpr.subst, if_neg hzx]
        refine ValHasType.var ?_
        apply ValCtx.substMap_lookup
        rw [Finmap.lookup_erase_ne hzx]; exact hl
  | .zero hsv => .zero (hsv.subst sd)
  | .rlit r => .rlit r
  | .scale h₀ h₁ => .scale (h₀.subst sd) (h₁.subst sd)
  | .vadd h₀ h₁ hs => .vadd (h₀.subst sd) (h₁.subst sd) (hs.subst sd)
  | .dsumE h₀ h₁ => .dsumE (h₀.subst sd) (h₁.subst sd)
  | .tprodE h₀ h₁ => .tprodE (h₀.subst sd) (h₁.subst sd)
  | .delta hsv => .delta (hsv.subst sd)
  | .idelta hsv => .idelta (hsv.subst sd)
  | .ttv_space hsv h₀ h₁ => .ttv_space (hsv.subst sd) (h₀.subst sd) (h₁.subst sd)
  | .ttv_real hsv h₀ h₁ hne =>
      .ttv_real (hsv.subst sd) (h₀.subst sd) (h₁.subst sd) (ValSpace.subst_ne_tprod x u hne)
  | .mtm hsv0 hsv1 h₀ h₁ =>
      .mtm (hsv0.subst sd) (hsv1.subst sd) (h₀.subst sd) (h₁.subst sd)
  | @ValHasType.vsum _ s0 s es hsv0 hbody hsvr hdet => by
      refine ValHasType.vsum (hsv0.subst sd) ?_ (hsvr.subst sd) ?_
      intro e' he'
      rw [ValExpr.substList_eq_map] at he'

      have hex := List.mem_map.mp he'
      have hmem : hex.choose ∈ es := hex.choose_spec.1
      have heq : ValExpr.subst x u hex.choose = e' := hex.choose_spec.2
      rw [← heq]
      exact (hbody hex.choose hmem).subst sd
      intro hempty
      have hes : es = [] := by
        rw [ValExpr.substList_eq_map, List.map_eq_nil_iff] at hempty
        exact hempty
      subst es
      have hs := hdet rfl
      subst s
      rfl
  | @ValHasType.vlam ε τ₀ τ₁ k₀ k₁ e L htval hbody => by
      refine ValHasType.vlam (L ∪ {x} ∪ ε.keys) (htval.subst sd) (fun y hy => ?_)
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
      obtain ⟨⟨hyL, hyx⟩, hyε⟩ := hy
      rw [Finmap.mem_keys] at hyε
      have hrec := (hbody y hyL).subst (sd.extend τ₀ hyx hyε)
      have hsrc : ValExpr.subst x u (ValExpr.openVar y τ₀ e)
          = ValExpr.openVar y (ValTy.subst x u τ₀) (ValExpr.subst x u e) := by
        simp only [ValExpr.openVar, ValExpr.subst_openRec x u sd.lc e 0 (.var y τ₀),
          ValExpr.subst, if_neg hyx]
      have hsty : ValTy.subst x u (ValTy.openVar y τ₀ τ₁)
          = ValTy.openVar y (ValTy.subst x u τ₀) (ValTy.subst x u τ₁) := by
        simp only [ValTy.openVar, ValTy.subst_openRec x u sd.lc τ₁ 0 (.var y τ₀),
          ValExpr.subst, if_neg hyx]
      rw [hsrc, hsty, ValCtx.erase_insert_ne (Ne.symm hyx), ValCtx.substMap_insert] at hrec
      exact hrec
  | @ValHasType.appV ε e₀ e₁ τ₀ τ₁ τ_out k_out h₀ h₁ heq htval => by
      have hheq : ValTy.subst x u τ_out
          = ValTy.applyCodomain (ValExpr.subst x u e₁) (ValTy.subst x u τ₁) := by
        simp only [heq, ValTy.subst_applyCodomain x u sd.lc e₁ τ₁]
      exact ValHasType.appV (h₀.subst sd) (h₁.subst sd) hheq (htval.subst sd)
  | .vkrn h h' => .vkrn (h.subst sd) (h'.subst sd)
  | .vblk h h' => .vblk (h.subst sd) (h'.subst sd)
  | .reshap h htval0 htval => .reshap (h.subst sd) (htval0.subst sd) (htval.subst sd)
  | .vtrans h => .vtrans (h.subst sd)
  | .gsvdS he ha hb => .gsvdS (he.subst sd) (ha.subst sd) (hb.subst sd)
  | .gsvdU he ha hb => .gsvdU (he.subst sd) (ha.subst sd) (hb.subst sd)
  | .gsvdUI he ha hb => .gsvdUI (he.subst sd) (ha.subst sd) (hb.subst sd)
  | .gsvdV he ha hb => .gsvdV (he.subst sd) (ha.subst sd) (hb.subst sd)
  | .gsvdVI he ha hb => .gsvdVI (he.subst sd) (ha.subst sd) (hb.subst sd)
  | .pinv_tensor h => .pinv_tensor (h.subst sd)
  | .pinv_raw h hne => .pinv_raw (h.subst sd) (ValSpace.subst_ne_tprod x u hne)
  | .gpinv he ha hb => .gpinv (he.subst sd) (ha.subst sd) (hb.subst sd)
  | .rrefRep h₀ h₁ => .rrefRep (h₀.subst sd) (h₁.subst sd)
  | .inv_tensor h => .inv_tensor (h.subst sd)
  | .inv_raw h hne => .inv_raw (h.subst sd) (ValSpace.subst_ne_tprod x u hne)
  | .svds he => .svds (he.subst sd)

end

end GLang
