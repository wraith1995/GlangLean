import GLang.Graded.Weakening

namespace GLang.Graded

open GLang

/-! ## The type-context view of a nonlinear context. -/

/-- The ω/type view of a nonlinear context: every ε-binding as a type. -/
def asTypeCtx (ε : NLCtx) : Name → Option Ty := fun x => ε.lookup x

/-- Context disjointness (the `CtxWF` invariant `ε ∩ Δ = ∅`). -/
def CtxDisj (Δ : LCtx) (ε : NLCtx) : Prop := ∀ x, x ∈ Δ → x ∉ ε

theorem CtxDisj.of_union_left {Δ₀ Δ₁ : LCtx} {ε : NLCtx}
    (h : CtxDisj (Δ₀ ∪ Δ₁) ε) : CtxDisj Δ₀ ε :=
  fun x hx => h x (Finmap.mem_union.mpr (Or.inl hx))

theorem CtxDisj.of_union_right {Δ₀ Δ₁ : LCtx} {ε : NLCtx}
    (h : CtxDisj (Δ₀ ∪ Δ₁) ε) : CtxDisj Δ₁ ε :=
  fun x hx => h x (Finmap.mem_union.mpr (Or.inr hx))

/-! ## `typeCtxOmega` of a translation is the type view (under disjointness). -/

theorem typeCtxOmega_tr {Δ : LCtx} {ε : NLCtx} (hd : CtxDisj Δ ε) :
    typeCtxOmega (tr Δ ε) = asTypeCtx ε := by
  funext x
  simp only [typeCtxOmega, tr, asTypeCtx]
  cases hΔ : Δ.lookup x with
  | some s =>
      have hxΔ : x ∈ Δ := Finmap.mem_of_lookup_eq_some hΔ
      have hxε : x ∉ ε := hd x hxΔ
      rw [Finmap.lookup_eq_none.mpr hxε]
  | none => cases ε.lookup x <;> rfl

/-- `resurrect (asTypeCtx ε)` equals the all-omega context `tr ∅ ε`. -/
theorem tr_empty_resurrect (ε : NLCtx) :
    tr (∅ : LCtx) ε = resurrect (asTypeCtx ε) := by
  funext x
  simp only [tr, resurrect, asTypeCtx, Finmap.lookup_empty]
  cases ε.lookup x with
  | some τ => rfl
  | none => rfl

/-! ## Binders relate `insert` to `Function.update`. -/

theorem tr_insert (Δ : LCtx) (ε : NLCtx) (y : Name) (s : Space) :
    tr (Finmap.insert y s Δ) ε
      = Function.update (tr Δ ε) y (some (GGrade.one, .space s)) := by
  funext x
  rcases eq_or_ne x y with rfl | hxy
  · rw [Function.update_self]; simp only [tr, Finmap.lookup_insert]
  · rw [Function.update_of_ne hxy]; simp only [tr, Finmap.lookup_insert_of_ne _ hxy]

theorem tr_insert_nl (ε : NLCtx) (y : Name) (τ : Ty) :
    tr ∅ (Finmap.insert y τ ε)
      = Function.update (tr ∅ ε) y (some (GGrade.omega, τ)) := by
  funext x
  rcases eq_or_ne x y with rfl | hxy
  · rw [Function.update_self]
    simp only [tr, Finmap.lookup_empty, Finmap.lookup_insert]
  · rw [Function.update_of_ne hxy]
    simp only [tr, Finmap.lookup_empty, Finmap.lookup_insert_of_ne _ hxy]

theorem asTypeCtx_insert (ε : NLCtx) (y : Name) (τ : Ty) :
    asTypeCtx (Finmap.insert y τ ε) = Function.update (asTypeCtx ε) y (some τ) := by
  funext x
  rcases eq_or_ne x y with rfl | hxy
  · rw [Function.update_self]; simp only [asTypeCtx, Finmap.lookup_insert]
  · rw [Function.update_of_ne hxy]; simp only [asTypeCtx, Finmap.lookup_insert_of_ne _ hxy]

/-! ## Split distribution: `tr` of a disjoint union is a `gadd`. -/

theorem tr_add {Δ₀ Δ₁ : LCtx} {ε : NLCtx}
    (hd : Finmap.Disjoint Δ₀ Δ₁) (hd0 : CtxDisj Δ₀ ε) (hd1 : CtxDisj Δ₁ ε) :
    ∀ x, tr (Δ₀ ∪ Δ₁) ε x = gadd (tr Δ₀ ε x) (tr Δ₁ ε x) := by
  intro x
  simp only [tr]
  cases h0 : Δ₀.lookup x with
  | some s =>
      have hxΔ₀ : x ∈ Δ₀ := Finmap.mem_of_lookup_eq_some h0
      have hxΔ₁ : x ∉ Δ₁ := fun h => hd x hxΔ₀ h
      have hxε : x ∉ ε := hd0 x hxΔ₀
      rw [Finmap.lookup_union_left hxΔ₀, h0, Finmap.lookup_eq_none.mpr hxΔ₁,
          Finmap.lookup_eq_none.mpr hxε]
      rfl
  | none =>
      have hxΔ₀ : x ∉ Δ₀ := Finmap.lookup_eq_none.mp h0
      cases h1 : Δ₁.lookup x with
      | some s =>
          have hxΔ₁ : x ∈ Δ₁ := Finmap.mem_of_lookup_eq_some h1
          have hxε : x ∉ ε := hd1 x hxΔ₁
          rw [Finmap.lookup_union_right hxΔ₀, h1, Finmap.lookup_eq_none.mpr hxε]
          rfl
      | none =>
          have hxΔ₁ : x ∉ Δ₁ := Finmap.lookup_eq_none.mp h1
          rw [Finmap.lookup_union_right hxΔ₀, h1]
          cases hε : ε.lookup x with
          | some τ => simp [gadd, GGrade.add]
          | none => rfl

/-- **The split branches type-agree.** At a var present in BOTH `tr Δ₀ ε` and
    `tr Δ₁ ε`: it cannot be linear in one and present in the other (Δ₀,Δ₁ disjoint;
    a linear var is `CtxDisj`-excluded from ε, hence from the other branch's ε part),
    so it must be an ε var in both — where both give `some (ω, ε x)`, the same type. -/
theorem tr_typeagree {Δ₀ Δ₁ : LCtx} {ε : NLCtx}
    (hdisj : Finmap.Disjoint Δ₀ Δ₁) (hd0 : CtxDisj Δ₀ ε) (hd1 : CtxDisj Δ₁ ε) :
    TypeAgree (tr Δ₀ ε) (tr Δ₁ ε) := by
  intro x g₀ τ₀ g₁ τ₁ h0 h1
  simp only [tr] at h0 h1
  cases hΔ0 : Δ₀.lookup x with
  | some s0 =>
      have hx0 : x ∈ Δ₀ := Finmap.mem_of_lookup_eq_some hΔ0
      have hxΔ1 : x ∉ Δ₁ := fun h => hdisj x hx0 h
      have hxε : x ∉ ε := hd0 x hx0
      rw [Finmap.lookup_eq_none.mpr hxΔ1, Finmap.lookup_eq_none.mpr hxε] at h1
      simp at h1
  | none =>
      rw [hΔ0] at h0
      cases hε : ε.lookup x with
      | none => rw [hε] at h0; simp at h0
      | some τ =>
          have hxε : x ∈ ε := Finmap.mem_of_lookup_eq_some hε
          cases hΔ1 : Δ₁.lookup x with
          | some s1 => exact absurd hxε (hd1 x (Finmap.mem_of_lookup_eq_some hΔ1))
          | none =>
              rw [hε] at h0
              rw [hΔ1, hε] at h1
              simp only [Option.some.injEq, Prod.mk.injEq] at h0 h1
              rw [← h0.2, ← h1.2]

/-! ## Context-disjointness plumbing. -/

theorem CtxDisj.empty (ε : NLCtx) : CtxDisj (∅ : LCtx) ε := by
  intro x hx
  obtain ⟨s, hs⟩ := Finmap.mem_iff.mp hx
  simp [Finmap.lookup_empty] at hs

theorem CtxDisj.insert' {Δ : LCtx} {ε : NLCtx} (hd : CtxDisj Δ ε) {y : Name}
    {s : Space} (hyε : y ∉ ε) : CtxDisj (Finmap.insert y s Δ) ε := by
  intro x hx
  rcases Finmap.mem_insert.mp hx with rfl | hxΔ
  · exact hyε
  · exact hd x hxΔ

theorem CtxDisj.promote_inner {lin Δ : LCtx} {ε' : NLCtx}
    (hd : CtxDisj Δ (lin.toNL ∪ ε')) (hdisjε : Finmap.Disjoint lin.toNL ε') :
    CtxDisj (lin ∪ Δ) ε' := by
  intro x hx
  rcases Finmap.mem_union.mp hx with hxlin | hxΔ
  · exact hdisjε x ((LCtx.mem_toNL_iff lin x).mpr hxlin)
  · exact fun h => hd x hxΔ (Finmap.mem_union.mpr (Or.inr h))

/-! ## The `gvar` affine-leaf helpers at `tr`. -/

theorem tr_singleton_no_lin (x : Name) (s : Space) (ε : NLCtx) :
    ∀ y, y ≠ x → ∀ τy, tr (Finmap.singleton x s : LCtx) ε y ≠ some (GGrade.one, τy) := by
  intro y hy τy h
  have hnone : (Finmap.singleton x s : LCtx).lookup y = none := by
    rw [Finmap.lookup_eq_none]; intro hm; rw [Finmap.mem_singleton] at hm; exact hy hm
  simp only [tr, hnone] at h
  split at h <;> simp_all

theorem tr_emptyΔ_no_lin (ε : NLCtx) :
    ∀ y, ∀ τy, tr (∅ : LCtx) ε y ≠ some (GGrade.one, τy) := by
  intro y τy h
  simp only [tr, Finmap.lookup_empty] at h
  split at h <;> simp_all

/-- `var_lin` at `tr`: `x` at grade `1` (`≠ 0`), all others non-linear. -/
def gvar_lin_tr {ε : NLCtx} (x : Name) (s : Space) :
    GHasType (tr (Finmap.singleton x s : LCtx) ε) (.var x) (.space s) :=
  GHasType.gvar
    (show tr (Finmap.singleton x s : LCtx) ε x = some (GGrade.one, .space s) by
      simp only [tr, Finmap.lookup_singleton_eq])
    (by decide)
    (tr_singleton_no_lin x s ε)

/-- `var_nlin` at `tr`: `x` at grade `ω` (`≠ 0`), all others non-linear. -/
def gvar_nlin_tr {ε : NLCtx} {x : Name} {τ : Ty}
    (hlk : ε.lookup x = some τ) : GHasType (tr (∅ : LCtx) ε) (.var x) τ :=
  GHasType.gvar
    (show tr (∅ : LCtx) ε x = some (GGrade.omega, τ) by
      simp only [tr, Finmap.lookup_empty, hlk])
    (by decide)
    (fun y _ τy => tr_emptyΔ_no_lin ε y τy)

/-! ## The forward bridge — one mutual induction over the source block.

`svalidBridge / tvalidBridge / subtypeBridge` land the type-formation judgments
(over `asTypeCtx ε`). `hasTypeBridge` lands term typing at `tr Δ ε`; its FFS
callers (`.ker` etc.) use `Δ = ∅` (the ω resurrection, `tr_empty_resurrect`). -/

mutual

/-- `SValid ε s → GSValid (asTypeCtx ε) s`. -/
def svalidBridge : {ε : NLCtx} → {s : Space} → SValid ε s → GSValid (asTypeCtx ε) s
  | _, _, .empty => .empty
  | _, _, .real => .real
  | _, _, .dual d => .dual (svalidBridge d)
  | _, _, .dsum d₀ d₁ => .dsum (svalidBridge d₀) (svalidBridge d₁)
  | _, _, .tprod d₀ d₁ => .tprod (svalidBridge d₀) (svalidBridge d₁)
  | ε, _, .ker hs₀ hs₁ he =>
      .ker (svalidBridge hs₀) (svalidBridge hs₁)
        (tr_empty_resurrect ε ▸ hasTypeBridgeCore he (CtxDisj.empty ε))
  | ε, _, .coker hs₀ hs₁ he =>
      .coker (svalidBridge hs₀) (svalidBridge hs₁)
        (tr_empty_resurrect ε ▸ hasTypeBridgeCore he (CtxDisj.empty ε))
  | ε, _, .img hs₀ hs₁ he =>
      .img (svalidBridge hs₀) (svalidBridge hs₁)
        (tr_empty_resurrect ε ▸ hasTypeBridgeCore he (CtxDisj.empty ε))
  | ε, _, .coimg hs₀ hs₁ he =>
      .coimg (svalidBridge hs₀) (svalidBridge hs₁)
        (tr_empty_resurrect ε ▸ hasTypeBridgeCore he (CtxDisj.empty ε))

/-- `TValid ε τ k → GTValid (asTypeCtx ε) τ k`. -/
def tvalidBridge : {ε : NLCtx} → {τ : Ty} → {k : Kind} → TValid ε τ k →
    GTValid (asTypeCtx ε) τ k
  | _, _, _, .space hs => .space (svalidBridge hs)
  | _, _, _, .piTy L hτ₀ hbody =>
      .piTy L (tvalidBridge hτ₀)
        (fun y hy => by
          have ih := tvalidBridge (hbody y hy)
          rw [asTypeCtx_insert] at ih
          exact ih)

/-- `SubType ε s₀ s₁ → GSubType (asTypeCtx ε) s₀ s₁`. -/
def subtypeBridge : {ε : NLCtx} → {s₀ s₁ : Space} → SubType ε s₀ s₁ →
    GSubType (asTypeCtx ε) s₀ s₁
  | ε, _, _, .sub_ker hs₀ hs₁ he =>
      .sub_ker (svalidBridge hs₀) (svalidBridge hs₁)
        (tr_empty_resurrect ε ▸ hasTypeBridgeCore he (CtxDisj.empty ε))
  | ε, _, _, .sub_coker hs₀ hs₁ he =>
      .sub_coker (svalidBridge hs₀) (svalidBridge hs₁)
        (tr_empty_resurrect ε ▸ hasTypeBridgeCore he (CtxDisj.empty ε))
  | ε, _, _, .sub_img hs₀ hs₁ he =>
      .sub_img (svalidBridge hs₀) (svalidBridge hs₁)
        (tr_empty_resurrect ε ▸ hasTypeBridgeCore he (CtxDisj.empty ε))
  | ε, _, _, .sub_coimg hs₀ hs₁ he =>
      .sub_coimg (svalidBridge hs₀) (svalidBridge hs₁)
        (tr_empty_resurrect ε ▸ hasTypeBridgeCore he (CtxDisj.empty ε))

/-- **The forward bridge.** `HasType Δ ε e τ → GHasType (tr Δ ε) e τ` (given the
    `CtxWF` disjointness `ε ∩ Δ = ∅`). -/
def hasTypeBridgeCore : {Δ : LCtx} → {ε : NLCtx} → {e : Term} → {τ : Ty} →
    HasType Δ ε e τ → CtxDisj Δ ε → GHasType (tr Δ ε) e τ
  | _, _, _, _, .zero hs, hd =>
      .gzero ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs)
  | _, _, _, _, .smul hs hdisj h₀ h₁, hd =>
      .gsmul ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs)
        (tr_add hdisj (CtxDisj.of_union_left hd) (CtxDisj.of_union_right hd))
        (tr_typeagree hdisj (CtxDisj.of_union_left hd) (CtxDisj.of_union_right hd))
        (hasTypeBridgeCore h₀ (CtxDisj.of_union_left hd))
        (hasTypeBridgeCore h₁ (CtxDisj.of_union_right hd))
  | _, _, _, _, .add hs h₀ h₁, hd =>
      .gadd ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs)
        (hasTypeBridgeCore h₀ hd) (hasTypeBridgeCore h₁ hd)
  | _, _, _, _, .inner hs, hd =>
      .ginner ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs) (tr_emptyΔ_no_lin _)
  | _, _, _, _, .real_lit r, _ => .greal_lit r (tr_emptyΔ_no_lin _)
  | _, _, _, _, .app_linear hs₀ hs₁ hdisj h₀ h₁, hd =>
      .gapp_linear ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs₀)
        ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs₁)
        (tr_add hdisj (CtxDisj.of_union_left hd) (CtxDisj.of_union_right hd))
        (tr_typeagree hdisj (CtxDisj.of_union_left hd) (CtxDisj.of_union_right hd))
        (hasTypeBridgeCore h₀ (CtxDisj.of_union_left hd))
        (hasTypeBridgeCore h₁ (CtxDisj.of_union_right hd))
  | _, _, _, _, .app_inner hs hdisj h₀ h₁, hd =>
      .gapp_inner ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs)
        (tr_add hdisj (CtxDisj.of_union_left hd) (CtxDisj.of_union_right hd))
        (tr_typeagree hdisj (CtxDisj.of_union_left hd) (CtxDisj.of_union_right hd))
        (hasTypeBridgeCore h₀ (CtxDisj.of_union_left hd))
        (hasTypeBridgeCore h₁ (CtxDisj.of_union_right hd))
  | _, _, _, _, .app_nonlinear h₀ h₁, hd =>
      .gapp_nonlinear (tr_emptyΔ_no_lin _) (hasTypeBridgeCore h₀ hd) (hasTypeBridgeCore h₁ hd)
  | _, _, _, _, @HasType.var_lin _ x s, _ => gvar_lin_tr x s
  | _, _, _, _, .var_nlin hlk, _ => gvar_nlin_tr hlk
  | _, _, _, _, .pinv_tensor hs₀ hs₁ he, hd =>
      .gpinv_tensor ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs₀)
        ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs₁) (tr_emptyΔ_no_lin _)
        (hasTypeBridgeCore he hd)
  | _, _, _, _, .pinv_dual hs he, hd =>
      .gpinv_dual ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs) (tr_emptyΔ_no_lin _)
        (hasTypeBridgeCore he hd)
  | _, _, _, _, .promote lin hdisjΔ hdisjε _ hinner, hd =>
      promote_admissible hdisjΔ
        (hasTypeBridgeCore hinner (CtxDisj.promote_inner hd hdisjε))
  | _, _, _, _, .dsumE hs₀ hs₁ h₀ h₁, hd =>
      .gdsumE ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs₀)
        ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs₁)
        (hasTypeBridgeCore h₀ hd) (hasTypeBridgeCore h₁ hd)
  | _, _, _, _, .tprodE hs₀ hs₁ hdisj h₀ h₁, hd =>
      .gtprodE ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs₀)
        ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs₁)
        (tr_add hdisj (CtxDisj.of_union_left hd) (CtxDisj.of_union_right hd))
        (tr_typeagree hdisj (CtxDisj.of_union_left hd) (CtxDisj.of_union_right hd))
        (hasTypeBridgeCore h₀ (CtxDisj.of_union_left hd))
        (hasTypeBridgeCore h₁ (CtxDisj.of_union_right hd))
  | _, ε, _, _, .llam_real L hs hbody, hd =>
      .gllam_real (L ∪ ε.keys) ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs)
        (fun y hy => by
          simp only [Finset.mem_union, not_or] at hy
          obtain ⟨hyL, hykeys⟩ := hy
          have hyε : y ∉ ε := fun h => hykeys (Finmap.mem_keys.mpr h)
          have ih := hasTypeBridgeCore (hbody y hyL) (CtxDisj.insert' hd hyε)
          rw [tr_insert] at ih
          exact ih)
  | _, ε, _, _, .llam_tensor L hne hs₀ hs hbody, hd =>
      .gllam_tensor (L ∪ ε.keys) hne
        ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs₀)
        ((typeCtxOmega_tr hd).symm ▸ svalidBridge hs)
        (fun y hy => by
          simp only [Finset.mem_union, not_or] at hy
          obtain ⟨hyL, hykeys⟩ := hy
          have hyε : y ∉ ε := fun h => hykeys (Finmap.mem_keys.mpr h)
          have ih := hasTypeBridgeCore (hbody y hyL) (CtxDisj.insert' hd hyε)
          rw [tr_insert] at ih
          exact ih)
  | _, _, _, _, .embed hsub, hd =>
      .gembed ((typeCtxOmega_tr hd).symm ▸ subtypeBridge hsub) (tr_emptyΔ_no_lin _)
  | _, ε, _, _, .nllam L htv hbody, hd =>
      .gnllam L ((typeCtxOmega_tr hd).symm ▸ tvalidBridge htv) (tr_emptyΔ_no_lin _)
        (fun y hy => by
          have ih := hasTypeBridgeCore (hbody y hy) (CtxDisj.empty _)
          rw [tr_insert_nl] at ih
          exact ih)

end

/-! ## The public forward bridge. -/

/-- **The forward bridge.** `HasType Δ ε e τ → GHasType (tr Δ ε) e τ` (given the
    `CtxWF` disjointness `ε ∩ Δ = ∅`). Argument order mirrors the U3.1 API. -/
def hasTypeBridge {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty}
    (hd : CtxDisj Δ ε) (h : HasType Δ ε e τ) : GHasType (tr Δ ε) e τ :=
  hasTypeBridgeCore h hd

end GLang.Graded
