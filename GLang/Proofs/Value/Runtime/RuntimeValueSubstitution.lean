import GLang.Proofs.Value.Binding.ValueSubstitution
import GLang.Proofs.Value.Runtime.RuntimeValueWeaken

/-! Substitution for the live value-typing judgment. -/
namespace GLang.RuntimeValue

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

end GLang.RuntimeValue
