import GLang.Proofs.Value.Runtime.RuntimeValueInfer
import GLang.Proofs.Value.Runtime.RuntimeValueWeaken

namespace GLang.RuntimeValue

/-- Inversion: a `.space`-typed `ValTValid` yields the space's validity
    (the only constructor at a `.space _` index is `space`; forces `k = base`). -/
def valTValid_space_inv {ε : ValCtx} {s : ValSpace} {k : ValKind}
    (h : ValTValid ε (.space s) k) : ValSValid ε s :=
  match h with | .space hsv => hsv

/-- Inversion: validity of a tensor space splits into its factors. -/
def valSValid_tprod_inv {ε : ValCtx} {a b : ValSpace}
    (h : ValSValid ε (.tprod a b)) : ValSValid ε a × ValSValid ε b :=
  match h with | .tprod ha hb => ⟨ha, hb⟩

/-- Context validity: every type bound in `ε` is itself valid (at some
    kind). Type-valued so it supplies an actual `ValTValid` derivation to
    the `.var` regularity case. -/
def ValCtxValid (ε : ValCtx) : Type :=
  ∀ x τ, ε.lookup x = some τ → Σ k, ValTValid ε τ k

/-- **`lem:soundVals` (1) — regularity.** A well-typed value's type is
    valid (at some kind) given a valid context. Structural recursion on the
    typing derivation. -/
def ValHasType.regular : {ε : ValCtx} → {e : ValExpr} → {τ : ValTy} →
    ValHasType ε e τ → ValCtxValid ε → Σ k, ValTValid ε τ k
  | _, _, _, .var hl, hctx => hctx _ _ hl
  | _, _, _, .zero hsv, _ => ⟨.base, .space hsv⟩
  | _, _, _, .rlit _, _ => ⟨.base, .space .real⟩
  | _, _, _, .scale _ h₁, hctx => h₁.regular hctx
  | _, _, _, .vadd _ _ hs, _ => ⟨.base, .space hs⟩
  | _, _, _, .dsumE h₀ h₁, hctx =>
      ⟨.base, .space (.dsum (valTValid_space_inv (h₀.regular hctx).2)
                            (valTValid_space_inv (h₁.regular hctx).2))⟩
  | _, _, _, .tprodE h₀ h₁, hctx =>
      ⟨.base, .space (.tprod (valTValid_space_inv (h₀.regular hctx).2)
                             (valTValid_space_inv (h₁.regular hctx).2))⟩
  | _, _, _, .delta hsv, _ => ⟨.base, .space hsv⟩
  | _, _, _, .idelta hsv, _ => ⟨.base, .space (.tprod hsv hsv)⟩
  | _, _, _, .ttv_space _ h₀ _, hctx =>
      ⟨.base, .space (valSValid_tprod_inv (valTValid_space_inv (h₀.regular hctx).2)).2⟩
  | _, _, _, .ttv_real _ _ _ _, _ => ⟨.base, .space .real⟩
  | _, _, _, .mtm _ _ h₀ h₁, hctx =>
      let hs0 := (valSValid_tprod_inv (valTValid_space_inv (h₀.regular hctx).2)).2
      let hs2 := (valSValid_tprod_inv (valTValid_space_inv (h₁.regular hctx).2)).1
      ⟨.base, .space (.tprod hs2 hs0)⟩
  | _, _, _, .vsum _ _ hsvr _, _ => ⟨.base, .space hsvr⟩
  | _, _, _, .vlam _ htval _, _ => ⟨_, htval⟩
  | _, _, _, .appV _ _ _ htval, _ => ⟨_, htval⟩
  | _, _, _, .vkrn h h', hctx =>
      let ⟨hs0, hs2⟩ := valSValid_tprod_inv (valTValid_space_inv (h.regular hctx).2)
      let ⟨hs1, hs3⟩ := valSValid_tprod_inv (valTValid_space_inv (h'.regular hctx).2)
      ⟨.base, .space (.tprod (.tprod hs0 hs1) (.tprod hs2 hs3))⟩
  | _, _, _, .vblk h h', hctx =>
      let ⟨hs0, hs2⟩ := valSValid_tprod_inv (valTValid_space_inv (h.regular hctx).2)
      let ⟨hs1, hs3⟩ := valSValid_tprod_inv (valTValid_space_inv (h'.regular hctx).2)
      ⟨.base, .space (.tprod (.dsum hs0 hs1) (.dsum hs2 hs3))⟩
  | _, _, _, .reshap _ _ htval, _ => ⟨_, htval⟩
  | _, _, _, .vtrans h, hctx =>
      let ⟨hs0, hs1⟩ := valSValid_tprod_inv (valTValid_space_inv (h.regular hctx).2)
      ⟨.base, .space (.tprod hs1 hs0)⟩
  | _, _, _, .gsvdS he _ _, hctx =>
      let ⟨hs0, hs1⟩ := valSValid_tprod_inv (valTValid_space_inv (he.regular hctx).2)
      ⟨.base, .space (.tprod (.ffs hs0 hs1 he) (.ffs hs0 hs1 he))⟩
  | _, _, _, .gsvdU he _ _, hctx =>
      let ⟨hs0, hs1⟩ := valSValid_tprod_inv (valTValid_space_inv (he.regular hctx).2)
      ⟨.base, .space (.tprod hs0 (.ffs hs0 hs1 he))⟩
  | _, _, _, .gsvdUI he _ _, hctx =>
      let ⟨hs0, hs1⟩ := valSValid_tprod_inv (valTValid_space_inv (he.regular hctx).2)
      ⟨.base, .space (.tprod hs0 (.ffs hs0 hs1 he))⟩
  | _, _, _, .gsvdV he _ _, hctx =>
      let ⟨hs0, hs1⟩ := valSValid_tprod_inv (valTValid_space_inv (he.regular hctx).2)
      ⟨.base, .space (.tprod hs1 (.ffs hs0 hs1 he))⟩
  | _, _, _, .gsvdVI he _ _, hctx =>
      let ⟨hs0, hs1⟩ := valSValid_tprod_inv (valTValid_space_inv (he.regular hctx).2)
      ⟨.base, .space (.tprod hs1 (.ffs hs0 hs1 he))⟩
  | _, _, _, .pinv_tensor h, hctx =>
      let ⟨hs0, hs1⟩ := valSValid_tprod_inv (valTValid_space_inv (h.regular hctx).2)
      ⟨.base, .space (.tprod hs1 hs0)⟩
  | _, _, _, .pinv_raw h _, hctx =>
      ⟨.base, .space (.tprod .real (valTValid_space_inv (h.regular hctx).2))⟩
  | _, _, _, .gpinv h₀ _ _, hctx =>
      let ⟨hs0, hs1⟩ := valSValid_tprod_inv (valTValid_space_inv (h₀.regular hctx).2)
      ⟨.base, .space (.tprod hs1 hs0)⟩
  | _, _, _, .rrefRep _ h₁, hctx =>
      let ⟨hp0, hp1⟩ := valSValid_tprod_inv (valTValid_space_inv (h₁.regular hctx).2)
      ⟨.base, .space (.tprod hp1 hp0)⟩
  | _, _, _, .inv_tensor h, hctx =>
      let ⟨hs0, hs1⟩ := valSValid_tprod_inv (valTValid_space_inv (h.regular hctx).2)
      ⟨.base, .space (.tprod hs1 hs0)⟩
  | _, _, _, .inv_raw h _, hctx =>
      ⟨.base, .space (.tprod .real (valTValid_space_inv (h.regular hctx).2))⟩
  | _, _, _, .svds he, hctx =>
      let ⟨hs0, hs1⟩ := valSValid_tprod_inv (valTValid_space_inv (he.regular hctx).2)
      ⟨.base, .space (.tprod (.ffs hs0 hs1 he) (.ffs hs0 hs1 he))⟩

end GLang.RuntimeValue
