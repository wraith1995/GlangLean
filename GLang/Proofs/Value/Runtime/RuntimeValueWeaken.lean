import GLang.Value.Typing
import GLang.Value.Supporting.StrictTyping

namespace GLang.RuntimeValue

mutual

/-- **Weakening (SValid).** Inserting a fresh binding preserves value-space
    validity. -/
def ValSValid.weaken : {ε : ValCtx} → {s : ValSpace} → ValSValid ε s →
    {y : VName} → {σ : ValTy} → y ∉ ε → ValSValid (Finmap.insert y σ ε) s
  | _, _, .real, _, _, _ => .real
  | _, _, .empty, _, _, _ => .empty
  | _, _, .dsum h₀ h₁, _, _, hy => .dsum (h₀.weaken hy) (h₁.weaken hy)
  | _, _, .tprod h₀ h₁, _, _, hy => .tprod (h₀.weaken hy) (h₁.weaken hy)
  | _, _, .ffs h₀ h₁ he, _, _, hy =>
      .ffs (h₀.weaken hy) (h₁.weaken hy) (he.weaken hy)

/-- **Weakening (TValid).** Inserting a fresh binding preserves type validity
    (at the same kind). -/
def ValTValid.weaken : {ε : ValCtx} → {τ : ValTy} → {k : ValKind} → ValTValid ε τ k →
    {y : VName} → {σ : ValTy} → y ∉ ε → ValTValid (Finmap.insert y σ ε) τ k
  | _, _, _, .space hs, _, _, hy => .space (hs.weaken hy)
  | _, _, _, @ValTValid.piTy ε τ₀ τ₁ k₀ k₁ L h₀ hbody, y, σ, hy =>
      ValTValid.piTy (L ∪ {y}) (h₀.weaken hy)
        (fun z hz => by
          have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
          have hzy : z ≠ y := fun h => hz (Finset.mem_union_right _ (by simp [h]))
          have hyins : y ∉ Finmap.insert z τ₀ ε := by
            rw [Finmap.mem_insert]
            rintro (h | h)
            · exact hzy h.symm
            · exact hy h
          rw [Finmap.insert_insert_of_ne (a := y) (a' := z) (b := σ) (b' := τ₀) ε hzy.symm]
          exact (hbody z hzL).weaken hyins)

/-- **Weakening (HasType).** Inserting a fresh binding preserves value typing;
    the expression and its type are unchanged. -/
def ValHasType.weaken : {ε : ValCtx} → {e : ValExpr} → {τ : ValTy} → ValHasType ε e τ →
    {y : VName} → {σ : ValTy} → y ∉ ε → ValHasType (Finmap.insert y σ ε) e τ
  | _, _, _, @ValHasType.var ε x τ hl, y, _, hy =>
      .var (by
        have hne : x ≠ y := fun h => hy (h ▸ Finmap.mem_of_lookup_eq_some hl)
        rw [Finmap.lookup_insert_of_ne _ hne]; exact hl)
  | _, _, _, .zero hsv, _, _, hy => .zero (hsv.weaken hy)
  | _, _, _, .rlit r, _, _, _ => .rlit r
  | _, _, _, .scale h₀ h₁, _, _, hy => .scale (h₀.weaken hy) (h₁.weaken hy)
  | _, _, _, .vadd h₀ h₁ hs, _, _, hy => .vadd (h₀.weaken hy) (h₁.weaken hy) (hs.weaken hy)
  | _, _, _, .dsumE h₀ h₁, _, _, hy => .dsumE (h₀.weaken hy) (h₁.weaken hy)
  | _, _, _, .tprodE h₀ h₁, _, _, hy => .tprodE (h₀.weaken hy) (h₁.weaken hy)
  | _, _, _, .delta hsv, _, _, hy => .delta (hsv.weaken hy)
  | _, _, _, .idelta hsv, _, _, hy => .idelta (hsv.weaken hy)
  | _, _, _, .ttv_space hsv h₀ h₁, _, _, hy =>
      .ttv_space (hsv.weaken hy) (h₀.weaken hy) (h₁.weaken hy)
  | _, _, _, .ttv_real hsv h₀ h₁ hd, _, _, hy =>
      .ttv_real (hsv.weaken hy) (h₀.weaken hy) (h₁.weaken hy) hd
  | _, _, _, .mtm hsv hsv1 h₀ h₁, _, _, hy =>
      .mtm (hsv.weaken hy) (hsv1.weaken hy) (h₀.weaken hy) (h₁.weaken hy)
  | _, _, _, .vsum hsv hbody hsvr hdet, _, _, hy =>
      .vsum (hsv.weaken hy) (fun e he => (hbody e he).weaken hy) (hsvr.weaken hy) hdet
  | _, _, _, @ValHasType.vlam ε τ₀ τ₁ k₀ k₁ e L htval hbody, y, σ, hy =>
      ValHasType.vlam (L ∪ {y}) (htval.weaken hy)
        (fun z hz => by
          have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
          have hzy : z ≠ y := fun h => hz (Finset.mem_union_right _ (by simp [h]))
          have hyins : y ∉ Finmap.insert z τ₀ ε := by
            rw [Finmap.mem_insert]
            rintro (h | h)
            · exact hzy h.symm
            · exact hy h
          rw [Finmap.insert_insert_of_ne (a := y) (a' := z) (b := σ) (b' := τ₀) ε hzy.symm]
          exact (hbody z hzL).weaken hyins)
  | _, _, _, .appV h₀ h₁ heq htval, _, _, hy =>
      .appV (h₀.weaken hy) (h₁.weaken hy) heq (htval.weaken hy)
  | _, _, _, .vkrn h h', _, _, hy => .vkrn (h.weaken hy) (h'.weaken hy)
  | _, _, _, .vblk h h', _, _, hy => .vblk (h.weaken hy) (h'.weaken hy)
  | _, _, _, .reshap he hτ₀ hτ, _, _, hy =>
      .reshap (he.weaken hy) (hτ₀.weaken hy) (hτ.weaken hy)
  | _, _, _, .vtrans h, _, _, hy => .vtrans (h.weaken hy)
  | _, _, _, .gsvdS he ha hb, _, _, hy =>
      .gsvdS (he.weaken hy) (ha.weaken hy) (hb.weaken hy)
  | _, _, _, .gsvdU he ha hb, _, _, hy =>
      .gsvdU (he.weaken hy) (ha.weaken hy) (hb.weaken hy)
  | _, _, _, .gsvdUI he ha hb, _, _, hy =>
      .gsvdUI (he.weaken hy) (ha.weaken hy) (hb.weaken hy)
  | _, _, _, .gsvdV he ha hb, _, _, hy =>
      .gsvdV (he.weaken hy) (ha.weaken hy) (hb.weaken hy)
  | _, _, _, .gsvdVI he ha hb, _, _, hy =>
      .gsvdVI (he.weaken hy) (ha.weaken hy) (hb.weaken hy)
  | _, _, _, .pinv_tensor h, _, _, hy => .pinv_tensor (h.weaken hy)
  | _, _, _, .pinv_raw h hd, _, _, hy => .pinv_raw (h.weaken hy) hd
  | _, _, _, .gpinv he ha hb, _, _, hy =>
      .gpinv (he.weaken hy) (ha.weaken hy) (hb.weaken hy)
  | _, _, _, .rrefRep h₀ h₁, _, _, hy => .rrefRep (h₀.weaken hy) (h₁.weaken hy)
  | _, _, _, .inv_tensor h, _, _, hy => .inv_tensor (h.weaken hy)
  | _, _, _, .inv_raw h hd, _, _, hy => .inv_raw (h.weaken hy) hd
  | _, _, _, .svds he, _, _, hy => .svds (he.weaken hy)

end

end GLang.RuntimeValue
