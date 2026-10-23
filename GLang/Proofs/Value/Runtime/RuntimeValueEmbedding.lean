import GLang.Proofs.Value.Runtime.RuntimeValueRegular
import GLang.Proofs.Value.Soundness.ValueSoundVals

namespace GLang

mutual

def ValSValid.runtime : {ε : ValCtx} → {s : ValSpace} → ValSValid ε s → RuntimeValue.ValSValid ε s
  | _, _, .real => .real
  | _, _, .empty => .empty
  | _, _, .dsum h₀ h₁ => .dsum (h₀.runtime) (h₁.runtime)
  | _, _, .tprod h₀ h₁ => .tprod (h₀.runtime) (h₁.runtime)
  | _, _, .ffs h₀ h₁ he =>
      .ffs (h₀.runtime) (h₁.runtime) (he.runtime)

def ValTValid.runtime : {ε : ValCtx} → {τ : ValTy} → {k : ValKind} → ValTValid ε τ k → RuntimeValue.ValTValid ε τ k
  | _, _, _, .space hs => .space (hs.runtime)
  | _, _, _, .piTy L hd hc => .piTy L hd.runtime (fun x hx => (hc x hx).runtime)

def ValHasType.runtime : {ε : ValCtx} → {e : ValExpr} → {τ : ValTy} → ValHasType ε e τ → RuntimeValue.ValHasType ε e τ
  | _, _, _, .var hl => .var hl
  | _, _, _, .zero hsv => .zero (hsv.runtime)
  | _, _, _, .rlit r => .rlit r
  | _, _, _, .scale h₀ h₁ => .scale (h₀.runtime) (h₁.runtime)
  | _, _, _, .vadd h₀ h₁ hs => .vadd (h₀.runtime) (h₁.runtime) (hs.runtime)
  | _, _, _, .dsumE h₀ h₁ => .dsumE (h₀.runtime) (h₁.runtime)
  | _, _, _, .tprodE h₀ h₁ => .tprodE (h₀.runtime) (h₁.runtime)
  | _, _, _, .delta hsv => .delta (hsv.runtime)
  | _, _, _, .idelta hsv => .idelta (hsv.runtime)
  | _, _, _, .ttv_space hsv h₀ h₁ =>
      .ttv_space (hsv.runtime) (h₀.runtime) (h₁.runtime)
  | _, _, _, .ttv_real hsv h₀ h₁ hd =>
      .ttv_real (hsv.runtime) (h₀.runtime) (h₁.runtime) hd
  | _, _, _, .mtm hsv hsv1 h₀ h₁ =>
      .mtm (hsv.runtime) (hsv1.runtime) (h₀.runtime) (h₁.runtime)
  | _, _, _, .vsum hsv hbody hsvr hdet =>
      .vsum (hsv.runtime) (fun e he => (hbody e he).runtime) (hsvr.runtime) hdet
  | _, _, _, .vlam L ht hb => .vlam L ht.runtime (fun x hx => (hb x hx).runtime)
  | _, _, _, .appV h₀ h₁ _heq htval =>
      .appV (h₀.runtime) (h₁.runtime) _heq (htval.runtime)
  | _, _, _, .vkrn h h' => .vkrn (h.runtime) (h'.runtime)
  | _, _, _, .vblk h h' => .vblk (h.runtime) (h'.runtime)
  | _, _, _, .reshap he hτ₀ hτ =>
      .reshap (he.runtime) (hτ₀.runtime) (hτ.runtime)
  | _, _, _, .vtrans h => .vtrans (h.runtime)
  | _, _, _, .gsvdS he ha hb =>
      .gsvdS (he.runtime) (ha.runtime) (hb.runtime)
  | _, _, _, .gsvdU he ha hb =>
      .gsvdU (he.runtime) (ha.runtime) (hb.runtime)
  | _, _, _, .gsvdUI he ha hb =>
      .gsvdUI (he.runtime) (ha.runtime) (hb.runtime)
  | _, _, _, .gsvdV he ha hb =>
      .gsvdV (he.runtime) (ha.runtime) (hb.runtime)
  | _, _, _, .gsvdVI he ha hb =>
      .gsvdVI (he.runtime) (ha.runtime) (hb.runtime)
  | _, _, _, .pinv_tensor h => .pinv_tensor (h.runtime)
  | _, _, _, .pinv_raw h hd => .pinv_raw (h.runtime) hd
  | _, _, _, .gpinv he ha hb =>
      .gpinv (he.runtime) (ha.runtime) (hb.runtime)
  | _, _, _, .rrefRep h₀ h₁ => .rrefRep (h₀.runtime) (h₁.runtime)
  | _, _, _, .inv_tensor h => .inv_tensor (h.runtime)
  | _, _, _, .inv_raw h hd => .inv_raw (h.runtime) hd
  | _, _, _, .svds he => .svds (he.runtime)

end

noncomputable def ValCtxValid.runtime (h : ValCtxValid ε) : RuntimeValue.ValCtxValid ε :=
  fun x t hl => ⟨(h x t hl).1, (h x t hl).2.runtime⟩

end GLang
