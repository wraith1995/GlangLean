import GLang.Value.Typing
import GLang.Value.Supporting.StrictTyping
import GLang.Proofs.Value.Typing.ValueDeclaredAnnotations

namespace GLang.RuntimeValue
open ValueDependency
mutual
  theorem ValSValid.declared {ε : ValCtx} {s : ValSpace} (h : ValSValid ε s) :
      spaceDeclared ε s :=
    match h with
    | .real => trivial
    | .empty => trivial
    | .dsum h0 h1 => ⟨h0.declared, h1.declared⟩
    | .tprod h0 h1 => ⟨h0.declared, h1.declared⟩
    | .ffs h0 h1 he => ⟨⟨h0.declared, h1.declared⟩, he.declared⟩
  termination_by structural h

  theorem ValTValid.declared {ε : ValCtx} {t : ValTy} {k : ValKind}
      (h : ValTValid ε t k) : typeDeclared ε t :=
    match h with
    | .space hs => hs.declared
    | @ValTValid.piTy ε d c k0 k1 L hd hb => by
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ c.fv ∪ ε.fvSupport)
      simp only [Finset.mem_union, not_or] at hx
      exact ⟨hd.declared, typeDeclared_open_inv ε x d hx.2 c 0 hx.1.2
        (hb x hx.1.1).declared⟩
  termination_by structural h

  theorem ValHasType.declared {ε : ValCtx} {e : ValExpr} {t : ValTy}
      (h : ValHasType ε e t) : exprDeclared ε e :=
    match h with
    | .var hl => hl
    | .zero hs => hs.declared
    | .rlit _ => trivial
    | .scale h0 h1 => ⟨h0.declared, h1.declared⟩
    | .vadd h0 h1 hs => ⟨hs.declared, h0.declared, h1.declared⟩
    | .dsumE h0 h1 => ⟨h0.declared, h1.declared⟩
    | .tprodE h0 h1 => ⟨h0.declared, h1.declared⟩
    | .delta hs => hs.declared
    | .idelta hs => hs.declared
    | .ttv_space hs h0 h1 => ⟨hs.declared, h0.declared, h1.declared⟩
    | .ttv_real hs h0 h1 _ => ⟨hs.declared, h0.declared, h1.declared⟩
    | .mtm hs ht h0 h1 => ⟨hs.declared, ht.declared, h0.declared, h1.declared⟩
    | @ValHasType.vsum ε s0 s es hs hb ht hdet => by
      refine ⟨hs.declared, ?_⟩
      have hi : ∀ e ∈ es, exprDeclared ε e := fun e he => (hb e he).declared
      clear hb hdet
      induction es with
      | nil => trivial
      | cons e es ih => exact ⟨hi e (by simp), ih (fun e he => hi e (by simp [he]))⟩
    | @ValHasType.vlam ε d c kd kc body L ht hb => by
      have ht' := ht.declared
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ body.fv ∪ ε.fvSupport)
      simp only [Finset.mem_union, not_or] at hx
      exact ⟨ht'.1, ht'.2, exprDeclared_open_inv ε x d hx.2 body 0 hx.1.2
        (hb x hx.1.1).declared⟩
    | .appV hf ha _ _ => ⟨hf.declared, ha.declared⟩
    | .vkrn h0 h1 => ⟨h0.declared, h1.declared⟩
    | .vblk h0 h1 => ⟨h0.declared, h1.declared⟩
    | .reshap he hs ht => ⟨he.declared, ht.declared, hs.declared⟩
    | .vtrans he => he.declared
    | .gsvdS he ha hb => ⟨he.declared, ha.declared, hb.declared⟩
    | .gsvdU he ha hb => ⟨he.declared, ha.declared, hb.declared⟩
    | .gsvdUI he ha hb => ⟨he.declared, ha.declared, hb.declared⟩
    | .gsvdV he ha hb => ⟨he.declared, ha.declared, hb.declared⟩
    | .gsvdVI he ha hb => ⟨he.declared, ha.declared, hb.declared⟩
    | .pinv_tensor he => he.declared
    | .pinv_raw he _ => he.declared
    | .gpinv he ha hb => ⟨he.declared, ha.declared, hb.declared⟩
    | .rrefRep h0 h1 => ⟨h0.declared, h1.declared⟩
    | .inv_tensor he => he.declared
    | .inv_raw he _ => he.declared
    | .svds he => he.declared
  termination_by structural h
end
end GLang.RuntimeValue
