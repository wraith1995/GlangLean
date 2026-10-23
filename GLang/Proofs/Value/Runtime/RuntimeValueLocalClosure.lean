import GLang.Value.Typing
import GLang.Value.Supporting.StrictTyping
import GLang.Proofs.Value.Binding.ValueLN

namespace GLang.RuntimeValue

/-- Structural input contract used only to derive local closure. -/
def ContextLocallyClosed (ε : ValCtx) : Prop :=
  ∀ x τ, ε.lookup x = some τ → ValTy.lc τ

theorem ContextLocallyClosed.insert {ε : ValCtx} (h : ContextLocallyClosed ε)
    (x : VName) (τ : ValTy) (ht : ValTy.lc τ) :
    ContextLocallyClosed (Finmap.insert x τ ε) := by
  intro z u hz
  by_cases hx : z = x
  · subst z
    simp only [Finmap.lookup_insert, Option.some.injEq] at hz
    subst u
    exact ht
  · exact h z u (by simpa only [Finmap.lookup_insert_of_ne _ hx] using hz)

private theorem space_lc_inv {s : ValSpace} (h : ValTy.lc (.space s)) : ValSpace.lc s :=
  by cases h; assumption
private theorem tensor_lc_inv {s t : ValSpace} (h : ValTy.lc (.space (.tprod s t))) :
    ValSpace.lc s ∧ ValSpace.lc t := by
  cases h with
  | space h => cases h with | tprod hs ht => exact ⟨hs, ht⟩

mutual
 theorem originalSpace_lc {ε : ValCtx} {s : ValSpace}
    (h : ValSValid ε s) (hc : ContextLocallyClosed ε) : ValSpace.lc s :=
  match h with
  | .real => by exact .real
  | .empty => by exact .empty
  | .dsum h0 h1 => by exact .dsum (originalSpace_lc h0 hc) (originalSpace_lc h1 hc)
  | .tprod h0 h1 => by exact .tprod (originalSpace_lc h0 hc) (originalSpace_lc h1 hc)
  | .ffs h0 h1 he => by
    exact .ffs (.tprod (originalSpace_lc h0 hc) (originalSpace_lc h1 hc))
      (originalExpr_lc he hc).1

 termination_by structural h

 theorem originalType_lc {ε : ValCtx} {τ : ValTy} {k : ValKind}
    (h : ValTValid ε τ k) (hc : ContextLocallyClosed ε) : ValTy.lc τ :=
  match h with
  | .space hs => by exact .space (originalSpace_lc hs hc)
  | .piTy L hd hb => by
    have hdl := originalType_lc hd hc
    exact .piTy L hdl (fun x hx => originalType_lc (hb x hx) (hc.insert x _ hdl))

 termination_by structural h

 theorem originalExpr_lc {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (h : ValHasType ε e τ) (hc : ContextLocallyClosed ε) : ValExpr.lc e ∧ ValTy.lc τ :=
  match h with
  | .var hx => by exact ⟨.var (hc _ _ hx), hc _ _ hx⟩
  | .zero hs => by exact ⟨.zero (originalSpace_lc hs hc), .space (originalSpace_lc hs hc)⟩
  | .rlit r => by exact ⟨.rlit, .space .real⟩
  | .scale h0 h1 => by
    have a := originalExpr_lc h0 hc; have b := originalExpr_lc h1 hc
    exact ⟨.scale a.1 b.1, b.2⟩
  | .vadd h0 h1 hs => by
    have a := originalExpr_lc h0 hc; have b := originalExpr_lc h1 hc
    exact ⟨.vadd (originalSpace_lc hs hc) a.1 b.1, .space (originalSpace_lc hs hc)⟩
  | .dsumE h0 h1 => by
    have a := originalExpr_lc h0 hc; have b := originalExpr_lc h1 hc
    exact ⟨.dsumE a.1 b.1, .space (.dsum (space_lc_inv a.2) (space_lc_inv b.2))⟩
  | .tprodE h0 h1 => by
    have a := originalExpr_lc h0 hc; have b := originalExpr_lc h1 hc
    exact ⟨.tprodE a.1 b.1, .space (.tprod (space_lc_inv a.2) (space_lc_inv b.2))⟩
  | .delta hs => by exact ⟨.delta (originalSpace_lc hs hc), .space (originalSpace_lc hs hc)⟩
  | .idelta hs => by
    have a := originalSpace_lc hs hc
    exact ⟨.idelta a, .space (.tprod a a)⟩
  | .ttv_space hs h0 h1 => by
    have a := originalExpr_lc h0 hc; have b := originalExpr_lc h1 hc
    exact ⟨.ttv (originalSpace_lc hs hc) a.1 b.1, .space (tensor_lc_inv a.2).2⟩
  | .ttv_real hs h0 h1 _ => by
    exact ⟨.ttv (originalSpace_lc hs hc) (originalExpr_lc h0 hc).1
      (originalExpr_lc h1 hc).1, .space .real⟩
  | .mtm hs ht h0 h1 => by
    have a := originalExpr_lc h0 hc; have b := originalExpr_lc h1 hc
    exact ⟨.mtm (originalSpace_lc hs hc) (originalSpace_lc ht hc) a.1 b.1,
      .space (.tprod (tensor_lc_inv b.2).1 (tensor_lc_inv a.2).2)⟩
  | .vsum hs hb ht _ => by
    exact ⟨.vsum (originalSpace_lc hs hc) (fun e he => (originalExpr_lc (hb e he) hc).1),
      .space (originalSpace_lc ht hc)⟩
  | .vlam L ht hb => by
    have hpi := originalType_lc ht hc
    cases hpi with
    | piTy L' hd hcod =>
      refine ⟨.vlam (L ∪ L') hd ?_ ?_, .piTy L' hd hcod⟩
      · intro x hx
        exact hcod x ((not_or.mp (by simpa only [Finset.mem_union] using hx)).2)
      · intro x hx
        have hxL : x ∉ L := (not_or.mp (by simpa only [Finset.mem_union] using hx)).1
        exact (originalExpr_lc (hb x hxL) (hc.insert x _ hd)).1
  | .appV h0 h1 _ ht => by
    have a := originalExpr_lc h0 hc; have b := originalExpr_lc h1 hc
    have t := originalType_lc ht hc
    exact ⟨.appV a.1 b.1, t⟩
  | .vkrn h0 h1 => by
    have a := originalExpr_lc h0 hc; have b := originalExpr_lc h1 hc
    have p := tensor_lc_inv a.2; have q := tensor_lc_inv b.2
    exact ⟨.vkrn a.1 b.1, .space (.tprod (.tprod p.1 q.1) (.tprod p.2 q.2))⟩
  | .vblk h0 h1 => by
    have a := originalExpr_lc h0 hc; have b := originalExpr_lc h1 hc
    have p := tensor_lc_inv a.2; have q := tensor_lc_inv b.2
    exact ⟨.vblk a.1 b.1, .space (.tprod (.dsum p.1 q.1) (.dsum p.2 q.2))⟩
  | .reshap he h0 h1 => by
    have a := originalExpr_lc he hc; have t := originalType_lc h1 hc
    exact ⟨.reshap a.1 t (originalType_lc h0 hc), t⟩
  | .vtrans he => by
    have a := originalExpr_lc he hc; have p := tensor_lc_inv a.2
    exact ⟨.vtrans a.1, .space (.tprod p.2 p.1)⟩
  | .gsvdS he ha hb => by
    have a := originalExpr_lc he hc; have b := originalExpr_lc ha hc; have c := originalExpr_lc hb hc
    have p := tensor_lc_inv a.2
    have f : ∀ q, ValSpace.lc (.ffs q _ _) := fun _ => .ffs (space_lc_inv a.2) a.1
    exact ⟨.gsvdS a.1 b.1 c.1, .space (.tprod (f .cokernel) (f .image))⟩
  | .gsvdU he ha hb => by
    have a := originalExpr_lc he hc; have b := originalExpr_lc ha hc; have c := originalExpr_lc hb hc
    have p := tensor_lc_inv a.2
    have f : ∀ q, ValSpace.lc (.ffs q _ _) := fun _ => .ffs (space_lc_inv a.2) a.1
    exact ⟨.gsvdU a.1 b.1 c.1, .space (.tprod p.1 (f _))⟩
  | .gsvdUI he ha hb => by
    have a := originalExpr_lc he hc; have b := originalExpr_lc ha hc; have c := originalExpr_lc hb hc
    have p := tensor_lc_inv a.2
    have f : ∀ q, ValSpace.lc (.ffs q _ _) := fun _ => .ffs (space_lc_inv a.2) a.1
    exact ⟨.gsvdUI a.1 b.1 c.1, .space (.tprod p.1 (f _))⟩
  | .gsvdV he ha hb => by
    have a := originalExpr_lc he hc; have b := originalExpr_lc ha hc; have c := originalExpr_lc hb hc
    have p := tensor_lc_inv a.2
    have f : ∀ q, ValSpace.lc (.ffs q _ _) := fun _ => .ffs (space_lc_inv a.2) a.1
    exact ⟨.gsvdV a.1 b.1 c.1, .space (.tprod p.2 (f _))⟩
  | .gsvdVI he ha hb => by
    have a := originalExpr_lc he hc; have b := originalExpr_lc ha hc; have c := originalExpr_lc hb hc
    have p := tensor_lc_inv a.2
    have f : ∀ q, ValSpace.lc (.ffs q _ _) := fun _ => .ffs (space_lc_inv a.2) a.1
    exact ⟨.gsvdVI a.1 b.1 c.1, .space (.tprod p.2 (f _))⟩
  | .pinv_tensor he => by
    have a := originalExpr_lc he hc; have p := tensor_lc_inv a.2
    exact ⟨.pinv a.1, .space (.tprod p.2 p.1)⟩
  | .pinv_raw he _ => by
    have a := originalExpr_lc he hc
    exact ⟨.pinv a.1, .space (.tprod .real (space_lc_inv a.2))⟩
  | .inv_tensor he => by
    have a := originalExpr_lc he hc; have p := tensor_lc_inv a.2
    exact ⟨.inv a.1, .space (.tprod p.2 p.1)⟩
  | .inv_raw he _ => by
    have a := originalExpr_lc he hc
    exact ⟨.inv a.1, .space (.tprod .real (space_lc_inv a.2))⟩
  | .gpinv he ha hb => by
    have a := originalExpr_lc he hc; have b := originalExpr_lc ha hc; have c := originalExpr_lc hb hc
    have p := tensor_lc_inv a.2
    exact ⟨.gpinv a.1 b.1 c.1, .space (.tprod p.2 p.1)⟩
  | .rrefRep h0 h1 => by
    have a := originalExpr_lc h0 hc; have b := originalExpr_lc h1 hc
    have p := tensor_lc_inv b.2
    exact ⟨.rrefRep a.1 b.1, .space (.tprod p.2 p.1)⟩
  | .svds he => by
    have a := originalExpr_lc he hc
    exact ⟨.svds a.1, .space (.tprod (.ffs (space_lc_inv a.2) a.1) (.ffs (space_lc_inv a.2) a.1))⟩
 termination_by structural h
end

end GLang.RuntimeValue
