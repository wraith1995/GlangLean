import GLang.Value.Inference
import GLang.Proofs.Value.Binding.ValueBeta

namespace GLang

/-- The base-space projection of a closed type is closed. -/
theorem ValTy.lc.spaceOf {t : ValTy} (h : t.lc) : t.spaceOf.lc := by
  cases h with
  | space hs => exact hs
  | piTy => exact .empty

/-- The domain of a closed function type is closed. -/
theorem ValTy.lc.domain {t : ValTy} (h : t.lc) : t.domain.lc := by
  cases h with
  | space hs => exact .space hs
  | piTy _ hd _ => exact hd

private theorem lc_space_inv {s : ValSpace} (h : ValTy.lc (.space s)) : s.lc := by
  cases h; assumption
private theorem lc_tprod_inv {s t : ValSpace} (h : ValSpace.lc (.tprod s t)) : s.lc ∧ t.lc := by
  cases h; constructor <;> assumption

/-- Inference preserves local closure, including substituted application results. -/
theorem ValExpr.lc.inferType : ∀ {e : ValExpr}, ValExpr.lc e → (ValExpr.inferType e).lc
  | _, .var ht => ht
  | _, .vlam L hd hc _ => .piTy L hd hc
  | _, .zero hs => .space hs
  | _, .rlit => .space .real
  | _, .scale _ hb => hb.inferType
  | _, .vadd hs _ _ => .space hs
  | _, .dsumE ha hb => .space (.dsum ha.inferType.spaceOf hb.inferType.spaceOf)
  | _, .tprodE ha hb => .space (.tprod ha.inferType.spaceOf hb.inferType.spaceOf)
  | _, .delta hs => .space hs
  | _, .idelta hs => .space (.tprod hs hs)
  | .vsum _ [], .vsum _ _ => .space .empty
  | .vsum _ (e :: es), .vsum _ he => (he e (by simp)).inferType
  | .appV f a, .appV hf ha => by
    have h := hf.inferType
    simp only [ValExpr.inferType]
    split
    · rename_i d c heq
      exact ValTy.applyCodomain_lc (heq ▸ h) ha
    · exact .space .empty
  | _, .reshap _ ht _ => ht
  | _, .ttv hs h0 h1 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]
  | _, .mtm hs ht h0 h1 => by
    have hi0 := h0.inferType
    have hi1 := h1.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals obtain ⟨ha1, hb1⟩ := lc_tprod_inv (lc_space_inv hi1)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]
  | _, .vkrn h0 h1 => by
    have hi0 := h0.inferType
    have hi1 := h1.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals obtain ⟨ha1, hb1⟩ := lc_tprod_inv (lc_space_inv hi1)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]
  | _, .vblk h0 h1 => by
    have hi0 := h0.inferType
    have hi1 := h1.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals obtain ⟨ha1, hb1⟩ := lc_tprod_inv (lc_space_inv hi1)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]
  | _, .vtrans h0 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]
  | _, .pinv h0 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split
    · rename_i a b heq
      have hp := lc_tprod_inv (lc_space_inv (heq ▸ hi0))
      exact .space (.tprod hp.2 hp.1)
    · rename_i a heq
      exact .space (.tprod .real (lc_space_inv (heq ▸ hi0)))
    · exact .space .empty

  | _, .inv h0 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split
    · rename_i a b heq
      have hp := lc_tprod_inv (lc_space_inv (heq ▸ hi0))
      exact .space (.tprod hp.2 hp.1)
    · rename_i a heq
      exact .space (.tprod .real (lc_space_inv (heq ▸ hi0)))
    · exact .space .empty

  | _, .svds h0 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    exact .space (.tprod (.ffs (.tprod ha0 hb0) h0) (.ffs (.tprod ha0 hb0) h0))

  | _, .rrefRep h0 h1 => by
    have hi0 := h1.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]
  | _, .gsvdS h0 h1 h2 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    exact .space (.tprod (.ffs (.tprod ha0 hb0) h0) (.ffs (.tprod ha0 hb0) h0))

  | _, .gsvdU h0 h1 h2 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]
  | _, .gsvdUI h0 h1 h2 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]
  | _, .gsvdV h0 h1 h2 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]
  | _, .gsvdVI h0 h1 h2 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]
  | _, .gpinv h0 h1 h2 => by
    have hi0 := h0.inferType
    simp only [ValExpr.inferType]
    split <;> try simp_all only []
    all_goals try exact .space .empty
    all_goals try exact .space .real
    all_goals obtain ⟨ha0, hb0⟩ := lc_tprod_inv (lc_space_inv hi0)
    all_goals solve_by_elim (maxDepth := 10) [ValTy.lc.space, ValSpace.lc.empty,
      ValSpace.lc.real, ValSpace.lc.tprod, ValSpace.lc.dsum, ValSpace.lc.ffs]

/-- An empty bound-variable stack agrees with context-free inference. -/
theorem ValExpr.inferTypeCtx_nil (e : ValExpr) :
    ValExpr.inferTypeCtx [] e = ValExpr.inferType e := by
  apply ValExpr.rec
    (motive_1 := fun _ => True)
    (motive_2 := fun _ => True)
    (motive_3 := fun e => ValExpr.inferTypeCtx [] e = ValExpr.inferType e)
    (motive_4 := fun es => ∀ e ∈ es, ValExpr.inferTypeCtx [] e = ValExpr.inferType e)
  all_goals intros
  all_goals try trivial
  all_goals try simp_all only [ValExpr.inferTypeCtx, ValExpr.inferType]
  case vsum =>
    rename_i s es ih
    cases es with
    | nil => rfl
    | cons e es => exact ih e (by simp)

  all_goals aesop

end GLang
