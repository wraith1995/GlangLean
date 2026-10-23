/- Semantic invariance of de Bruijn raising, derived from the oracle opening law. -/
import GLang.Value.Inference

namespace GLang.ValRaise

def dummy : ValExpr := .rlit 0

mutual
  theorem open_raise_space (n cutoff : Nat) : ∀ s : ValSpace,
      ValSpace.openRec (cutoff + n) dummy (ValSpace.raise n cutoff s) =
        ValSpace.raise n (cutoff + 1) (ValSpace.openRec cutoff dummy s)
    | .empty => rfl
    | .real => rfl
    | .dsum s0 s1 => by
        simp [ValSpace.openRec, ValSpace.raise, open_raise_space n cutoff s0,
          open_raise_space n cutoff s1]
    | .tprod s0 s1 => by
        simp [ValSpace.openRec, ValSpace.raise, open_raise_space n cutoff s0,
          open_raise_space n cutoff s1]
    | .ffs p s e => by
        simp [ValSpace.openRec, ValSpace.raise, open_raise_space n cutoff s,
          open_raise_expr n cutoff e]

  theorem open_raise_ty (n cutoff : Nat) : ∀ t : ValTy,
      ValTy.openRec (cutoff + n) dummy (ValTy.raise n cutoff t) =
        ValTy.raise n (cutoff + 1) (ValTy.openRec cutoff dummy t)
    | .space s => by
        simp [ValTy.openRec, ValTy.raise, open_raise_space n cutoff s]
    | .piTy t0 t1 => by
        simp only [ValTy.openRec, ValTy.raise]
        rw [open_raise_ty n cutoff t0]
        have h := open_raise_ty n (cutoff + 1) t1
        apply congrArg (ValTy.piTy (ValTy.raise n (cutoff + 1)
          (ValTy.openRec cutoff dummy t0)))
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

  theorem open_raise_expr (n cutoff : Nat) : ∀ e : ValExpr,
      ValExpr.openRec (cutoff + n) dummy (ValExpr.raise n cutoff e) =
        ValExpr.raise n (cutoff + 1) (ValExpr.openRec cutoff dummy e)
    | .bvar i => by
        by_cases hci : cutoff ≤ i
        · by_cases hic : i = cutoff
          · subst i
            simp [ValExpr.raise, ValExpr.openRec, dummy]
          · have hcsi : cutoff + 1 ≤ i := by omega
            have hsum : i + n ≠ cutoff + n := by omega
            simp [ValExpr.raise, ValExpr.openRec, hci, hic, hcsi]
        · have hic : i ≠ cutoff := by omega
          have hcsi : ¬ cutoff + 1 ≤ i := by omega
          have hsum : i ≠ cutoff + n := by omega
          simp [ValExpr.raise, ValExpr.openRec, hci, hic, hcsi, hsum]
    | .var x t => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_ty n cutoff t]
    | .vlam t0 t1 e => by
        simp only [ValExpr.openRec, ValExpr.raise]
        rw [open_raise_ty n cutoff t0]
        have ht := open_raise_ty n (cutoff + 1) t1
        have he := open_raise_expr n (cutoff + 1) e
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          congrArg₂ (fun t e => ValExpr.vlam (ValTy.raise n (cutoff + 1)
            (ValTy.openRec cutoff dummy t0)) t e) ht he
    | .zero s => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_space n cutoff s]
    | .rlit r => rfl
    | .scale e0 e1 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e0,
          open_raise_expr n cutoff e1]
    | .vadd s e0 e1 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_space n cutoff s,
          open_raise_expr n cutoff e0, open_raise_expr n cutoff e1]
    | .dsumE e0 e1 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e0,
          open_raise_expr n cutoff e1]
    | .tprodE e0 e1 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e0,
          open_raise_expr n cutoff e1]
    | .delta i s => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_space n cutoff s]
    | .idelta s => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_space n cutoff s]
    | .vsum s es => by
        simp only [ValExpr.openRec, ValExpr.raise, open_raise_space n cutoff s]
        congr 1
        exact open_raise_expr_list n cutoff es
    | .ttv s e0 e1 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_space n cutoff s,
          open_raise_expr n cutoff e0, open_raise_expr n cutoff e1]
    | .mtm i j s0 s1 e0 e1 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_space n cutoff s0,
          open_raise_space n cutoff s1, open_raise_expr n cutoff e0,
          open_raise_expr n cutoff e1]
    | .appV e0 e1 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e0,
          open_raise_expr n cutoff e1]
    | .vkrn e0 e1 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e0,
          open_raise_expr n cutoff e1]
    | .vblk e0 e1 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e0,
          open_raise_expr n cutoff e1]
    | .reshap e t t0 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e,
          open_raise_ty n cutoff t, open_raise_ty n cutoff t0]
    | .vtrans e => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e]
    | .gsvdS e a b => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e,
          open_raise_expr n cutoff a, open_raise_expr n cutoff b]
    | .gsvdU e a b => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e,
          open_raise_expr n cutoff a, open_raise_expr n cutoff b]
    | .gsvdUI e a b => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e,
          open_raise_expr n cutoff a, open_raise_expr n cutoff b]
    | .gsvdV e a b => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e,
          open_raise_expr n cutoff a, open_raise_expr n cutoff b]
    | .gsvdVI e a b => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e,
          open_raise_expr n cutoff a, open_raise_expr n cutoff b]
    | .pinv e => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e]
    | .gpinv e a b => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e,
          open_raise_expr n cutoff a, open_raise_expr n cutoff b]
    | .rrefRep e0 e1 => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e0,
          open_raise_expr n cutoff e1]
    | .inv e => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e]
    | .svds e => by
        simp [ValExpr.openRec, ValExpr.raise, open_raise_expr n cutoff e]

  theorem open_raise_expr_list (n cutoff : Nat) : ∀ es : List ValExpr,
      ValExpr.openRecList (cutoff + n) dummy (ValExpr.raiseList n cutoff es) =
        ValExpr.raiseList n (cutoff + 1) (ValExpr.openRecList cutoff dummy es)
    | [] => rfl
    | e :: es => by
        change
          ValExpr.openRec (cutoff + n) dummy (ValExpr.raise n cutoff e) ::
              ValExpr.openRecList (cutoff + n) dummy (ValExpr.raiseList n cutoff es) =
            ValExpr.raise n (cutoff + 1) (ValExpr.openRec cutoff dummy e) ::
              ValExpr.raiseList n (cutoff + 1) (ValExpr.openRecList cutoff dummy es)
        rw [open_raise_expr n cutoff e, open_raise_expr_list n cutoff es]
end

/-! A deliberately coarse bound: the largest raw numeral occurring in any
`bvar`, ignoring binder depth.  Ignoring depth only over-approximates support,
which keeps the proofs simple. -/
mutual
  def bmaxSpace : ValSpace -> Nat
    | .empty | .real => 0
    | .dsum s0 s1 | .tprod s0 s1 => max (bmaxSpace s0) (bmaxSpace s1)
    | .ffs _ s e => max (bmaxSpace s) (bmaxExpr e)

  def bmaxTy : ValTy -> Nat
    | .space s => bmaxSpace s
    | .piTy t0 t1 => max (bmaxTy t0) (bmaxTy t1)

  def bmaxExpr : ValExpr -> Nat
    | .bvar i => i
    | .var _ t => bmaxTy t
    | .vlam t0 t1 e => max (bmaxTy t0) (max (bmaxTy t1) (bmaxExpr e))
    | .zero s | .delta _ s | .idelta s => bmaxSpace s
    | .rlit _ => 0
    | .scale e0 e1 | .dsumE e0 e1 | .tprodE e0 e1 |
        .vkrn e0 e1 | .vblk e0 e1 | .rrefRep e0 e1 =>
        max (bmaxExpr e0) (bmaxExpr e1)
    | .vadd s e0 e1 | .ttv s e0 e1 =>
        max (bmaxSpace s) (max (bmaxExpr e0) (bmaxExpr e1))
    | .vsum s es => max (bmaxSpace s) (bmaxExprList es)
    | .mtm _ _ s0 s1 e0 e1 =>
        max (bmaxSpace s0) (max (bmaxSpace s1)
          (max (bmaxExpr e0) (bmaxExpr e1)))
    | .appV e0 e1 => max (bmaxExpr e0) (bmaxExpr e1)
    | .reshap e t t0 => max (bmaxExpr e) (max (bmaxTy t) (bmaxTy t0))
    | .vtrans e | .pinv e | .inv e | .svds e => bmaxExpr e
    | .gsvdS e a b | .gsvdU e a b | .gsvdUI e a b |
        .gsvdV e a b | .gsvdVI e a b | .gpinv e a b =>
        max (bmaxExpr e) (max (bmaxExpr a) (bmaxExpr b))

  def bmaxExprList : List ValExpr -> Nat
    | [] => 0
    | e :: es => max (bmaxExpr e) (bmaxExprList es)
end

mutual
  theorem raiseSpace_eq_of_bmax (n cutoff : Nat) : ∀ s : ValSpace,
      bmaxSpace s < cutoff -> ValSpace.raise n cutoff s = s
    | .empty, _ => rfl
    | .real, _ => rfl
    | .dsum s0 s1, h => by
        simp only [bmaxSpace, Nat.max_lt] at h
        simp [ValSpace.raise, raiseSpace_eq_of_bmax n cutoff s0 h.1,
          raiseSpace_eq_of_bmax n cutoff s1 h.2]
    | .tprod s0 s1, h => by
        simp only [bmaxSpace, Nat.max_lt] at h
        simp [ValSpace.raise, raiseSpace_eq_of_bmax n cutoff s0 h.1,
          raiseSpace_eq_of_bmax n cutoff s1 h.2]
    | .ffs p s e, h => by
        simp only [bmaxSpace, Nat.max_lt] at h
        simp [ValSpace.raise, raiseSpace_eq_of_bmax n cutoff s h.1,
          raiseExpr_eq_of_bmax n cutoff e h.2]

  theorem raiseTy_eq_of_bmax (n cutoff : Nat) : ∀ t : ValTy,
      bmaxTy t < cutoff -> ValTy.raise n cutoff t = t
    | .space s, h => by
        simp only [bmaxTy] at h
        simp [ValTy.raise, raiseSpace_eq_of_bmax n cutoff s h]
    | .piTy t0 t1, h => by
        simp only [bmaxTy, Nat.max_lt] at h
        simp [ValTy.raise, raiseTy_eq_of_bmax n cutoff t0 h.1,
          raiseTy_eq_of_bmax n (cutoff + 1) t1 (by omega)]

  theorem raiseExpr_eq_of_bmax (n cutoff : Nat) : ∀ e : ValExpr,
      bmaxExpr e < cutoff -> ValExpr.raise n cutoff e = e
    | .bvar i, h => by
        simp only [bmaxExpr] at h
        simp [ValExpr.raise, Nat.not_le.mpr h]
    | .var x t, h => by
        simp only [bmaxExpr] at h
        simp [ValExpr.raise, raiseTy_eq_of_bmax n cutoff t h]
    | .vlam t0 t1 e, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseTy_eq_of_bmax n cutoff t0 h.1,
          raiseTy_eq_of_bmax n (cutoff + 1) t1 (by omega),
          raiseExpr_eq_of_bmax n (cutoff + 1) e (by omega)]
    | .zero s, h => by
        simp only [bmaxExpr] at h
        simp [ValExpr.raise, raiseSpace_eq_of_bmax n cutoff s h]
    | .rlit r, _ => rfl
    | .scale e0 e1, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e0 h.1,
          raiseExpr_eq_of_bmax n cutoff e1 h.2]
    | .vadd s e0 e1, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseSpace_eq_of_bmax n cutoff s h.1,
          raiseExpr_eq_of_bmax n cutoff e0 h.2.1,
          raiseExpr_eq_of_bmax n cutoff e1 h.2.2]
    | .dsumE e0 e1, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e0 h.1,
          raiseExpr_eq_of_bmax n cutoff e1 h.2]
    | .tprodE e0 e1, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e0 h.1,
          raiseExpr_eq_of_bmax n cutoff e1 h.2]
    | .delta i s, h => by
        simp only [bmaxExpr] at h
        simp [ValExpr.raise, raiseSpace_eq_of_bmax n cutoff s h]
    | .idelta s, h => by
        simp only [bmaxExpr] at h
        simp [ValExpr.raise, raiseSpace_eq_of_bmax n cutoff s h]
    | .vsum s es, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.raise]
        rw [raiseSpace_eq_of_bmax n cutoff s h.1,
          raiseExprList_eq_of_bmax n cutoff es h.2]
    | .ttv s e0 e1, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseSpace_eq_of_bmax n cutoff s h.1,
          raiseExpr_eq_of_bmax n cutoff e0 h.2.1,
          raiseExpr_eq_of_bmax n cutoff e1 h.2.2]
    | .mtm i j s0 s1 e0 e1, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseSpace_eq_of_bmax n cutoff s0 h.1,
          raiseSpace_eq_of_bmax n cutoff s1 h.2.1,
          raiseExpr_eq_of_bmax n cutoff e0 h.2.2.1,
          raiseExpr_eq_of_bmax n cutoff e1 h.2.2.2]
    | .appV e0 e1, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e0 h.1,
          raiseExpr_eq_of_bmax n cutoff e1 h.2]
    | .vkrn e0 e1, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e0 h.1,
          raiseExpr_eq_of_bmax n cutoff e1 h.2]
    | .vblk e0 e1, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e0 h.1,
          raiseExpr_eq_of_bmax n cutoff e1 h.2]
    | .reshap e t t0, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h.1,
          raiseTy_eq_of_bmax n cutoff t h.2.1,
          raiseTy_eq_of_bmax n cutoff t0 h.2.2]
    | .vtrans e, h => by
        simp only [bmaxExpr] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h]
    | .gsvdS e a b, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h.1,
          raiseExpr_eq_of_bmax n cutoff a h.2.1,
          raiseExpr_eq_of_bmax n cutoff b h.2.2]
    | .gsvdU e a b, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h.1,
          raiseExpr_eq_of_bmax n cutoff a h.2.1,
          raiseExpr_eq_of_bmax n cutoff b h.2.2]
    | .gsvdUI e a b, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h.1,
          raiseExpr_eq_of_bmax n cutoff a h.2.1,
          raiseExpr_eq_of_bmax n cutoff b h.2.2]
    | .gsvdV e a b, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h.1,
          raiseExpr_eq_of_bmax n cutoff a h.2.1,
          raiseExpr_eq_of_bmax n cutoff b h.2.2]
    | .gsvdVI e a b, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h.1,
          raiseExpr_eq_of_bmax n cutoff a h.2.1,
          raiseExpr_eq_of_bmax n cutoff b h.2.2]
    | .pinv e, h => by
        simp only [bmaxExpr] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h]
    | .gpinv e a b, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h.1,
          raiseExpr_eq_of_bmax n cutoff a h.2.1,
          raiseExpr_eq_of_bmax n cutoff b h.2.2]
    | .rrefRep e0 e1, h => by
        simp only [bmaxExpr, Nat.max_lt] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e0 h.1,
          raiseExpr_eq_of_bmax n cutoff e1 h.2]
    | .inv e, h => by
        simp only [bmaxExpr] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h]
    | .svds e, h => by
        simp only [bmaxExpr] at h
        simp [ValExpr.raise, raiseExpr_eq_of_bmax n cutoff e h]

  theorem raiseExprList_eq_of_bmax (n cutoff : Nat) : ∀ es : List ValExpr,
      bmaxExprList es < cutoff -> ValExpr.raiseList n cutoff es = es
    | [], _ => rfl
    | e :: es, h => by
        simp only [bmaxExprList, Nat.max_lt] at h
        simp only [ValExpr.raiseList]
        rw [raiseExpr_eq_of_bmax n cutoff e h.1,
          raiseExprList_eq_of_bmax n cutoff es h.2]
end

theorem raiseSpace_eventually_id (n : Nat) (s : ValSpace) :
    ValSpace.raise n (bmaxSpace s + 1) s = s :=
  raiseSpace_eq_of_bmax n _ s (by omega)

theorem raiseTy_eventually_id (n : Nat) (t : ValTy) :
    ValTy.raise n (bmaxTy t + 1) t = t :=
  raiseTy_eq_of_bmax n _ t (by omega)

theorem raiseExpr_eventually_id (n : Nat) (e : ValExpr) :
    ValExpr.raise n (bmaxExpr e + 1) e = e :=
  raiseExpr_eq_of_bmax n _ e (by omega)

/-! Opening with `dummy` never introduces a larger raw bound index. -/
mutual
  theorem bmax_open_space_le (k : Nat) : ∀ s : ValSpace,
      bmaxSpace (ValSpace.openRec k dummy s) ≤ bmaxSpace s
    | .empty => by simp [ValSpace.openRec, bmaxSpace]
    | .real => by simp [ValSpace.openRec, bmaxSpace]
    | .dsum s0 s1 => by
        simp only [ValSpace.openRec, bmaxSpace]
        exact max_le_max (bmax_open_space_le k s0) (bmax_open_space_le k s1)
    | .tprod s0 s1 => by
        simp only [ValSpace.openRec, bmaxSpace]
        exact max_le_max (bmax_open_space_le k s0) (bmax_open_space_le k s1)
    | .ffs p s e => by
        simp only [ValSpace.openRec, bmaxSpace]
        exact max_le_max (bmax_open_space_le k s) (bmax_open_expr_le k e)

  theorem bmax_open_ty_le (k : Nat) : ∀ t : ValTy,
      bmaxTy (ValTy.openRec k dummy t) ≤ bmaxTy t
    | .space s => by
        simpa [ValTy.openRec, bmaxTy] using bmax_open_space_le k s
    | .piTy t0 t1 => by
        simp only [ValTy.openRec, bmaxTy]
        exact max_le_max (bmax_open_ty_le k t0) (bmax_open_ty_le (k + 1) t1)

  theorem bmax_open_expr_le (k : Nat) : ∀ e : ValExpr,
      bmaxExpr (ValExpr.openRec k dummy e) ≤ bmaxExpr e
    | .bvar i => by
        by_cases h : i = k
        · subst i; simp [ValExpr.openRec, dummy, bmaxExpr]
        · simp [ValExpr.openRec, h, bmaxExpr]
    | .var x t => by
        simpa [ValExpr.openRec, bmaxExpr] using bmax_open_ty_le k t
    | .vlam t0 t1 e => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_ty_le k t0)
          (max_le_max (bmax_open_ty_le (k + 1) t1)
            (bmax_open_expr_le (k + 1) e))
    | .zero s => by
        simpa [ValExpr.openRec, bmaxExpr] using bmax_open_space_le k s
    | .rlit r => by simp [ValExpr.openRec, bmaxExpr]
    | .scale e0 e1 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e0) (bmax_open_expr_le k e1)
    | .vadd s e0 e1 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_space_le k s)
          (max_le_max (bmax_open_expr_le k e0) (bmax_open_expr_le k e1))
    | .dsumE e0 e1 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e0) (bmax_open_expr_le k e1)
    | .tprodE e0 e1 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e0) (bmax_open_expr_le k e1)
    | .delta i s => by
        simpa [ValExpr.openRec, bmaxExpr] using bmax_open_space_le k s
    | .idelta s => by
        simpa [ValExpr.openRec, bmaxExpr] using bmax_open_space_le k s
    | .vsum s es => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_space_le k s) (bmax_open_expr_list_le k es)
    | .ttv s e0 e1 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_space_le k s)
          (max_le_max (bmax_open_expr_le k e0) (bmax_open_expr_le k e1))
    | .mtm i j s0 s1 e0 e1 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_space_le k s0)
          (max_le_max (bmax_open_space_le k s1)
            (max_le_max (bmax_open_expr_le k e0) (bmax_open_expr_le k e1)))
    | .appV e0 e1 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e0) (bmax_open_expr_le k e1)
    | .vkrn e0 e1 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e0) (bmax_open_expr_le k e1)
    | .vblk e0 e1 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e0) (bmax_open_expr_le k e1)
    | .reshap e t t0 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e)
          (max_le_max (bmax_open_ty_le k t) (bmax_open_ty_le k t0))
    | .vtrans e => by
        simpa [ValExpr.openRec, bmaxExpr] using bmax_open_expr_le k e
    | .gsvdS e a b => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e)
          (max_le_max (bmax_open_expr_le k a) (bmax_open_expr_le k b))
    | .gsvdU e a b => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e)
          (max_le_max (bmax_open_expr_le k a) (bmax_open_expr_le k b))
    | .gsvdUI e a b => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e)
          (max_le_max (bmax_open_expr_le k a) (bmax_open_expr_le k b))
    | .gsvdV e a b => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e)
          (max_le_max (bmax_open_expr_le k a) (bmax_open_expr_le k b))
    | .gsvdVI e a b => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e)
          (max_le_max (bmax_open_expr_le k a) (bmax_open_expr_le k b))
    | .pinv e => by
        simpa [ValExpr.openRec, bmaxExpr] using bmax_open_expr_le k e
    | .gpinv e a b => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e)
          (max_le_max (bmax_open_expr_le k a) (bmax_open_expr_le k b))
    | .rrefRep e0 e1 => by
        simp only [ValExpr.openRec, bmaxExpr]
        exact max_le_max (bmax_open_expr_le k e0) (bmax_open_expr_le k e1)
    | .inv e => by
        simpa [ValExpr.openRec, bmaxExpr] using bmax_open_expr_le k e
    | .svds e => by
        simpa [ValExpr.openRec, bmaxExpr] using bmax_open_expr_le k e

  theorem bmax_open_expr_list_le (k : Nat) : ∀ es : List ValExpr,
      bmaxExprList (ValExpr.openRecList k dummy es) ≤ bmaxExprList es
    | [] => by simp [ValExpr.openRecList, bmaxExprList]
    | e :: es => by
        change max (bmaxExpr (ValExpr.openRec k dummy e))
            (bmaxExprList (ValExpr.openRecList k dummy es)) ≤
          max (bmaxExpr e) (bmaxExprList es)
        exact max_le_max (bmax_open_expr_le k e) (bmax_open_expr_list_le k es)
end

theorem oracle_raise_bounded (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc] (p : ValFFSProp) (n : Nat) :
    ∀ (steps cutoff : Nat) (s : ValSpace) (e : ValExpr),
      bmaxSpace s < cutoff + steps ->
      bmaxExpr e < cutoff + steps ->
      orc p (ValSpace.raise n cutoff s) (ValExpr.raise n cutoff e) = orc p s e
  | 0, cutoff, s, e, hs, he => by
      simp only [Nat.add_zero] at hs he
      rw [raiseSpace_eq_of_bmax n cutoff s hs,
        raiseExpr_eq_of_bmax n cutoff e he]
  | steps + 1, cutoff, s, e, hs, he => by
      have hs' : bmaxSpace (ValSpace.openRec cutoff dummy s) <
          (cutoff + 1) + steps := by
        have hle := bmax_open_space_le cutoff s
        omega
      have he' : bmaxExpr (ValExpr.openRec cutoff dummy e) <
          (cutoff + 1) + steps := by
        have hle := bmax_open_expr_le cutoff e
        omega
      calc
        orc p (ValSpace.raise n cutoff s) (ValExpr.raise n cutoff e) =
            orc p
              (ValSpace.openRec (cutoff + n) dummy (ValSpace.raise n cutoff s))
              (ValExpr.openRec (cutoff + n) dummy (ValExpr.raise n cutoff e)) :=
          (FFSOracle.openRec_respect orc (cutoff + n) dummy p
            (ValSpace.raise n cutoff s) (ValExpr.raise n cutoff e)).symm
        _ = orc p
              (ValSpace.raise n (cutoff + 1) (ValSpace.openRec cutoff dummy s))
              (ValExpr.raise n (cutoff + 1) (ValExpr.openRec cutoff dummy e)) := by
          rw [open_raise_space n cutoff s, open_raise_expr n cutoff e]
        _ = orc p (ValSpace.openRec cutoff dummy s)
              (ValExpr.openRec cutoff dummy e) :=
          oracle_raise_bounded orc p n steps (cutoff + 1)
            (ValSpace.openRec cutoff dummy s) (ValExpr.openRec cutoff dummy e)
            hs' he'
        _ = orc p s e :=
          FFSOracle.openRec_respect orc cutoff dummy p s e

/-- Global oracle invariance under depth-aware raising.  The support bound is
computed from the finite syntax, so callers need no scope premise. -/
theorem oracle_raise (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (p : ValFFSProp) (n cutoff : Nat) (s : ValSpace) (e : ValExpr) :
    orc p (ValSpace.raise n cutoff s) (ValExpr.raise n cutoff e) = orc p s e := by
  let steps := max (bmaxSpace s) (bmaxExpr e) + 1
  apply oracle_raise_bounded orc p n steps cutoff s e
  · dsimp only [steps]
    omega
  · dsimp only [steps]
    omega

/-! Propagate the leaf equality through space/type skeletons. -/
theorem skel_raise (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (n cutoff : Nat) : ∀ s : ValSpace,
    ValSpace.skel orc (ValSpace.raise n cutoff s) = ValSpace.skel orc s
  | .empty => rfl
  | .real => rfl
  | .dsum s0 s1 => by
      simp [ValSpace.raise, ValSpace.skel, skel_raise orc n cutoff s0,
        skel_raise orc n cutoff s1]
  | .tprod s0 s1 => by
      simp [ValSpace.raise, ValSpace.skel, skel_raise orc n cutoff s0,
        skel_raise orc n cutoff s1]
  | .ffs p s e => by
      simp only [ValSpace.raise, ValSpace.skel, ValSpace.dof, ValSpace.shpOf_ffs,
        ValSpace.Skel.leaf.injEq]
      simpa using oracle_raise orc p n cutoff s e

theorem SDEq_raise (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (n cutoff : Nat) (s : ValSpace) :
    ValSpace.SDEq orc (ValSpace.raise n cutoff s) s :=
  skel_raise orc n cutoff s

end GLang.ValRaise
