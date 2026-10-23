import GLang.Proofs.Value.Binding.ValueLN

namespace GLang.DirectOracleOpenPush

/-! ## A simple scopedness predicate for the custom raising operation -/

mutual
  def ScopedSpace (depth : Nat) : ValSpace -> Prop
    | .empty | .real => True
    | .dsum s0 s1 | .tprod s0 s1 => ScopedSpace depth s0 /\ ScopedSpace depth s1
    | .ffs _ s e => ScopedSpace depth s /\ ScopedExpr depth e

  def ScopedTy (depth : Nat) : ValTy -> Prop
    | .space s => ScopedSpace depth s
    | .piTy t0 t1 => ScopedTy depth t0 /\ ScopedTy (depth + 1) t1

  def ScopedExpr (depth : Nat) : ValExpr -> Prop
    | .bvar i => i < depth
    | .var _ t => ScopedTy depth t
    | .vlam t0 t1 e =>
        ScopedTy depth t0 /\ ScopedTy (depth + 1) t1 /\ ScopedExpr (depth + 1) e
    | .zero s | .delta _ s | .idelta s => ScopedSpace depth s
    | .rlit _ => True
    | .scale e0 e1 | .dsumE e0 e1 | .tprodE e0 e1 |
        .vkrn e0 e1 | .vblk e0 e1 | .rrefRep e0 e1 =>
        ScopedExpr depth e0 /\ ScopedExpr depth e1
    | .vadd s e0 e1 =>
        ScopedSpace depth s /\ ScopedExpr depth e0 /\ ScopedExpr depth e1
    | .vsum s es => ScopedSpace depth s /\ forall e, e ∈ es -> ScopedExpr depth e
    | .ttv s e0 e1 =>
        ScopedSpace depth s /\ ScopedExpr depth e0 /\ ScopedExpr depth e1
    | .mtm _ _ s0 s1 e0 e1 =>
        ScopedSpace depth s0 /\ ScopedSpace depth s1 /\
          ScopedExpr depth e0 /\ ScopedExpr depth e1
    | .appV e0 e1 => ScopedExpr depth e0 /\ ScopedExpr depth e1
    | .reshap e t t0 => ScopedExpr depth e /\ ScopedTy depth t /\ ScopedTy depth t0
    | .vtrans e | .pinv e | .inv e | .svds e => ScopedExpr depth e
    | .gsvdS e a b | .gsvdU e a b | .gsvdUI e a b |
        .gsvdV e a b | .gsvdVI e a b | .gpinv e a b =>
        ScopedExpr depth e /\ ScopedExpr depth a /\ ScopedExpr depth b
end

/-! Closing a slot strictly below the raising cutoff commutes with raising.
This lets the cofinite `lc` binder rule be converted back to its raw body. -/

mutual
  theorem raiseSpace_closeRec (n cutoff j : Nat) (x : VName)
      (hj : j < cutoff) : forall s : ValSpace,
      ValSpace.raise n cutoff (ValSpace.closeRec j x s) =
        ValSpace.closeRec j x (ValSpace.raise n cutoff s)
    | .empty => rfl
    | .real => rfl
    | .dsum s0 s1 => by
        simp only [ValSpace.closeRec, ValSpace.raise,
          raiseSpace_closeRec n cutoff j x hj s0,
          raiseSpace_closeRec n cutoff j x hj s1]
    | .tprod s0 s1 => by
        simp only [ValSpace.closeRec, ValSpace.raise,
          raiseSpace_closeRec n cutoff j x hj s0,
          raiseSpace_closeRec n cutoff j x hj s1]
    | .ffs p s e => by
        simp only [ValSpace.closeRec, ValSpace.raise,
          raiseSpace_closeRec n cutoff j x hj s,
          raiseExpr_closeRec n cutoff j x hj e]

  theorem raiseTy_closeRec (n cutoff j : Nat) (x : VName)
      (hj : j < cutoff) : forall t : ValTy,
      ValTy.raise n cutoff (ValTy.closeRec j x t) =
        ValTy.closeRec j x (ValTy.raise n cutoff t)
    | .space s => by
        simp only [ValTy.closeRec, ValTy.raise,
          raiseSpace_closeRec n cutoff j x hj s]
    | .piTy t0 t1 => by
        simp only [ValTy.closeRec, ValTy.raise,
          raiseTy_closeRec n cutoff j x hj t0,
          raiseTy_closeRec n (cutoff + 1) (j + 1) x (by omega) t1]

  theorem raiseExpr_closeRec (n cutoff j : Nat) (x : VName)
      (hj : j < cutoff) : forall e : ValExpr,
      ValExpr.raise n cutoff (ValExpr.closeRec j x e) =
        ValExpr.closeRec j x (ValExpr.raise n cutoff e)
    | .bvar i => by
        by_cases hci : cutoff <= i <;>
          simp [ValExpr.closeRec, ValExpr.raise, hci]
    | .var y t => by
        by_cases hyx : y = x
        · subst y
          simp [ValExpr.closeRec, ValExpr.raise, Nat.not_le_of_lt hj]
        · simp only [ValExpr.closeRec, if_neg hyx, ValExpr.raise,
            raiseTy_closeRec n cutoff j x hj t]
    | .vlam t0 t1 body => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseTy_closeRec n cutoff j x hj t0,
          raiseTy_closeRec n (cutoff + 1) (j + 1) x (by omega) t1,
          raiseExpr_closeRec n (cutoff + 1) (j + 1) x (by omega) body]
    | .zero s => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseSpace_closeRec n cutoff j x hj s]
    | .rlit r => rfl
    | .scale e0 e1 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e0,
          raiseExpr_closeRec n cutoff j x hj e1]
    | .vadd s e0 e1 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseSpace_closeRec n cutoff j x hj s,
          raiseExpr_closeRec n cutoff j x hj e0,
          raiseExpr_closeRec n cutoff j x hj e1]
    | .dsumE e0 e1 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e0,
          raiseExpr_closeRec n cutoff j x hj e1]
    | .tprodE e0 e1 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e0,
          raiseExpr_closeRec n cutoff j x hj e1]
    | .delta i s => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseSpace_closeRec n cutoff j x hj s]
    | .idelta s => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseSpace_closeRec n cutoff j x hj s]
    | .vsum s es => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseSpace_closeRec n cutoff j x hj s,
          raiseExprList_closeRec n cutoff j x hj es]
    | .ttv s e0 e1 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseSpace_closeRec n cutoff j x hj s,
          raiseExpr_closeRec n cutoff j x hj e0,
          raiseExpr_closeRec n cutoff j x hj e1]
    | .mtm i0 i1 s0 s1 e0 e1 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseSpace_closeRec n cutoff j x hj s0,
          raiseSpace_closeRec n cutoff j x hj s1,
          raiseExpr_closeRec n cutoff j x hj e0,
          raiseExpr_closeRec n cutoff j x hj e1]
    | .appV e0 e1 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e0,
          raiseExpr_closeRec n cutoff j x hj e1]
    | .vkrn e0 e1 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e0,
          raiseExpr_closeRec n cutoff j x hj e1]
    | .vblk e0 e1 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e0,
          raiseExpr_closeRec n cutoff j x hj e1]
    | .reshap e t t0 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e,
          raiseTy_closeRec n cutoff j x hj t,
          raiseTy_closeRec n cutoff j x hj t0]
    | .vtrans e => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e]
    | .gsvdS e a b => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e,
          raiseExpr_closeRec n cutoff j x hj a,
          raiseExpr_closeRec n cutoff j x hj b]
    | .gsvdU e a b => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e,
          raiseExpr_closeRec n cutoff j x hj a,
          raiseExpr_closeRec n cutoff j x hj b]
    | .gsvdUI e a b => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e,
          raiseExpr_closeRec n cutoff j x hj a,
          raiseExpr_closeRec n cutoff j x hj b]
    | .gsvdV e a b => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e,
          raiseExpr_closeRec n cutoff j x hj a,
          raiseExpr_closeRec n cutoff j x hj b]
    | .gsvdVI e a b => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e,
          raiseExpr_closeRec n cutoff j x hj a,
          raiseExpr_closeRec n cutoff j x hj b]
    | .pinv e => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e]
    | .gpinv e a b => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e,
          raiseExpr_closeRec n cutoff j x hj a,
          raiseExpr_closeRec n cutoff j x hj b]
    | .rrefRep e0 e1 => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e0,
          raiseExpr_closeRec n cutoff j x hj e1]
    | .inv e => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e]
    | .svds e => by
        simp only [ValExpr.closeRec, ValExpr.raise,
          raiseExpr_closeRec n cutoff j x hj e]

  theorem raiseExprList_closeRec (n cutoff j : Nat) (x : VName)
      (hj : j < cutoff) : forall es : List ValExpr,
      ValExpr.raiseList n cutoff (ValExpr.closeRecList j x es) =
        ValExpr.closeRecList j x (ValExpr.raiseList n cutoff es)
    | [] => rfl
    | e :: es => by
        simp only [ValExpr.closeRecList, ValExpr.raiseList,
          raiseExpr_closeRec n cutoff j x hj e,
          raiseExprList_closeRec n cutoff j x hj es]
end

theorem raiseExprList_eq_map (n cutoff : Nat) (es : List ValExpr) :
    ValExpr.raiseList n cutoff es = es.map (ValExpr.raise n cutoff) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [ValExpr.raiseList, List.map_cons, ih]

/-! Locally closed syntax is stable under every finite raise.  The binder
cases reuse the existing `close_openVar` laws: prove stability of one fresh
opening, commute raise back through `closeRec`, then recover the raw body. -/

mutual
  theorem raiseSpace_lc : forall {s : ValSpace}, ValSpace.lc s ->
      forall n cutoff, ValSpace.raise n cutoff s = s
    | _, .empty => fun _ _ => rfl
    | _, .real => fun _ _ => rfl
    | _, .dsum h0 h1 => fun n cutoff => by
        simp only [ValSpace.raise, raiseSpace_lc h0 n cutoff,
          raiseSpace_lc h1 n cutoff]
    | _, .tprod h0 h1 => fun n cutoff => by
        simp only [ValSpace.raise, raiseSpace_lc h0 n cutoff,
          raiseSpace_lc h1 n cutoff]
    | _, .ffs hs he => fun n cutoff => by
        simp only [ValSpace.raise, raiseSpace_lc hs n cutoff,
          raiseExpr_lc he n cutoff]

  theorem raiseTy_lc : forall {t : ValTy}, ValTy.lc t ->
      forall n cutoff, ValTy.raise n cutoff t = t
    | _, .space hs => fun n cutoff => by
        simp only [ValTy.raise, raiseSpace_lc hs n cutoff]
    | .piTy t0 t1, .piTy L ht0 hbody => fun n cutoff => by
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ ValTy.fv t1)
        simp only [Finset.mem_union, not_or] at hx
        have hopen := raiseTy_lc (hbody x hx.1) n (cutoff + 1)
        simp only [ValTy.openVar] at hopen
        have hclose := ValTy.close_openVar x t0 t1 hx.2 0
        have hcod : ValTy.raise n (cutoff + 1) t1 = t1 := by
          calc
            ValTy.raise n (cutoff + 1) t1 =
                ValTy.raise n (cutoff + 1)
                  (ValTy.closeRec 0 x
                    (ValTy.openRec 0 (.var x t0) t1)) := by rw [hclose]
            _ = ValTy.closeRec 0 x
                  (ValTy.raise n (cutoff + 1)
                    (ValTy.openRec 0 (.var x t0) t1)) :=
              raiseTy_closeRec n (cutoff + 1) 0 x (by omega)
                (ValTy.openRec 0 (.var x t0) t1)
            _ = ValTy.closeRec 0 x
                  (ValTy.openRec 0 (.var x t0) t1) := by rw [hopen]
            _ = t1 := hclose
        simp only [ValTy.raise, raiseTy_lc ht0 n cutoff, hcod]

  theorem raiseExpr_lc : forall {e : ValExpr}, ValExpr.lc e ->
      forall n cutoff, ValExpr.raise n cutoff e = e
    | _, .var ht => fun n cutoff => by
        simp only [ValExpr.raise, raiseTy_lc ht n cutoff]
    | .vlam t0 t1 body, .vlam L ht0 htype hbody => fun n cutoff => by
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
          (L ∪ (ValTy.fv t1 ∪ ValExpr.fv body))
        simp only [Finset.mem_union, not_or] at hx
        have hopenT := raiseTy_lc (htype x hx.1) n (cutoff + 1)
        have hopenE := raiseExpr_lc (hbody x hx.1) n (cutoff + 1)
        simp only [ValTy.openVar] at hopenT
        simp only [ValExpr.openVar] at hopenE
        have hcloseT := ValTy.close_openVar x t0 t1 hx.2.1 0
        have hcloseE := ValExpr.close_openVar x t0 body hx.2.2 0
        have hcod : ValTy.raise n (cutoff + 1) t1 = t1 := by
          calc
            ValTy.raise n (cutoff + 1) t1 =
                ValTy.raise n (cutoff + 1)
                  (ValTy.closeRec 0 x
                    (ValTy.openRec 0 (.var x t0) t1)) := by rw [hcloseT]
            _ = ValTy.closeRec 0 x
                  (ValTy.raise n (cutoff + 1)
                    (ValTy.openRec 0 (.var x t0) t1)) :=
              raiseTy_closeRec n (cutoff + 1) 0 x (by omega)
                (ValTy.openRec 0 (.var x t0) t1)
            _ = ValTy.closeRec 0 x
                  (ValTy.openRec 0 (.var x t0) t1) := by rw [hopenT]
            _ = t1 := hcloseT
        have hraw : ValExpr.raise n (cutoff + 1) body = body := by
          calc
            ValExpr.raise n (cutoff + 1) body =
                ValExpr.raise n (cutoff + 1)
                  (ValExpr.closeRec 0 x
                    (ValExpr.openRec 0 (.var x t0) body)) := by rw [hcloseE]
            _ = ValExpr.closeRec 0 x
                  (ValExpr.raise n (cutoff + 1)
                    (ValExpr.openRec 0 (.var x t0) body)) :=
              raiseExpr_closeRec n (cutoff + 1) 0 x (by omega)
                (ValExpr.openRec 0 (.var x t0) body)
            _ = ValExpr.closeRec 0 x
                  (ValExpr.openRec 0 (.var x t0) body) := by rw [hopenE]
            _ = body := hcloseE
        simp only [ValExpr.raise, raiseTy_lc ht0 n cutoff, hcod, hraw]
    | _, .zero hs => fun n cutoff => by
        simp only [ValExpr.raise, raiseSpace_lc hs n cutoff]
    | _, .rlit => fun _ _ => rfl
    | _, .scale h0 h1 => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc h0 n cutoff,
          raiseExpr_lc h1 n cutoff]
    | _, .vadd hs h0 h1 => fun n cutoff => by
        simp only [ValExpr.raise, raiseSpace_lc hs n cutoff,
          raiseExpr_lc h0 n cutoff, raiseExpr_lc h1 n cutoff]
    | _, .dsumE h0 h1 => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc h0 n cutoff,
          raiseExpr_lc h1 n cutoff]
    | _, .tprodE h0 h1 => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc h0 n cutoff,
          raiseExpr_lc h1 n cutoff]
    | _, .delta hs => fun n cutoff => by
        simp only [ValExpr.raise, raiseSpace_lc hs n cutoff]
    | _, .idelta hs => fun n cutoff => by
        simp only [ValExpr.raise, raiseSpace_lc hs n cutoff]
    | _, .vsum hs hes => fun n cutoff => by
        simp only [ValExpr.raise, raiseSpace_lc hs n cutoff,
          raiseExprList_eq_map]
        rw [List.map_congr_left
          (g := id) (fun e he => raiseExpr_lc (hes e he) n cutoff),
          List.map_id]
    | _, .ttv hs h0 h1 => fun n cutoff => by
        simp only [ValExpr.raise, raiseSpace_lc hs n cutoff,
          raiseExpr_lc h0 n cutoff, raiseExpr_lc h1 n cutoff]
    | _, .mtm hs0 hs1 h0 h1 => fun n cutoff => by
        simp only [ValExpr.raise, raiseSpace_lc hs0 n cutoff,
          raiseSpace_lc hs1 n cutoff, raiseExpr_lc h0 n cutoff,
          raiseExpr_lc h1 n cutoff]
    | _, .appV h0 h1 => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc h0 n cutoff,
          raiseExpr_lc h1 n cutoff]
    | _, .vkrn h0 h1 => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc h0 n cutoff,
          raiseExpr_lc h1 n cutoff]
    | _, .vblk h0 h1 => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc h0 n cutoff,
          raiseExpr_lc h1 n cutoff]
    | _, .reshap he ht ht0 => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff,
          raiseTy_lc ht n cutoff, raiseTy_lc ht0 n cutoff]
    | _, .vtrans he => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff]
    | _, .gsvdS he ha hb => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff,
          raiseExpr_lc ha n cutoff, raiseExpr_lc hb n cutoff]
    | _, .gsvdU he ha hb => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff,
          raiseExpr_lc ha n cutoff, raiseExpr_lc hb n cutoff]
    | _, .gsvdUI he ha hb => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff,
          raiseExpr_lc ha n cutoff, raiseExpr_lc hb n cutoff]
    | _, .gsvdV he ha hb => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff,
          raiseExpr_lc ha n cutoff, raiseExpr_lc hb n cutoff]
    | _, .gsvdVI he ha hb => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff,
          raiseExpr_lc ha n cutoff, raiseExpr_lc hb n cutoff]
    | _, .pinv he => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff]
    | _, .gpinv he ha hb => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff,
          raiseExpr_lc ha n cutoff, raiseExpr_lc hb n cutoff]
    | _, .rrefRep h0 h1 => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc h0 n cutoff,
          raiseExpr_lc h1 n cutoff]
    | _, .inv he => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff]
    | _, .svds he => fun n cutoff => by
        simp only [ValExpr.raise, raiseExpr_lc he n cutoff]
end

abbrev uOf (y : VName) (sigmaV : ValTy) : ValExpr := .var y sigmaV

def RaiseStableTy (t : ValTy) : Prop := forall n, ValTy.raise n 0 t = t

def RaiseStableExpr (e : ValExpr) : Prop :=
  forall n cutoff, ValExpr.raise n cutoff e = e

theorem raiseStableTy_of_lc {t : ValTy} (ht : ValTy.lc t) :
    RaiseStableTy t := by
  intro n
  exact raiseTy_lc ht n 0

theorem raiseStableExpr_of_lc {e : ValExpr} (he : ValExpr.lc e) :
    RaiseStableExpr e := by
  intro n cutoff
  exact raiseExpr_lc he n cutoff

theorem raiseStable_uOf_of_lc {y : VName} {sigmaV : ValTy}
    (hsigma : ValTy.lc sigmaV) : RaiseStableExpr (uOf y sigmaV) := by
  exact raiseStableExpr_of_lc (.var hsigma)

/-! ## Raising commutes with opening

The inserted expression is assumed stable under raising.  This is the usual
locally-closed use of locally-nameless opening: an inserted value does not
acquire de Bruijn dependencies when it crosses a binder.  The inequality
`cutoff <= k` says that the new slots are inserted outside the slot being
opened, so the opened index moves from `k` to `k+n`.
-/

mutual
  theorem raiseSpace_openRec (n cutoff k : Nat) (u : ValExpr)
      (hu : RaiseStableExpr u) (hcut : cutoff <= k) :
      forall s : ValSpace,
        ValSpace.raise n cutoff (ValSpace.openRec k u s) =
          ValSpace.openRec (k + n) u (ValSpace.raise n cutoff s)
    | .empty => rfl
    | .real => rfl
    | .dsum s0 s1 => by
        simp only [ValSpace.openRec, ValSpace.raise,
          raiseSpace_openRec n cutoff k u hu hcut s0,
          raiseSpace_openRec n cutoff k u hu hcut s1]
    | .tprod s0 s1 => by
        simp only [ValSpace.openRec, ValSpace.raise,
          raiseSpace_openRec n cutoff k u hu hcut s0,
          raiseSpace_openRec n cutoff k u hu hcut s1]
    | .ffs p s e => by
        simp only [ValSpace.openRec, ValSpace.raise,
          raiseSpace_openRec n cutoff k u hu hcut s,
          raiseExpr_openRec n cutoff k u hu hcut e]

  theorem raiseTy_openRec (n cutoff k : Nat) (u : ValExpr)
      (hu : RaiseStableExpr u) (hcut : cutoff <= k) :
      forall t : ValTy,
        ValTy.raise n cutoff (ValTy.openRec k u t) =
          ValTy.openRec (k + n) u (ValTy.raise n cutoff t)
    | .space s => by
        simp only [ValTy.openRec, ValTy.raise,
          raiseSpace_openRec n cutoff k u hu hcut s]
    | .piTy t0 t1 => by
        simp only [ValTy.openRec, ValTy.raise,
          raiseTy_openRec n cutoff k u hu hcut t0,
          raiseTy_openRec n (cutoff + 1) (k + 1) u hu
            (Nat.add_le_add_right hcut 1) t1]
        congr 2
        omega

  theorem raiseExpr_openRec (n cutoff k : Nat) (u : ValExpr)
      (hu : RaiseStableExpr u) (hcut : cutoff <= k) :
      forall e : ValExpr,
        ValExpr.raise n cutoff (ValExpr.openRec k u e) =
          ValExpr.openRec (k + n) u (ValExpr.raise n cutoff e)
    | .bvar i => by
        by_cases hik : i = k
        · subst i
          simpa [ValExpr.openRec, ValExpr.raise, hcut, hu n cutoff,
            Nat.add_comm]
        · by_cases hci : cutoff <= i
          · have hne : i + n ≠ k + n := by omega
            simp only [ValExpr.openRec, if_neg hik, ValExpr.raise, if_pos hci,
              if_neg hne]
          · have hikn : i ≠ k + n := by omega
            simp only [ValExpr.openRec, if_neg hik, ValExpr.raise, if_neg hci,
              if_neg hikn]
    | .var x t => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseTy_openRec n cutoff k u hu hcut t]
    | .vlam t0 t1 body => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseTy_openRec n cutoff k u hu hcut t0,
          raiseTy_openRec n (cutoff + 1) (k + 1) u hu
            (Nat.add_le_add_right hcut 1) t1,
          raiseExpr_openRec n (cutoff + 1) (k + 1) u hu
            (Nat.add_le_add_right hcut 1) body]
        congr 2 <;> omega
    | .zero s => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseSpace_openRec n cutoff k u hu hcut s]
    | .rlit r => rfl
    | .scale e0 e1 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e0,
          raiseExpr_openRec n cutoff k u hu hcut e1]
    | .vadd s e0 e1 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseSpace_openRec n cutoff k u hu hcut s,
          raiseExpr_openRec n cutoff k u hu hcut e0,
          raiseExpr_openRec n cutoff k u hu hcut e1]
    | .dsumE e0 e1 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e0,
          raiseExpr_openRec n cutoff k u hu hcut e1]
    | .tprodE e0 e1 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e0,
          raiseExpr_openRec n cutoff k u hu hcut e1]
    | .delta i s => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseSpace_openRec n cutoff k u hu hcut s]
    | .idelta s => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseSpace_openRec n cutoff k u hu hcut s]
    | .vsum s es => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseSpace_openRec n cutoff k u hu hcut s,
          raiseExprList_openRec n cutoff k u hu hcut es]
    | .ttv s e0 e1 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseSpace_openRec n cutoff k u hu hcut s,
          raiseExpr_openRec n cutoff k u hu hcut e0,
          raiseExpr_openRec n cutoff k u hu hcut e1]
    | .mtm i j s0 s1 e0 e1 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseSpace_openRec n cutoff k u hu hcut s0,
          raiseSpace_openRec n cutoff k u hu hcut s1,
          raiseExpr_openRec n cutoff k u hu hcut e0,
          raiseExpr_openRec n cutoff k u hu hcut e1]
    | .appV e0 e1 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e0,
          raiseExpr_openRec n cutoff k u hu hcut e1]
    | .vkrn e0 e1 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e0,
          raiseExpr_openRec n cutoff k u hu hcut e1]
    | .vblk e0 e1 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e0,
          raiseExpr_openRec n cutoff k u hu hcut e1]
    | .reshap e t t0 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e,
          raiseTy_openRec n cutoff k u hu hcut t,
          raiseTy_openRec n cutoff k u hu hcut t0]
    | .vtrans e => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e]
    | .gsvdS e a b => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e,
          raiseExpr_openRec n cutoff k u hu hcut a,
          raiseExpr_openRec n cutoff k u hu hcut b]
    | .gsvdU e a b => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e,
          raiseExpr_openRec n cutoff k u hu hcut a,
          raiseExpr_openRec n cutoff k u hu hcut b]
    | .gsvdUI e a b => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e,
          raiseExpr_openRec n cutoff k u hu hcut a,
          raiseExpr_openRec n cutoff k u hu hcut b]
    | .gsvdV e a b => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e,
          raiseExpr_openRec n cutoff k u hu hcut a,
          raiseExpr_openRec n cutoff k u hu hcut b]
    | .gsvdVI e a b => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e,
          raiseExpr_openRec n cutoff k u hu hcut a,
          raiseExpr_openRec n cutoff k u hu hcut b]
    | .pinv e => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e]
    | .gpinv e a b => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e,
          raiseExpr_openRec n cutoff k u hu hcut a,
          raiseExpr_openRec n cutoff k u hu hcut b]
    | .rrefRep e0 e1 => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e0,
          raiseExpr_openRec n cutoff k u hu hcut e1]
    | .inv e => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e]
    | .svds e => by
        simp only [ValExpr.openRec, ValExpr.raise,
          raiseExpr_openRec n cutoff k u hu hcut e]

  theorem raiseExprList_openRec (n cutoff k : Nat) (u : ValExpr)
      (hu : RaiseStableExpr u) (hcut : cutoff <= k) :
      forall es : List ValExpr,
        ValExpr.raiseList n cutoff (ValExpr.openRecList k u es) =
          ValExpr.openRecList (k + n) u (ValExpr.raiseList n cutoff es)
    | [] => rfl
    | e :: es => by
        simp only [ValExpr.openRecList, ValExpr.raiseList,
          raiseExpr_openRec n cutoff k u hu hcut e,
          raiseExprList_openRec n cutoff k u hu hcut es]
end

end GLang.DirectOracleOpenPush
