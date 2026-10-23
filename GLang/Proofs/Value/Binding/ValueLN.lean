/- GLang.ValueLN — locally-nameless operations for the value IR. -/
import GLang.Value.Binding
import Mathlib.Data.Fintype.EquivFin  -- `Infinite.exists_notMem_finset`, `String.infinite`

namespace GLang

/-! ## `openRec` — instantiate a bound index. -/

mutual
  def ValSpace.openRec (k : Nat) (u : ValExpr) : ValSpace → ValSpace
    | .empty       => .empty
    | .real        => .real
    | .dsum s₀ s₁  => .dsum (ValSpace.openRec k u s₀) (ValSpace.openRec k u s₁)
    | .tprod s₀ s₁ => .tprod (ValSpace.openRec k u s₀) (ValSpace.openRec k u s₁)
    | .ffs p s e   => .ffs p (ValSpace.openRec k u s) (ValExpr.openRec k u e)

  def ValTy.openRec (k : Nat) (u : ValExpr) : ValTy → ValTy
    | .space s    => .space (ValSpace.openRec k u s)
    -- codomain `τ₁` is UNDER the binder ⇒ index `k+1`.
    | .piTy τ₀ τ₁ => .piTy (ValTy.openRec k u τ₀) (ValTy.openRec (k+1) u τ₁)

  def ValExpr.openRec (k : Nat) (u : ValExpr) : ValExpr → ValExpr
    | .bvar i              => if i = k then u else .bvar i
    | .var x τ             => .var x (ValTy.openRec k u τ)
    -- `vlam` binds in BOTH the codomain `τ₁` and the body `e` ⇒ index `k+1`.
    | .vlam τ₀ τ₁ e        =>
        .vlam (ValTy.openRec k u τ₀) (ValTy.openRec (k+1) u τ₁) (ValExpr.openRec (k+1) u e)
    | .zero s              => .zero (ValSpace.openRec k u s)
    | .rlit r              => .rlit r
    | .scale e₀ e₁         => .scale (ValExpr.openRec k u e₀) (ValExpr.openRec k u e₁)
    | .vadd s e₀ e₁        =>
        .vadd (ValSpace.openRec k u s) (ValExpr.openRec k u e₀) (ValExpr.openRec k u e₁)
    | .dsumE e₀ e₁         => .dsumE (ValExpr.openRec k u e₀) (ValExpr.openRec k u e₁)
    | .tprodE e₀ e₁        => .tprodE (ValExpr.openRec k u e₀) (ValExpr.openRec k u e₁)
    | .delta n s           => .delta n (ValSpace.openRec k u s)
    | .idelta s            => .idelta (ValSpace.openRec k u s)
    | .vsum s es           => .vsum (ValSpace.openRec k u s) (ValExpr.openRecList k u es)
    | .ttv s e₀ e₁         =>
        .ttv (ValSpace.openRec k u s) (ValExpr.openRec k u e₀) (ValExpr.openRec k u e₁)
    | .mtm n₀ n₁ s₀ s₁ e₀ e₁ =>
        .mtm n₀ n₁ (ValSpace.openRec k u s₀) (ValSpace.openRec k u s₁)
          (ValExpr.openRec k u e₀) (ValExpr.openRec k u e₁)
    | .appV e₀ e₁          => .appV (ValExpr.openRec k u e₀) (ValExpr.openRec k u e₁)
    | .vkrn e₀ e₁          => .vkrn (ValExpr.openRec k u e₀) (ValExpr.openRec k u e₁)
    | .vblk e₀ e₁          => .vblk (ValExpr.openRec k u e₀) (ValExpr.openRec k u e₁)
    | .reshap e τ τ₀       => .reshap (ValExpr.openRec k u e)
        (ValTy.openRec k u τ) (ValTy.openRec k u τ₀)
    | .vtrans e            => .vtrans (ValExpr.openRec k u e)
    | .gsvdS e a b         => .gsvdS (ValExpr.openRec k u e) (ValExpr.openRec k u a) (ValExpr.openRec k u b)
    | .gsvdU e a b         => .gsvdU (ValExpr.openRec k u e) (ValExpr.openRec k u a) (ValExpr.openRec k u b)
    | .gsvdUI e a b        => .gsvdUI (ValExpr.openRec k u e) (ValExpr.openRec k u a) (ValExpr.openRec k u b)
    | .gsvdV e a b         => .gsvdV (ValExpr.openRec k u e) (ValExpr.openRec k u a) (ValExpr.openRec k u b)
    | .gsvdVI e a b        => .gsvdVI (ValExpr.openRec k u e) (ValExpr.openRec k u a) (ValExpr.openRec k u b)
    | .pinv e              => .pinv (ValExpr.openRec k u e)
    | .gpinv e a b         => .gpinv (ValExpr.openRec k u e) (ValExpr.openRec k u a) (ValExpr.openRec k u b)
    | .rrefRep e₀ e₁       => .rrefRep (ValExpr.openRec k u e₀) (ValExpr.openRec k u e₁)
    | .inv e               => .inv (ValExpr.openRec k u e)
    | .svds e              => .svds (ValExpr.openRec k u e)

  def ValExpr.openRecList (k : Nat) (u : ValExpr) : List ValExpr → List ValExpr
    | []      => []
    | e :: es => ValExpr.openRec k u e :: ValExpr.openRecList k u es
end

@[simp] theorem ValExpr.openRecList_eq_map (k : Nat) (u : ValExpr) (es : List ValExpr) :
    ValExpr.openRecList k u es = es.map (ValExpr.openRec k u) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ValExpr.openRecList, List.map_cons, ih]

/-- `ValTy.kindSize` is invariant under `openRec` (it counts only `piTy` nesting,
    which `openRec` preserves). The termination measure for binder recursions that
    open their codomain. -/
theorem ValTy.kindSize_openRec (k : Nat) (u : ValExpr) :
    ∀ τ : ValTy, ValTy.kindSize (ValTy.openRec k u τ) = ValTy.kindSize τ
  | .space _   => by simp only [ValTy.openRec, ValTy.kindSize_space]
  | .piTy τ₀ τ₁ => by
      simp only [ValTy.openRec, ValTy.kindSize_piTy,
        ValTy.kindSize_openRec k u τ₀, ValTy.kindSize_openRec (k+1) u τ₁]

/-! ## `raise` — weaken dangling de Bruijn indices.

`raise n cutoff` makes room for `n` new binders at `cutoff`: every bound
index at or above the cutoff is increased by `n`.  The cutoff is increased
under `piTy`/`vlam`, because their codomain/body is below one more binder.

This operation is also used when a dependent type is read back from the local
type telescope.  The `k`th entry was formed before the `k + 1` entries at and
inside that position existed, so using it in the current telescope requires
raising its dangling indices by `k + 1`.
-/

mutual
  def ValSpace.raise (n cutoff : Nat) : ValSpace → ValSpace
    | .empty        => .empty
    | .real         => .real
    | .dsum s₀ s₁   => .dsum (ValSpace.raise n cutoff s₀) (ValSpace.raise n cutoff s₁)
    | .tprod s₀ s₁  => .tprod (ValSpace.raise n cutoff s₀) (ValSpace.raise n cutoff s₁)
    | .ffs p s e    => .ffs p (ValSpace.raise n cutoff s) (ValExpr.raise n cutoff e)

  def ValTy.raise (n cutoff : Nat) : ValTy → ValTy
    | .space s     => .space (ValSpace.raise n cutoff s)
    | .piTy τ₀ τ₁   => .piTy (ValTy.raise n cutoff τ₀) (ValTy.raise n (cutoff + 1) τ₁)

  def ValExpr.raise (n cutoff : Nat) : ValExpr → ValExpr
    | .bvar i              => if cutoff ≤ i then .bvar (i + n) else .bvar i
    | .var x τ             => .var x (ValTy.raise n cutoff τ)
    | .vlam τ₀ τ₁ e        =>
        .vlam (ValTy.raise n cutoff τ₀) (ValTy.raise n (cutoff + 1) τ₁)
          (ValExpr.raise n (cutoff + 1) e)
    | .zero s              => .zero (ValSpace.raise n cutoff s)
    | .rlit r              => .rlit r
    | .scale e₀ e₁         => .scale (ValExpr.raise n cutoff e₀) (ValExpr.raise n cutoff e₁)
    | .vadd s e₀ e₁        =>
        .vadd (ValSpace.raise n cutoff s) (ValExpr.raise n cutoff e₀)
          (ValExpr.raise n cutoff e₁)
    | .dsumE e₀ e₁        => .dsumE (ValExpr.raise n cutoff e₀) (ValExpr.raise n cutoff e₁)
    | .tprodE e₀ e₁       => .tprodE (ValExpr.raise n cutoff e₀) (ValExpr.raise n cutoff e₁)
    | .delta i s           => .delta i (ValSpace.raise n cutoff s)
    | .idelta s            => .idelta (ValSpace.raise n cutoff s)
    | .vsum s es           => .vsum (ValSpace.raise n cutoff s) (ValExpr.raiseList n cutoff es)
    | .ttv s e₀ e₁         =>
        .ttv (ValSpace.raise n cutoff s) (ValExpr.raise n cutoff e₀)
          (ValExpr.raise n cutoff e₁)
    | .mtm i j s₀ s₁ e₀ e₁ =>
        .mtm i j (ValSpace.raise n cutoff s₀) (ValSpace.raise n cutoff s₁)
          (ValExpr.raise n cutoff e₀) (ValExpr.raise n cutoff e₁)
    | .appV e₀ e₁          => .appV (ValExpr.raise n cutoff e₀) (ValExpr.raise n cutoff e₁)
    | .vkrn e₀ e₁          => .vkrn (ValExpr.raise n cutoff e₀) (ValExpr.raise n cutoff e₁)
    | .vblk e₀ e₁          => .vblk (ValExpr.raise n cutoff e₀) (ValExpr.raise n cutoff e₁)
    | .reshap e τ τ₀       =>
        .reshap (ValExpr.raise n cutoff e) (ValTy.raise n cutoff τ)
          (ValTy.raise n cutoff τ₀)
    | .vtrans e            => .vtrans (ValExpr.raise n cutoff e)
    | .gsvdS e a b         =>
        .gsvdS (ValExpr.raise n cutoff e) (ValExpr.raise n cutoff a)
          (ValExpr.raise n cutoff b)
    | .gsvdU e a b         =>
        .gsvdU (ValExpr.raise n cutoff e) (ValExpr.raise n cutoff a)
          (ValExpr.raise n cutoff b)
    | .gsvdUI e a b        =>
        .gsvdUI (ValExpr.raise n cutoff e) (ValExpr.raise n cutoff a)
          (ValExpr.raise n cutoff b)
    | .gsvdV e a b         =>
        .gsvdV (ValExpr.raise n cutoff e) (ValExpr.raise n cutoff a)
          (ValExpr.raise n cutoff b)
    | .gsvdVI e a b        =>
        .gsvdVI (ValExpr.raise n cutoff e) (ValExpr.raise n cutoff a)
          (ValExpr.raise n cutoff b)
    | .pinv e              => .pinv (ValExpr.raise n cutoff e)
    | .gpinv e a b         =>
        .gpinv (ValExpr.raise n cutoff e) (ValExpr.raise n cutoff a)
          (ValExpr.raise n cutoff b)
    | .rrefRep e₀ e₁       => .rrefRep (ValExpr.raise n cutoff e₀) (ValExpr.raise n cutoff e₁)
    | .inv e               => .inv (ValExpr.raise n cutoff e)
    | .svds e              => .svds (ValExpr.raise n cutoff e)

  def ValExpr.raiseList (n cutoff : Nat) : List ValExpr → List ValExpr
    | []      => []
    | e :: es => ValExpr.raise n cutoff e :: ValExpr.raiseList n cutoff es
end

@[simp] theorem ValExpr.raiseList_eq_map (n cutoff : Nat) (es : List ValExpr) :
    ValExpr.raiseList n cutoff es = es.map (ValExpr.raise n cutoff) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ValExpr.raiseList, ih]

/-! Raising changes only bound indices, so it preserves free names exactly. -/

mutual
  @[simp] theorem ValSpace.fv_raise (n cutoff : Nat) :
      ∀ s : ValSpace, ValSpace.fv (ValSpace.raise n cutoff s) = ValSpace.fv s
    | .empty => rfl
    | .real => rfl
    | .dsum s₀ s₁ => by
        simp [ValSpace.raise, ValSpace.fv, ValSpace.fv_raise]
    | .tprod s₀ s₁ => by
        simp [ValSpace.raise, ValSpace.fv, ValSpace.fv_raise]
    | .ffs p s e => by
        simp [ValSpace.raise, ValSpace.fv, ValSpace.fv_raise, ValExpr.fv_raise]

  @[simp] theorem ValTy.fv_raise (n cutoff : Nat) :
      ∀ τ : ValTy, ValTy.fv (ValTy.raise n cutoff τ) = ValTy.fv τ
    | .space s => by
        simp [ValTy.raise, ValTy.fv, ValSpace.fv_raise]
    | .piTy τ₀ τ₁ => by
        simp [ValTy.raise, ValTy.fv, ValTy.fv_raise]

  @[simp] theorem ValExpr.fv_raise (n cutoff : Nat) :
      ∀ e : ValExpr, ValExpr.fv (ValExpr.raise n cutoff e) = ValExpr.fv e
    | .bvar i => by
        by_cases h : cutoff ≤ i <;> simp [ValExpr.raise, ValExpr.fv, h]
    | .var x τ => by simp [ValExpr.raise, ValExpr.fv, ValTy.fv_raise]
    | .vlam τ₀ τ₁ e => by
        simp [ValExpr.raise, ValExpr.fv, ValTy.fv_raise, ValExpr.fv_raise]
    | .zero s => by simp [ValExpr.raise, ValExpr.fv, ValSpace.fv_raise]
    | .rlit r => rfl
    | .scale e₀ e₁ => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .vadd s e₀ e₁ => by
        simp [ValExpr.raise, ValExpr.fv, ValSpace.fv_raise, ValExpr.fv_raise]
    | .dsumE e₀ e₁ => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .tprodE e₀ e₁ => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .delta i s => by simp [ValExpr.raise, ValExpr.fv, ValSpace.fv_raise]
    | .idelta s => by simp [ValExpr.raise, ValExpr.fv, ValSpace.fv_raise]
    | .vsum s es => by
        simp only [ValExpr.raise, ValExpr.fv]
        rw [ValSpace.fv_raise, ValExpr.fv_raiseList]
    | .ttv s e₀ e₁ => by
        simp [ValExpr.raise, ValExpr.fv, ValSpace.fv_raise, ValExpr.fv_raise]
    | .mtm i j s₀ s₁ e₀ e₁ => by
        simp [ValExpr.raise, ValExpr.fv, ValSpace.fv_raise, ValExpr.fv_raise]
    | .appV e₀ e₁ => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .vkrn e₀ e₁ => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .vblk e₀ e₁ => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .reshap e τ τ₀ => by
        simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise, ValTy.fv_raise]
    | .vtrans e => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .gsvdS e a b => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .gsvdU e a b => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .gsvdUI e a b => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .gsvdV e a b => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .gsvdVI e a b => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .pinv e => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .gpinv e a b => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .rrefRep e₀ e₁ => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .inv e => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]
    | .svds e => by simp [ValExpr.raise, ValExpr.fv, ValExpr.fv_raise]

  @[simp] theorem ValExpr.fv_raiseList (n cutoff : Nat) :
      ∀ es : List ValExpr,
        ValExpr.fvList (ValExpr.raiseList n cutoff es) = ValExpr.fvList es
    | [] => rfl
    | e :: es => by
        simp only [ValExpr.raiseList, ValExpr.fvList]
        rw [ValExpr.fv_raise, ValExpr.fv_raiseList]
end

/-! ## Substitution under an enclosing value binder.

Unlike locally closed opening, this operation can insert an argument with
bound occurrences. It raises the argument under nested binders and removes
the substituted binder from the surrounding telescope. Application inference
uses it both outside and inside lambdas.
-/

mutual
  def ValSpace.substBound (k : Nat) (u : ValExpr) : ValSpace → ValSpace
    | .empty       => .empty
    | .real        => .real
    | .dsum s₀ s₁  => .dsum (ValSpace.substBound k u s₀) (ValSpace.substBound k u s₁)
    | .tprod s₀ s₁ => .tprod (ValSpace.substBound k u s₀) (ValSpace.substBound k u s₁)
    | .ffs p s e   => .ffs p (ValSpace.substBound k u s) (ValExpr.substBound k u e)

  def ValTy.substBound (k : Nat) (u : ValExpr) : ValTy → ValTy
    | .space s    => .space (ValSpace.substBound k u s)
    -- codomain `τ₁` is UNDER the binder ⇒ index `k+1`.
    | .piTy τ₀ τ₁ => .piTy (ValTy.substBound k u τ₀) (ValTy.substBound (k+1) u τ₁)

  def ValExpr.substBound (k : Nat) (u : ValExpr) : ValExpr → ValExpr
    | .bvar i              => if i = k then ValExpr.raise k 0 u
        else if k < i then .bvar (i - 1) else .bvar i
    | .var x τ             => .var x (ValTy.substBound k u τ)
    -- `vlam` binds in BOTH the codomain `τ₁` and the body `e` ⇒ index `k+1`.
    | .vlam τ₀ τ₁ e        =>
        .vlam (ValTy.substBound k u τ₀) (ValTy.substBound (k+1) u τ₁) (ValExpr.substBound (k+1) u e)
    | .zero s              => .zero (ValSpace.substBound k u s)
    | .rlit r              => .rlit r
    | .scale e₀ e₁         => .scale (ValExpr.substBound k u e₀) (ValExpr.substBound k u e₁)
    | .vadd s e₀ e₁        =>
        .vadd (ValSpace.substBound k u s) (ValExpr.substBound k u e₀) (ValExpr.substBound k u e₁)
    | .dsumE e₀ e₁         => .dsumE (ValExpr.substBound k u e₀) (ValExpr.substBound k u e₁)
    | .tprodE e₀ e₁        => .tprodE (ValExpr.substBound k u e₀) (ValExpr.substBound k u e₁)
    | .delta n s           => .delta n (ValSpace.substBound k u s)
    | .idelta s            => .idelta (ValSpace.substBound k u s)
    | .vsum s es           => .vsum (ValSpace.substBound k u s) (ValExpr.substBoundList k u es)
    | .ttv s e₀ e₁         =>
        .ttv (ValSpace.substBound k u s) (ValExpr.substBound k u e₀) (ValExpr.substBound k u e₁)
    | .mtm n₀ n₁ s₀ s₁ e₀ e₁ =>
        .mtm n₀ n₁ (ValSpace.substBound k u s₀) (ValSpace.substBound k u s₁)
          (ValExpr.substBound k u e₀) (ValExpr.substBound k u e₁)
    | .appV e₀ e₁          => .appV (ValExpr.substBound k u e₀) (ValExpr.substBound k u e₁)
    | .vkrn e₀ e₁          => .vkrn (ValExpr.substBound k u e₀) (ValExpr.substBound k u e₁)
    | .vblk e₀ e₁          => .vblk (ValExpr.substBound k u e₀) (ValExpr.substBound k u e₁)
    | .reshap e τ τ₀       => .reshap (ValExpr.substBound k u e)
        (ValTy.substBound k u τ) (ValTy.substBound k u τ₀)
    | .vtrans e            => .vtrans (ValExpr.substBound k u e)
    | .gsvdS e a b         => .gsvdS (ValExpr.substBound k u e) (ValExpr.substBound k u a) (ValExpr.substBound k u b)
    | .gsvdU e a b         => .gsvdU (ValExpr.substBound k u e) (ValExpr.substBound k u a) (ValExpr.substBound k u b)
    | .gsvdUI e a b        => .gsvdUI (ValExpr.substBound k u e) (ValExpr.substBound k u a) (ValExpr.substBound k u b)
    | .gsvdV e a b         => .gsvdV (ValExpr.substBound k u e) (ValExpr.substBound k u a) (ValExpr.substBound k u b)
    | .gsvdVI e a b        => .gsvdVI (ValExpr.substBound k u e) (ValExpr.substBound k u a) (ValExpr.substBound k u b)
    | .pinv e              => .pinv (ValExpr.substBound k u e)
    | .gpinv e a b         => .gpinv (ValExpr.substBound k u e) (ValExpr.substBound k u a) (ValExpr.substBound k u b)
    | .rrefRep e₀ e₁       => .rrefRep (ValExpr.substBound k u e₀) (ValExpr.substBound k u e₁)
    | .inv e               => .inv (ValExpr.substBound k u e)
    | .svds e              => .svds (ValExpr.substBound k u e)

  def ValExpr.substBoundList (k : Nat) (u : ValExpr) : List ValExpr → List ValExpr
    | []      => []
    | e :: es => ValExpr.substBound k u e :: ValExpr.substBoundList k u es
end

/-- Capture-avoiding dependent result substitution for value application. -/
def ValTy.applyCodomain (argument : ValExpr) (codomain : ValTy) : ValTy :=
  ValTy.substBound 0 argument codomain

/-! ### Reading declaration-level types in the current telescope. -/

namespace ValTyCtx

/-- Realize the `k`th declaration-level type at its current use depth.

Contexts are innermost-first.  An entry at index `k` predates exactly `k + 1`
current binders, so its dangling indices must cross all of them before the
entry is used by context-aware inference.
-/
def lookupUse (Gamma : List ValTy) (k : Nat) : ValTy :=
  ValTy.raise (k + 1) 0 (Gamma.getD k default)

@[simp] theorem fv_lookupUse (Gamma : List ValTy) (k : Nat) :
    ValTy.fv (lookupUse Gamma k) = ValTy.fv (Gamma.getD k default) := by
  simp [lookupUse]

end ValTyCtx

/-! ## `closeRec` — abstract a free name to a bound index. -/

mutual
  def ValSpace.closeRec (k : Nat) (x : VName) : ValSpace → ValSpace
    | .empty       => .empty
    | .real        => .real
    | .dsum s₀ s₁  => .dsum (ValSpace.closeRec k x s₀) (ValSpace.closeRec k x s₁)
    | .tprod s₀ s₁ => .tprod (ValSpace.closeRec k x s₀) (ValSpace.closeRec k x s₁)
    | .ffs p s e   => .ffs p (ValSpace.closeRec k x s) (ValExpr.closeRec k x e)

  def ValTy.closeRec (k : Nat) (x : VName) : ValTy → ValTy
    | .space s    => .space (ValSpace.closeRec k x s)
    | .piTy τ₀ τ₁ => .piTy (ValTy.closeRec k x τ₀) (ValTy.closeRec (k+1) x τ₁)

  def ValExpr.closeRec (k : Nat) (x : VName) : ValExpr → ValExpr
    | .var y τ             =>
        if y = x then .bvar k else .var y (ValTy.closeRec k x τ)
    | .bvar i              => .bvar i
    | .vlam τ₀ τ₁ e        =>
        .vlam (ValTy.closeRec k x τ₀) (ValTy.closeRec (k+1) x τ₁) (ValExpr.closeRec (k+1) x e)
    | .zero s              => .zero (ValSpace.closeRec k x s)
    | .rlit r              => .rlit r
    | .scale e₀ e₁         => .scale (ValExpr.closeRec k x e₀) (ValExpr.closeRec k x e₁)
    | .vadd s e₀ e₁        =>
        .vadd (ValSpace.closeRec k x s) (ValExpr.closeRec k x e₀) (ValExpr.closeRec k x e₁)
    | .dsumE e₀ e₁         => .dsumE (ValExpr.closeRec k x e₀) (ValExpr.closeRec k x e₁)
    | .tprodE e₀ e₁        => .tprodE (ValExpr.closeRec k x e₀) (ValExpr.closeRec k x e₁)
    | .delta n s           => .delta n (ValSpace.closeRec k x s)
    | .idelta s            => .idelta (ValSpace.closeRec k x s)
    | .vsum s es           => .vsum (ValSpace.closeRec k x s) (ValExpr.closeRecList k x es)
    | .ttv s e₀ e₁         =>
        .ttv (ValSpace.closeRec k x s) (ValExpr.closeRec k x e₀) (ValExpr.closeRec k x e₁)
    | .mtm n₀ n₁ s₀ s₁ e₀ e₁ =>
        .mtm n₀ n₁ (ValSpace.closeRec k x s₀) (ValSpace.closeRec k x s₁)
          (ValExpr.closeRec k x e₀) (ValExpr.closeRec k x e₁)
    | .appV e₀ e₁          => .appV (ValExpr.closeRec k x e₀) (ValExpr.closeRec k x e₁)
    | .vkrn e₀ e₁          => .vkrn (ValExpr.closeRec k x e₀) (ValExpr.closeRec k x e₁)
    | .vblk e₀ e₁          => .vblk (ValExpr.closeRec k x e₀) (ValExpr.closeRec k x e₁)
    | .reshap e τ τ₀       => .reshap (ValExpr.closeRec k x e)
        (ValTy.closeRec k x τ) (ValTy.closeRec k x τ₀)
    | .vtrans e            => .vtrans (ValExpr.closeRec k x e)
    | .gsvdS e a b         => .gsvdS (ValExpr.closeRec k x e) (ValExpr.closeRec k x a) (ValExpr.closeRec k x b)
    | .gsvdU e a b         => .gsvdU (ValExpr.closeRec k x e) (ValExpr.closeRec k x a) (ValExpr.closeRec k x b)
    | .gsvdUI e a b        => .gsvdUI (ValExpr.closeRec k x e) (ValExpr.closeRec k x a) (ValExpr.closeRec k x b)
    | .gsvdV e a b         => .gsvdV (ValExpr.closeRec k x e) (ValExpr.closeRec k x a) (ValExpr.closeRec k x b)
    | .gsvdVI e a b        => .gsvdVI (ValExpr.closeRec k x e) (ValExpr.closeRec k x a) (ValExpr.closeRec k x b)
    | .pinv e              => .pinv (ValExpr.closeRec k x e)
    | .gpinv e a b         => .gpinv (ValExpr.closeRec k x e) (ValExpr.closeRec k x a) (ValExpr.closeRec k x b)
    | .rrefRep e₀ e₁       => .rrefRep (ValExpr.closeRec k x e₀) (ValExpr.closeRec k x e₁)
    | .inv e               => .inv (ValExpr.closeRec k x e)
    | .svds e              => .svds (ValExpr.closeRec k x e)

  def ValExpr.closeRecList (k : Nat) (x : VName) : List ValExpr → List ValExpr
    | []      => []
    | e :: es => ValExpr.closeRec k x e :: ValExpr.closeRecList k x es
end

@[simp] theorem ValExpr.closeRecList_eq_map (k : Nat) (x : VName) (es : List ValExpr) :
    ValExpr.closeRecList k x es = es.map (ValExpr.closeRec k x) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ValExpr.closeRecList, List.map_cons, ih]

/-! ## `subst` — free-variable substitution `[x ↦ u]`.

Capture-free by construction: binders are nameless, so there is no shadow guard
and no freshness side condition. -/

mutual
  def ValSpace.subst (x : VName) (u : ValExpr) : ValSpace → ValSpace
    | .empty       => .empty
    | .real        => .real
    | .dsum s₀ s₁  => .dsum (ValSpace.subst x u s₀) (ValSpace.subst x u s₁)
    | .tprod s₀ s₁ => .tprod (ValSpace.subst x u s₀) (ValSpace.subst x u s₁)
    | .ffs p s e   => .ffs p (ValSpace.subst x u s) (ValExpr.subst x u e)

  def ValTy.subst (x : VName) (u : ValExpr) : ValTy → ValTy
    | .space s    => .space (ValSpace.subst x u s)
    | .piTy τ₀ τ₁ => .piTy (ValTy.subst x u τ₀) (ValTy.subst x u τ₁)

  def ValExpr.subst (x : VName) (u : ValExpr) : ValExpr → ValExpr
    | .var y τ             => if y = x then u else .var y (ValTy.subst x u τ)
    | .bvar i              => .bvar i
    | .vlam τ₀ τ₁ e        =>
        .vlam (ValTy.subst x u τ₀) (ValTy.subst x u τ₁) (ValExpr.subst x u e)
    | .zero s              => .zero (ValSpace.subst x u s)
    | .rlit r              => .rlit r
    | .scale e₀ e₁         => .scale (ValExpr.subst x u e₀) (ValExpr.subst x u e₁)
    | .vadd s e₀ e₁        =>
        .vadd (ValSpace.subst x u s) (ValExpr.subst x u e₀) (ValExpr.subst x u e₁)
    | .dsumE e₀ e₁         => .dsumE (ValExpr.subst x u e₀) (ValExpr.subst x u e₁)
    | .tprodE e₀ e₁        => .tprodE (ValExpr.subst x u e₀) (ValExpr.subst x u e₁)
    | .delta n s           => .delta n (ValSpace.subst x u s)
    | .idelta s            => .idelta (ValSpace.subst x u s)
    | .vsum s es           => .vsum (ValSpace.subst x u s) (ValExpr.substList x u es)
    | .ttv s e₀ e₁         =>
        .ttv (ValSpace.subst x u s) (ValExpr.subst x u e₀) (ValExpr.subst x u e₁)
    | .mtm n₀ n₁ s₀ s₁ e₀ e₁ =>
        .mtm n₀ n₁ (ValSpace.subst x u s₀) (ValSpace.subst x u s₁)
          (ValExpr.subst x u e₀) (ValExpr.subst x u e₁)
    | .appV e₀ e₁          => .appV (ValExpr.subst x u e₀) (ValExpr.subst x u e₁)
    | .vkrn e₀ e₁          => .vkrn (ValExpr.subst x u e₀) (ValExpr.subst x u e₁)
    | .vblk e₀ e₁          => .vblk (ValExpr.subst x u e₀) (ValExpr.subst x u e₁)
    | .reshap e τ τ₀       => .reshap (ValExpr.subst x u e)
        (ValTy.subst x u τ) (ValTy.subst x u τ₀)
    | .vtrans e            => .vtrans (ValExpr.subst x u e)
    | .gsvdS e a b         => .gsvdS (ValExpr.subst x u e) (ValExpr.subst x u a) (ValExpr.subst x u b)
    | .gsvdU e a b         => .gsvdU (ValExpr.subst x u e) (ValExpr.subst x u a) (ValExpr.subst x u b)
    | .gsvdUI e a b        => .gsvdUI (ValExpr.subst x u e) (ValExpr.subst x u a) (ValExpr.subst x u b)
    | .gsvdV e a b         => .gsvdV (ValExpr.subst x u e) (ValExpr.subst x u a) (ValExpr.subst x u b)
    | .gsvdVI e a b        => .gsvdVI (ValExpr.subst x u e) (ValExpr.subst x u a) (ValExpr.subst x u b)
    | .pinv e              => .pinv (ValExpr.subst x u e)
    | .gpinv e a b         => .gpinv (ValExpr.subst x u e) (ValExpr.subst x u a) (ValExpr.subst x u b)
    | .rrefRep e₀ e₁       => .rrefRep (ValExpr.subst x u e₀) (ValExpr.subst x u e₁)
    | .inv e               => .inv (ValExpr.subst x u e)
    | .svds e              => .svds (ValExpr.subst x u e)

  def ValExpr.substList (x : VName) (u : ValExpr) : List ValExpr → List ValExpr
    | []      => []
    | e :: es => ValExpr.subst x u e :: ValExpr.substList x u es
end

@[simp] theorem ValExpr.substList_eq_map (x : VName) (u : ValExpr) (es : List ValExpr) :
    ValExpr.substList x u es = es.map (ValExpr.subst x u) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ValExpr.substList, List.map_cons, ih]

/-- Free-variable substitution changes the witnesses stored in fundamental
    spaces, but not their oracle-independent dimension upper bound. -/
@[simp] theorem ValSpace.dofUB_subst (x : VName) (u : ValExpr) :
    ∀ s : ValSpace, ValSpace.dofUB (ValSpace.subst x u s) = ValSpace.dofUB s
  | .empty => rfl
  | .real => rfl
  | .dsum s₀ s₁ => by
      simp only [ValSpace.subst, ValSpace.dofUB, ValSpace.dofUB_subst x u s₀,
        ValSpace.dofUB_subst x u s₁]
  | .tprod s₀ s₁ => by
      simp only [ValSpace.subst, ValSpace.dofUB, ValSpace.dofUB_subst x u s₀,
        ValSpace.dofUB_subst x u s₁]
  | .ffs .kernel (.tprod s₀ s₁) e => by
      simp only [ValSpace.subst, ValSpace.dofUB, ValSpace.dofUB_subst x u s₀]
  | .ffs .cokernel (.tprod s₀ s₁) e => by
      simp only [ValSpace.subst, ValSpace.dofUB, ValSpace.dofUB_subst x u s₀]
  | .ffs .image (.tprod s₀ s₁) e => by
      simp only [ValSpace.subst, ValSpace.dofUB, ValSpace.dofUB_subst x u s₁]
  | .ffs .coimage (.tprod s₀ s₁) e => by
      simp only [ValSpace.subst, ValSpace.dofUB, ValSpace.dofUB_subst x u s₁]
  | .ffs p .empty e => by cases p <;> rfl
  | .ffs p .real e => by cases p <;> rfl
  | .ffs p (.dsum s₀ s₁) e => by
      cases p <;>
        simp only [ValSpace.subst, ValSpace.dofUB, ValSpace.dofUB_subst x u s₀,
          ValSpace.dofUB_subst x u s₁]
  | .ffs p (.ffs q s e₀) e => by
      cases p <;> simp only [ValSpace.subst, ValSpace.dofUB] <;>
        exact ValSpace.dofUB_subst x u (.ffs q s e₀)

/-! ## Derived openers. -/

/-- The β-substitution: instantiate the top bound index with `u`. -/
@[reducible] def ValExpr.instantiate (u e : ValExpr) : ValExpr := ValExpr.openRec 0 u e
@[reducible] def ValTy.instantiate (u : ValExpr) (τ : ValTy) : ValTy := ValTy.openRec 0 u τ

/-- Open the top binder with a fresh free variable `x` (annotated `τ`). -/
@[reducible] def ValExpr.openVar (x : VName) (τ : ValTy) (e : ValExpr) : ValExpr :=
  ValExpr.openRec 0 (.var x τ) e
@[reducible] def ValTy.openVar (x : VName) (τ : ValTy) (σ : ValTy) : ValTy :=
  ValTy.openRec 0 (.var x τ) σ

/-! ## `lc` — locally closed (no dangling `bvar`).

Cofinitely quantified at the two binders. REPLACES the named `WellAnn` /
`bound`-freshness discipline: a value is well-formed iff it is locally closed.
There is deliberately NO `bvar` rule — a lone bound index is not locally closed;
indices only appear under their binder and become `var` once opened. -/

mutual
  inductive ValSpace.lc : ValSpace → Prop
    | empty : ValSpace.lc .empty
    | real  : ValSpace.lc .real
    | dsum  {s₀ s₁} : ValSpace.lc s₀ → ValSpace.lc s₁ → ValSpace.lc (.dsum s₀ s₁)
    | tprod {s₀ s₁} : ValSpace.lc s₀ → ValSpace.lc s₁ → ValSpace.lc (.tprod s₀ s₁)
    | ffs   {p s e} : ValSpace.lc s → ValExpr.lc e → ValSpace.lc (.ffs p s e)

  inductive ValTy.lc : ValTy → Prop
    | space {s} : ValSpace.lc s → ValTy.lc (.space s)
    | piTy  {τ₀ τ₁} (L : Finset VName) :
        ValTy.lc τ₀ → (∀ x, x ∉ L → ValTy.lc (ValTy.openVar x τ₀ τ₁)) →
        ValTy.lc (.piTy τ₀ τ₁)

  inductive ValExpr.lc : ValExpr → Prop
    | var   {x τ} : ValTy.lc τ → ValExpr.lc (.var x τ)
    | vlam  {τ₀ τ₁ e} (L : Finset VName) :
        ValTy.lc τ₀ →
        (∀ x, x ∉ L → ValTy.lc (ValTy.openVar x τ₀ τ₁)) →
        (∀ x, x ∉ L → ValExpr.lc (ValExpr.openVar x τ₀ e)) →
        ValExpr.lc (.vlam τ₀ τ₁ e)
    | zero  {s} : ValSpace.lc s → ValExpr.lc (.zero s)
    | rlit  {r} : ValExpr.lc (.rlit r)
    | scale {e₀ e₁} : ValExpr.lc e₀ → ValExpr.lc e₁ → ValExpr.lc (.scale e₀ e₁)
    | vadd  {s e₀ e₁} : ValSpace.lc s → ValExpr.lc e₀ → ValExpr.lc e₁ →
        ValExpr.lc (.vadd s e₀ e₁)
    | dsumE {e₀ e₁} : ValExpr.lc e₀ → ValExpr.lc e₁ → ValExpr.lc (.dsumE e₀ e₁)
    | tprodE {e₀ e₁} : ValExpr.lc e₀ → ValExpr.lc e₁ → ValExpr.lc (.tprodE e₀ e₁)
    | delta {n s} : ValSpace.lc s → ValExpr.lc (.delta n s)
    | idelta {s} : ValSpace.lc s → ValExpr.lc (.idelta s)
    | vsum  {s es} : ValSpace.lc s → (∀ e ∈ es, ValExpr.lc e) → ValExpr.lc (.vsum s es)
    | ttv   {s e₀ e₁} : ValSpace.lc s → ValExpr.lc e₀ → ValExpr.lc e₁ → ValExpr.lc (.ttv s e₀ e₁)
    | mtm   {n₀ n₁ s₀ s₁ e₀ e₁} : ValSpace.lc s₀ → ValSpace.lc s₁ →
        ValExpr.lc e₀ → ValExpr.lc e₁ → ValExpr.lc (.mtm n₀ n₁ s₀ s₁ e₀ e₁)
    | appV  {e₀ e₁} : ValExpr.lc e₀ → ValExpr.lc e₁ → ValExpr.lc (.appV e₀ e₁)
    | vkrn  {e₀ e₁} : ValExpr.lc e₀ → ValExpr.lc e₁ → ValExpr.lc (.vkrn e₀ e₁)
    | vblk  {e₀ e₁} : ValExpr.lc e₀ → ValExpr.lc e₁ → ValExpr.lc (.vblk e₀ e₁)
    | reshap {e τ τ₀} : ValExpr.lc e → ValTy.lc τ → ValTy.lc τ₀ →
        ValExpr.lc (.reshap e τ τ₀)
    | vtrans {e} : ValExpr.lc e → ValExpr.lc (.vtrans e)
    | gsvdS {e a b} : ValExpr.lc e → ValExpr.lc a → ValExpr.lc b → ValExpr.lc (.gsvdS e a b)
    | gsvdU {e a b} : ValExpr.lc e → ValExpr.lc a → ValExpr.lc b → ValExpr.lc (.gsvdU e a b)
    | gsvdUI {e a b} : ValExpr.lc e → ValExpr.lc a → ValExpr.lc b → ValExpr.lc (.gsvdUI e a b)
    | gsvdV {e a b} : ValExpr.lc e → ValExpr.lc a → ValExpr.lc b → ValExpr.lc (.gsvdV e a b)
    | gsvdVI {e a b} : ValExpr.lc e → ValExpr.lc a → ValExpr.lc b → ValExpr.lc (.gsvdVI e a b)
    | pinv  {e} : ValExpr.lc e → ValExpr.lc (.pinv e)
    | gpinv {e a b} : ValExpr.lc e → ValExpr.lc a → ValExpr.lc b → ValExpr.lc (.gpinv e a b)
    | rrefRep {e₀ e₁} : ValExpr.lc e₀ → ValExpr.lc e₁ → ValExpr.lc (.rrefRep e₀ e₁)
    | inv   {e} : ValExpr.lc e → ValExpr.lc (.inv e)
    | svds  {e} : ValExpr.lc e → ValExpr.lc (.svds e)
end

theorem ValExpr.lc.canonicalFSV {which : ValFFSProp} {e a b : ValExpr}
    (he : ValExpr.lc e) (ha : ValExpr.lc a) (hb : ValExpr.lc b) :
    ValExpr.lc (.canonicalFSV which e a b) := by
  cases which with
  | kernel => exact .gsvdUI he ha hb
  | cokernel => exact .gsvdU he ha hb
  | image => exact .gsvdV he ha hb
  | coimage => exact .gsvdVI he ha hb

/-! ## Lemma kit (1): `subst` is identity on a free name not in `fv`.

The LN analogue of the retired `subst_eq_self`. No binder shadow-guards (binders
are nameless), so the binder arms recurse uniformly. -/

mutual
theorem ValSpace.subst_fresh (x : VName) (u : ValExpr) :
    ∀ (s : ValSpace), x ∉ ValSpace.fv s → ValSpace.subst x u s = s
  | .empty, _ => rfl
  | .real, _ => rfl
  | .dsum s₀ s₁, h => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h
      simp only [ValSpace.subst, ValSpace.subst_fresh x u s₀ h.1,
        ValSpace.subst_fresh x u s₁ h.2]
  | .tprod s₀ s₁, h => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h
      simp only [ValSpace.subst, ValSpace.subst_fresh x u s₀ h.1,
        ValSpace.subst_fresh x u s₁ h.2]
  | .ffs p s e, h => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h
      simp only [ValSpace.subst, ValSpace.subst_fresh x u s h.1,
        ValExpr.subst_fresh x u e h.2]

theorem ValTy.subst_fresh (x : VName) (u : ValExpr) :
    ∀ (τ : ValTy), x ∉ ValTy.fv τ → ValTy.subst x u τ = τ
  | .space s, h => by
      simp only [ValTy.fv] at h
      simp only [ValTy.subst, ValSpace.subst_fresh x u s h]
  | .piTy τ₀ τ₁, h => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at h
      simp only [ValTy.subst, ValTy.subst_fresh x u τ₀ h.1, ValTy.subst_fresh x u τ₁ h.2]

theorem ValExpr.subst_fresh (x : VName) (u : ValExpr) :
    ∀ (e : ValExpr), x ∉ ValExpr.fv e → ValExpr.subst x u e = e
  | .var y τ, h => by
      simp only [ValExpr.fv, Finset.mem_insert, not_or] at h
      simp only [ValExpr.subst, if_neg (Ne.symm h.1), ValTy.subst_fresh x u τ h.2]
  | .bvar i, _ => rfl
  | .rlit _, _ => rfl
  | .zero s, h => by
      simp only [ValExpr.fv] at h; simp only [ValExpr.subst, ValSpace.subst_fresh x u s h]
  | .delta n s, h => by
      simp only [ValExpr.fv] at h; simp only [ValExpr.subst, ValSpace.subst_fresh x u s h]
  | .idelta s, h => by
      simp only [ValExpr.fv] at h; simp only [ValExpr.subst, ValSpace.subst_fresh x u s h]
  | .scale e₀ e₁, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e₀ h.1, ValExpr.subst_fresh x u e₁ h.2]
  | .vadd s e₀ e₁, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValSpace.subst_fresh x u s h.1.1,
        ValExpr.subst_fresh x u e₀ h.1.2, ValExpr.subst_fresh x u e₁ h.2]
  | .dsumE e₀ e₁, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e₀ h.1, ValExpr.subst_fresh x u e₁ h.2]
  | .tprodE e₀ e₁, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e₀ h.1, ValExpr.subst_fresh x u e₁ h.2]
  | .vkrn e₀ e₁, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e₀ h.1, ValExpr.subst_fresh x u e₁ h.2]
  | .vblk e₀ e₁, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e₀ h.1, ValExpr.subst_fresh x u e₁ h.2]
  | .rrefRep e₀ e₁, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e₀ h.1, ValExpr.subst_fresh x u e₁ h.2]
  | .vsum s es, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValSpace.subst_fresh x u s h.1,
        ValExpr.substList_fresh x u es h.2]
  | .vlam τ₀ τ₁ e, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValTy.subst_fresh x u τ₀ h.1.1,
        ValTy.subst_fresh x u τ₁ h.1.2, ValExpr.subst_fresh x u e h.2]
  | .ttv s e₀ e₁, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValSpace.subst_fresh x u s h.1.1,
        ValExpr.subst_fresh x u e₀ h.1.2, ValExpr.subst_fresh x u e₁ h.2]
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValSpace.subst_fresh x u s₀ h.1.1.1,
        ValSpace.subst_fresh x u s₁ h.1.1.2, ValExpr.subst_fresh x u e₀ h.1.2,
        ValExpr.subst_fresh x u e₁ h.2]
  | .appV e₀ e₁, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e₀ h.1, ValExpr.subst_fresh x u e₁ h.2]
  | .reshap e τ τ₀, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e h.1.1,
        ValTy.subst_fresh x u τ h.1.2, ValTy.subst_fresh x u τ₀ h.2]
  | .vtrans e, h => by
      simp only [ValExpr.fv] at h; simp only [ValExpr.subst, ValExpr.subst_fresh x u e h]
  | .pinv e, h => by
      simp only [ValExpr.fv] at h; simp only [ValExpr.subst, ValExpr.subst_fresh x u e h]
  | .inv e, h => by
      simp only [ValExpr.fv] at h; simp only [ValExpr.subst, ValExpr.subst_fresh x u e h]
  | .svds e, h => by
      simp only [ValExpr.fv] at h; simp only [ValExpr.subst, ValExpr.subst_fresh x u e h]
  | .gsvdS e a b, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e h.1.1,
        ValExpr.subst_fresh x u a h.1.2, ValExpr.subst_fresh x u b h.2]
  | .gsvdU e a b, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e h.1.1,
        ValExpr.subst_fresh x u a h.1.2, ValExpr.subst_fresh x u b h.2]
  | .gsvdUI e a b, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e h.1.1,
        ValExpr.subst_fresh x u a h.1.2, ValExpr.subst_fresh x u b h.2]
  | .gsvdV e a b, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e h.1.1,
        ValExpr.subst_fresh x u a h.1.2, ValExpr.subst_fresh x u b h.2]
  | .gsvdVI e a b, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e h.1.1,
        ValExpr.subst_fresh x u a h.1.2, ValExpr.subst_fresh x u b h.2]
  | .gpinv e a b, h => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.subst, ValExpr.subst_fresh x u e h.1.1,
        ValExpr.subst_fresh x u a h.1.2, ValExpr.subst_fresh x u b h.2]

theorem ValExpr.substList_fresh (x : VName) (u : ValExpr) :
    ∀ (es : List ValExpr), x ∉ ValExpr.fvList es → ValExpr.substList x u es = es
  | [], _ => rfl
  | e :: es, h => by
      simp only [ValExpr.fvList, Finset.mem_union, not_or] at h
      simp only [ValExpr.substList, ValExpr.subst_fresh x u e h.1,
        ValExpr.substList_fresh x u es h.2]
end

/-! ## Lemma kit (2): `subst_intro` — opening = substituting at a fresh name.

`x ∉ fv e → openRec k u e = subst x u (openRec k (.var x τ) e)`. The bridge that
turns the cofinite "open at a fresh `x`" reasoning into `subst`. No `lc` needed;
pure structural induction (the inserted `.var x τ` lands at index `k`, and `subst`
turns exactly that occurrence into `u`). -/

mutual
theorem ValSpace.subst_intro (x : VName) (u : ValExpr) (τ : ValTy) :
    ∀ (s : ValSpace), x ∉ ValSpace.fv s → ∀ (k : Nat),
      ValSpace.openRec k u s = ValSpace.subst x u (ValSpace.openRec k (.var x τ) s)
  | .empty, _ => fun _ => rfl
  | .real, _ => fun _ => rfl
  | .dsum s₀ s₁, h => fun k => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h
      simp only [ValSpace.openRec, ValSpace.subst,
        ValSpace.subst_intro x u τ s₀ h.1 k, ValSpace.subst_intro x u τ s₁ h.2 k]
  | .tprod s₀ s₁, h => fun k => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h
      simp only [ValSpace.openRec, ValSpace.subst,
        ValSpace.subst_intro x u τ s₀ h.1 k, ValSpace.subst_intro x u τ s₁ h.2 k]
  | .ffs p s e, h => fun k => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h
      simp only [ValSpace.openRec, ValSpace.subst,
        ValSpace.subst_intro x u τ s h.1 k, ValExpr.subst_intro x u τ e h.2 k]

theorem ValTy.subst_intro (x : VName) (u : ValExpr) (τ : ValTy) :
    ∀ (σ : ValTy), x ∉ ValTy.fv σ → ∀ (k : Nat),
      ValTy.openRec k u σ = ValTy.subst x u (ValTy.openRec k (.var x τ) σ)
  | .space s, h => fun k => by
      simp only [ValTy.fv] at h
      simp only [ValTy.openRec, ValTy.subst, ValSpace.subst_intro x u τ s h k]
  | .piTy τ₀ τ₁, h => fun k => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at h
      simp only [ValTy.openRec, ValTy.subst,
        ValTy.subst_intro x u τ τ₀ h.1 k, ValTy.subst_intro x u τ τ₁ h.2 (k+1)]

theorem ValExpr.subst_intro (x : VName) (u : ValExpr) (τ : ValTy) :
    ∀ (e : ValExpr), x ∉ ValExpr.fv e → ∀ (k : Nat),
      ValExpr.openRec k u e = ValExpr.subst x u (ValExpr.openRec k (.var x τ) e)
  | .bvar i, _ => fun k => by
      by_cases hik : i = k
      · subst hik; simp only [ValExpr.openRec, ValExpr.subst, ↓reduceIte]
      · simp only [ValExpr.openRec, if_neg hik, ValExpr.subst]
  | .var y σ, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_insert, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, if_neg (Ne.symm h.1),
        ValTy.subst_intro x u τ σ h.2 k]
  | .rlit _, _ => fun _ => rfl
  | .zero s, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_intro x u τ s h k]
  | .delta n s, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_intro x u τ s h k]
  | .idelta s, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_intro x u τ s h k]
  | .scale e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst,
        ValExpr.subst_intro x u τ e₀ h.1 k, ValExpr.subst_intro x u τ e₁ h.2 k]
  | .vadd s e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_intro x u τ s h.1.1 k,
        ValExpr.subst_intro x u τ e₀ h.1.2 k, ValExpr.subst_intro x u τ e₁ h.2 k]
  | .dsumE e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst,
        ValExpr.subst_intro x u τ e₀ h.1 k, ValExpr.subst_intro x u τ e₁ h.2 k]
  | .tprodE e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst,
        ValExpr.subst_intro x u τ e₀ h.1 k, ValExpr.subst_intro x u τ e₁ h.2 k]
  | .vkrn e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst,
        ValExpr.subst_intro x u τ e₀ h.1 k, ValExpr.subst_intro x u τ e₁ h.2 k]
  | .vblk e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst,
        ValExpr.subst_intro x u τ e₀ h.1 k, ValExpr.subst_intro x u τ e₁ h.2 k]
  | .rrefRep e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst,
        ValExpr.subst_intro x u τ e₀ h.1 k, ValExpr.subst_intro x u τ e₁ h.2 k]
  | .vsum s es, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_intro x u τ s h.1 k,
        ValExpr.substList_intro x u τ es h.2 k]
  | .vlam τ₀ τ₁ e, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst,
        ValTy.subst_intro x u τ τ₀ h.1.1 k, ValTy.subst_intro x u τ τ₁ h.1.2 (k+1),
        ValExpr.subst_intro x u τ e h.2 (k+1)]
  | .ttv s e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_intro x u τ s h.1.1 k,
        ValExpr.subst_intro x u τ e₀ h.1.2 k, ValExpr.subst_intro x u τ e₁ h.2 k]
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_intro x u τ s₀ h.1.1.1 k,
        ValSpace.subst_intro x u τ s₁ h.1.1.2 k, ValExpr.subst_intro x u τ e₀ h.1.2 k,
        ValExpr.subst_intro x u τ e₁ h.2 k]
  | .appV e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst,
        ValExpr.subst_intro x u τ e₀ h.1 k, ValExpr.subst_intro x u τ e₁ h.2 k]
  | .reshap e σ σ₀, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h.1.1 k,
        ValTy.subst_intro x u τ σ h.1.2 k, ValTy.subst_intro x u τ σ₀ h.2 k]
  | .vtrans e, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h k]
  | .pinv e, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h k]
  | .inv e, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h k]
  | .svds e, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h k]
  | .gsvdS e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h.1.1 k,
        ValExpr.subst_intro x u τ a h.1.2 k, ValExpr.subst_intro x u τ b h.2 k]
  | .gsvdU e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h.1.1 k,
        ValExpr.subst_intro x u τ a h.1.2 k, ValExpr.subst_intro x u τ b h.2 k]
  | .gsvdUI e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h.1.1 k,
        ValExpr.subst_intro x u τ a h.1.2 k, ValExpr.subst_intro x u τ b h.2 k]
  | .gsvdV e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h.1.1 k,
        ValExpr.subst_intro x u τ a h.1.2 k, ValExpr.subst_intro x u τ b h.2 k]
  | .gsvdVI e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h.1.1 k,
        ValExpr.subst_intro x u τ a h.1.2 k, ValExpr.subst_intro x u τ b h.2 k]
  | .gpinv e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_intro x u τ e h.1.1 k,
        ValExpr.subst_intro x u τ a h.1.2 k, ValExpr.subst_intro x u τ b h.2 k]

theorem ValExpr.substList_intro (x : VName) (u : ValExpr) (τ : ValTy) :
    ∀ (es : List ValExpr), x ∉ ValExpr.fvList es → ∀ (k : Nat),
      ValExpr.openRecList k u es = ValExpr.substList x u (ValExpr.openRecList k (.var x τ) es)
  | [], _ => fun _ => rfl
  | e :: es, h => fun k => by
      simp only [ValExpr.fvList, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRecList, ValExpr.substList,
        ValExpr.subst_intro x u τ e h.1 k, ValExpr.substList_intro x u τ es h.2 k]
end

/-! ## Lemma kit (3): `open_lc` — opening a locally-closed term is the identity.

The lemma that is FALSE under 2.2B (annotated `bvar`) and CLEAN under 2.2A.
Via the standard `open_rec_lc_core` (Aydemir et al.): a doubly-opened term whose
outer open is a no-op has a no-op single open at the other index. -/

mutual
theorem ValSpace.openRec_lc_core :
    ∀ (s : ValSpace) (i j : Nat) (u v : ValExpr), i ≠ j →
      ValSpace.openRec i u (ValSpace.openRec j v s) = ValSpace.openRec j v s →
      ValSpace.openRec i u s = s
  | .empty, _, _, _, _, _, _ => rfl
  | .real, _, _, _, _, _, _ => rfl
  | .dsum s₀ s₁, i, j, u, v, hij, h => by
      simp only [ValSpace.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValSpace.openRec_lc_core s₀ i j u v hij h₀, ValSpace.openRec_lc_core s₁ i j u v hij h₁]
  | .tprod s₀ s₁, i, j, u, v, hij, h => by
      simp only [ValSpace.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValSpace.openRec_lc_core s₀ i j u v hij h₀, ValSpace.openRec_lc_core s₁ i j u v hij h₁]
  | .ffs p s e, i, j, u, v, hij, h => by
      simp only [ValSpace.openRec] at h ⊢
      injection h with _ h₀ h₁
      rw [ValSpace.openRec_lc_core s i j u v hij h₀, ValExpr.openRec_lc_core e i j u v hij h₁]

theorem ValTy.openRec_lc_core :
    ∀ (τ : ValTy) (i j : Nat) (u v : ValExpr), i ≠ j →
      ValTy.openRec i u (ValTy.openRec j v τ) = ValTy.openRec j v τ →
      ValTy.openRec i u τ = τ
  | .space s, i, j, u, v, hij, h => by
      simp only [ValTy.openRec] at h ⊢
      injection h with h₀
      rw [ValSpace.openRec_lc_core s i j u v hij h₀]
  | .piTy τ₀ τ₁, i, j, u, v, hij, h => by
      simp only [ValTy.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValTy.openRec_lc_core τ₀ i j u v hij h₀,
        ValTy.openRec_lc_core τ₁ (i+1) (j+1) u v (by omega) h₁]

theorem ValExpr.openRec_lc_core :
    ∀ (e : ValExpr) (i j : Nat) (u v : ValExpr), i ≠ j →
      ValExpr.openRec i u (ValExpr.openRec j v e) = ValExpr.openRec j v e →
      ValExpr.openRec i u e = e
  | .bvar n, i, j, _, _, hij, h => by
      by_cases hnj : n = j
      · have hni : ¬ n = i := fun e => hij (e.symm.trans hnj)
        simp only [ValExpr.openRec, if_neg hni]
      · simp only [ValExpr.openRec, if_neg hnj] at h ⊢; exact h
  | .var x τ, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with _ h₀
      rw [ValTy.openRec_lc_core τ i j u v hij h₀]
  | .rlit _, _, _, _, _, _, _ => rfl
  | .zero s, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀
      rw [ValSpace.openRec_lc_core s i j u v hij h₀]
  | .delta n s, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with _ h₀
      rw [ValSpace.openRec_lc_core s i j u v hij h₀]
  | .idelta s, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀
      rw [ValSpace.openRec_lc_core s i j u v hij h₀]
  | .scale e₀ e₁, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValExpr.openRec_lc_core e₀ i j u v hij h₀, ValExpr.openRec_lc_core e₁ i j u v hij h₁]
  | .vadd s e₀ e₁, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [ValSpace.openRec_lc_core s i j u v hij h₀,
        ValExpr.openRec_lc_core e₀ i j u v hij h₁,
        ValExpr.openRec_lc_core e₁ i j u v hij h₂]
  | .dsumE e₀ e₁, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValExpr.openRec_lc_core e₀ i j u v hij h₀, ValExpr.openRec_lc_core e₁ i j u v hij h₁]
  | .tprodE e₀ e₁, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValExpr.openRec_lc_core e₀ i j u v hij h₀, ValExpr.openRec_lc_core e₁ i j u v hij h₁]
  | .vkrn e₀ e₁, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValExpr.openRec_lc_core e₀ i j u v hij h₀, ValExpr.openRec_lc_core e₁ i j u v hij h₁]
  | .vblk e₀ e₁, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValExpr.openRec_lc_core e₀ i j u v hij h₀, ValExpr.openRec_lc_core e₁ i j u v hij h₁]
  | .rrefRep e₀ e₁, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValExpr.openRec_lc_core e₀ i j u v hij h₀, ValExpr.openRec_lc_core e₁ i j u v hij h₁]
  | .vsum s es, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValSpace.openRec_lc_core s i j u v hij h₀, ValExpr.openRecList_lc_core es i j u v hij h₁]
  | .vlam τ₀ τ₁ e, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [ValTy.openRec_lc_core τ₀ i j u v hij h₀,
        ValTy.openRec_lc_core τ₁ (i+1) (j+1) u v (by omega) h₁,
        ValExpr.openRec_lc_core e (i+1) (j+1) u v (by omega) h₂]
  | .ttv s e₀ e₁, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [ValSpace.openRec_lc_core s i j u v hij h₀, ValExpr.openRec_lc_core e₀ i j u v hij h₁,
        ValExpr.openRec_lc_core e₁ i j u v hij h₂]
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with _ _ h₀ h₁ h₂ h₃
      rw [ValSpace.openRec_lc_core s₀ i j u v hij h₀, ValSpace.openRec_lc_core s₁ i j u v hij h₁,
        ValExpr.openRec_lc_core e₀ i j u v hij h₂, ValExpr.openRec_lc_core e₁ i j u v hij h₃]
  | .appV e₀ e₁, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁
      rw [ValExpr.openRec_lc_core e₀ i j u v hij h₀, ValExpr.openRec_lc_core e₁ i j u v hij h₁]
  | .reshap e τ τ₀, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [ValExpr.openRec_lc_core e i j u v hij h₀,
        ValTy.openRec_lc_core τ i j u v hij h₁,
        ValTy.openRec_lc_core τ₀ i j u v hij h₂]
  | .vtrans e, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀
      rw [ValExpr.openRec_lc_core e i j u v hij h₀]
  | .pinv e, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀
      rw [ValExpr.openRec_lc_core e i j u v hij h₀]
  | .inv e, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀
      rw [ValExpr.openRec_lc_core e i j u v hij h₀]
  | .svds e, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀
      rw [ValExpr.openRec_lc_core e i j u v hij h₀]
  | .gsvdS e a b, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [ValExpr.openRec_lc_core e i j u v hij h₀, ValExpr.openRec_lc_core a i j u v hij h₁,
        ValExpr.openRec_lc_core b i j u v hij h₂]
  | .gsvdU e a b, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [ValExpr.openRec_lc_core e i j u v hij h₀, ValExpr.openRec_lc_core a i j u v hij h₁,
        ValExpr.openRec_lc_core b i j u v hij h₂]
  | .gsvdUI e a b, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [ValExpr.openRec_lc_core e i j u v hij h₀, ValExpr.openRec_lc_core a i j u v hij h₁,
        ValExpr.openRec_lc_core b i j u v hij h₂]
  | .gsvdV e a b, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [ValExpr.openRec_lc_core e i j u v hij h₀, ValExpr.openRec_lc_core a i j u v hij h₁,
        ValExpr.openRec_lc_core b i j u v hij h₂]
  | .gsvdVI e a b, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [ValExpr.openRec_lc_core e i j u v hij h₀, ValExpr.openRec_lc_core a i j u v hij h₁,
        ValExpr.openRec_lc_core b i j u v hij h₂]
  | .gpinv e a b, i, j, u, v, hij, h => by
      simp only [ValExpr.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [ValExpr.openRec_lc_core e i j u v hij h₀, ValExpr.openRec_lc_core a i j u v hij h₁,
        ValExpr.openRec_lc_core b i j u v hij h₂]

theorem ValExpr.openRecList_lc_core :
    ∀ (es : List ValExpr) (i j : Nat) (u v : ValExpr), i ≠ j →
      ValExpr.openRecList i u (ValExpr.openRecList j v es) = ValExpr.openRecList j v es →
      ValExpr.openRecList i u es = es
  | [], _, _, _, _, _, _ => rfl
  | e :: es, i, j, u, v, hij, h => by
      simp only [ValExpr.openRecList] at h ⊢
      injection h with h₀ h₁
      rw [ValExpr.openRec_lc_core e i j u v hij h₀, ValExpr.openRecList_lc_core es i j u v hij h₁]
end

/-! ## Lemma kit (3b): `open_lc` — opening a locally-closed term is the identity.

Term-mode recursion on the `lc` proof (the mutual `lc` inductives don't support the
`induction` tactic). Binder cases pick a fresh `x ∉ L` and transport the opened-body
fact to index `k+1` via `openRec_lc_core`. -/
mutual
theorem ValSpace.openRec_lc :
    ∀ {s : ValSpace}, ValSpace.lc s → ∀ (k : Nat) (u : ValExpr), ValSpace.openRec k u s = s
  | _, .empty => fun _ _ => rfl
  | _, .real => fun _ _ => rfl
  | _, .dsum h₀ h₁ => fun k u => by
      simp only [ValSpace.openRec, ValSpace.openRec_lc h₀ k u, ValSpace.openRec_lc h₁ k u]
  | _, .tprod h₀ h₁ => fun k u => by
      simp only [ValSpace.openRec, ValSpace.openRec_lc h₀ k u, ValSpace.openRec_lc h₁ k u]
  | _, .ffs hs he => fun k u => by
      simp only [ValSpace.openRec, ValSpace.openRec_lc hs k u, ValExpr.openRec_lc he k u]

theorem ValTy.openRec_lc :
    ∀ {τ : ValTy}, ValTy.lc τ → ∀ (k : Nat) (u : ValExpr), ValTy.openRec k u τ = τ
  | _, .space hs => fun k u => by simp only [ValTy.openRec, ValSpace.openRec_lc hs k u]
  | .piTy τ₀ τ₁, .piTy L hτ₀ hbody => fun k u => by
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset L
      have hb := ValTy.openRec_lc (hbody x hx) (k+1) u
      simp only [ValTy.openVar] at hb
      have hc := ValTy.openRec_lc_core τ₁ (k+1) 0 u (.var x τ₀) (by omega) hb
      simp only [ValTy.openRec, ValTy.openRec_lc hτ₀ k u, hc]

theorem ValExpr.openRec_lc :
    ∀ {e : ValExpr}, ValExpr.lc e → ∀ (k : Nat) (u : ValExpr), ValExpr.openRec k u e = e
  | _, .var hτ => fun k u => by simp only [ValExpr.openRec, ValTy.openRec_lc hτ k u]
  | .vlam τ₀ τ₁ e, .vlam L hτ₀ hT he => fun k u => by
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset L
      have hbT := ValTy.openRec_lc (hT x hx) (k+1) u
      have hbe := ValExpr.openRec_lc (he x hx) (k+1) u
      simp only [ValTy.openVar] at hbT
      simp only [ValExpr.openVar] at hbe
      have hcT := ValTy.openRec_lc_core τ₁ (k+1) 0 u (.var x τ₀) (by omega) hbT
      have hce := ValExpr.openRec_lc_core e (k+1) 0 u (.var x τ₀) (by omega) hbe
      simp only [ValExpr.openRec, ValTy.openRec_lc hτ₀ k u, hcT, hce]
  | _, .zero hs => fun k u => by simp only [ValExpr.openRec, ValSpace.openRec_lc hs k u]
  | _, .rlit => fun _ _ => rfl
  | _, .scale h₀ h₁ => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc h₀ k u, ValExpr.openRec_lc h₁ k u]
  | _, .vadd hs h₀ h₁ => fun k u => by
      simp only [ValExpr.openRec, ValSpace.openRec_lc hs k u,
        ValExpr.openRec_lc h₀ k u, ValExpr.openRec_lc h₁ k u]
  | _, .dsumE h₀ h₁ => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc h₀ k u, ValExpr.openRec_lc h₁ k u]
  | _, .tprodE h₀ h₁ => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc h₀ k u, ValExpr.openRec_lc h₁ k u]
  | _, .delta hs => fun k u => by simp only [ValExpr.openRec, ValSpace.openRec_lc hs k u]
  | _, .idelta hs => fun k u => by simp only [ValExpr.openRec, ValSpace.openRec_lc hs k u]
  | _, .vsum hs hes => fun k u => by
      simp only [ValExpr.openRec, ValSpace.openRec_lc hs k u, ValExpr.openRecList_eq_map]
      rw [List.map_congr_left (g := id) (fun e he => ValExpr.openRec_lc (hes e he) k u),
        List.map_id]
  | _, .ttv hs h₀ h₁ => fun k u => by
      simp only [ValExpr.openRec, ValSpace.openRec_lc hs k u, ValExpr.openRec_lc h₀ k u,
        ValExpr.openRec_lc h₁ k u]
  | _, .mtm hs₀ hs₁ h₀ h₁ => fun k u => by
      simp only [ValExpr.openRec, ValSpace.openRec_lc hs₀ k u, ValSpace.openRec_lc hs₁ k u,
        ValExpr.openRec_lc h₀ k u, ValExpr.openRec_lc h₁ k u]
  | _, .appV h₀ h₁ => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc h₀ k u, ValExpr.openRec_lc h₁ k u]
  | _, .vkrn h₀ h₁ => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc h₀ k u, ValExpr.openRec_lc h₁ k u]
  | _, .vblk h₀ h₁ => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc h₀ k u, ValExpr.openRec_lc h₁ k u]
  | _, .reshap he hτ hτ₀ => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc he k u,
        ValTy.openRec_lc hτ k u, ValTy.openRec_lc hτ₀ k u]
  | _, .vtrans he => fun k u => by simp only [ValExpr.openRec, ValExpr.openRec_lc he k u]
  | _, .gsvdS he ha hb => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc he k u, ValExpr.openRec_lc ha k u,
        ValExpr.openRec_lc hb k u]
  | _, .gsvdU he ha hb => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc he k u, ValExpr.openRec_lc ha k u,
        ValExpr.openRec_lc hb k u]
  | _, .gsvdUI he ha hb => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc he k u, ValExpr.openRec_lc ha k u,
        ValExpr.openRec_lc hb k u]
  | _, .gsvdV he ha hb => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc he k u, ValExpr.openRec_lc ha k u,
        ValExpr.openRec_lc hb k u]
  | _, .gsvdVI he ha hb => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc he k u, ValExpr.openRec_lc ha k u,
        ValExpr.openRec_lc hb k u]
  | _, .pinv he => fun k u => by simp only [ValExpr.openRec, ValExpr.openRec_lc he k u]
  | _, .gpinv he ha hb => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc he k u, ValExpr.openRec_lc ha k u,
        ValExpr.openRec_lc hb k u]
  | _, .rrefRep h₀ h₁ => fun k u => by
      simp only [ValExpr.openRec, ValExpr.openRec_lc h₀ k u, ValExpr.openRec_lc h₁ k u]
  | _, .inv he => fun k u => by simp only [ValExpr.openRec, ValExpr.openRec_lc he k u]
  | _, .svds he => fun k u => by simp only [ValExpr.openRec, ValExpr.openRec_lc he k u]
end

/-! ## Lemma kit (4): `subst_openRec` — substitution commutes with opening.

`lc u → subst x u (openRec k v e) = openRec k (subst x u v) (subst x u e)`. The β
substitution lemma. Only the `var x` leaf uses `lc u` (via `open_lc`, to discharge
`openRec k _ u = u`); everything else is structural. -/

mutual
theorem ValSpace.subst_openRec (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
    ∀ (s : ValSpace) (k : Nat) (v : ValExpr),
      ValSpace.subst x u (ValSpace.openRec k v s)
        = ValSpace.openRec k (ValExpr.subst x u v) (ValSpace.subst x u s)
  | .empty, _, _ => rfl
  | .real, _, _ => rfl
  | .dsum s₀ s₁, k, v => by
      simp only [ValSpace.openRec, ValSpace.subst, ValSpace.subst_openRec x u hu s₀ k v,
        ValSpace.subst_openRec x u hu s₁ k v]
  | .tprod s₀ s₁, k, v => by
      simp only [ValSpace.openRec, ValSpace.subst, ValSpace.subst_openRec x u hu s₀ k v,
        ValSpace.subst_openRec x u hu s₁ k v]
  | .ffs p s e, k, v => by
      simp only [ValSpace.openRec, ValSpace.subst, ValSpace.subst_openRec x u hu s k v,
        ValExpr.subst_openRec x u hu e k v]

theorem ValTy.subst_openRec (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
    ∀ (τ : ValTy) (k : Nat) (v : ValExpr),
      ValTy.subst x u (ValTy.openRec k v τ)
        = ValTy.openRec k (ValExpr.subst x u v) (ValTy.subst x u τ)
  | .space s, k, v => by
      simp only [ValTy.openRec, ValTy.subst, ValSpace.subst_openRec x u hu s k v]
  | .piTy τ₀ τ₁, k, v => by
      simp only [ValTy.openRec, ValTy.subst, ValTy.subst_openRec x u hu τ₀ k v,
        ValTy.subst_openRec x u hu τ₁ (k+1) v]

theorem ValExpr.subst_openRec (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
    ∀ (e : ValExpr) (k : Nat) (v : ValExpr),
      ValExpr.subst x u (ValExpr.openRec k v e)
        = ValExpr.openRec k (ValExpr.subst x u v) (ValExpr.subst x u e)
  | .bvar i, k, v => by
      by_cases hik : i = k
      · subst hik; simp only [ValExpr.openRec, ValExpr.subst, ↓reduceIte]
      · simp only [ValExpr.openRec, if_neg hik, ValExpr.subst]
  | .var y τ, k, v => by
      by_cases hyx : y = x
      · subst hyx
        simp only [ValExpr.openRec, ValExpr.subst, ↓reduceIte, ValExpr.openRec_lc hu k _]
      · simp only [ValExpr.openRec, ValExpr.subst, if_neg hyx,
          ValTy.subst_openRec x u hu τ k v]
  | .rlit _, _, _ => rfl
  | .zero s, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_openRec x u hu s k v]
  | .delta n s, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_openRec x u hu s k v]
  | .idelta s, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_openRec x u hu s k v]
  | .scale e₀ e₁, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e₀ k v,
        ValExpr.subst_openRec x u hu e₁ k v]
  | .vadd s e₀ e₁, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_openRec x u hu s k v,
        ValExpr.subst_openRec x u hu e₀ k v,
        ValExpr.subst_openRec x u hu e₁ k v]
  | .dsumE e₀ e₁, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e₀ k v,
        ValExpr.subst_openRec x u hu e₁ k v]
  | .tprodE e₀ e₁, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e₀ k v,
        ValExpr.subst_openRec x u hu e₁ k v]
  | .vkrn e₀ e₁, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e₀ k v,
        ValExpr.subst_openRec x u hu e₁ k v]
  | .vblk e₀ e₁, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e₀ k v,
        ValExpr.subst_openRec x u hu e₁ k v]
  | .rrefRep e₀ e₁, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e₀ k v,
        ValExpr.subst_openRec x u hu e₁ k v]
  | .vsum s es, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_openRec x u hu s k v,
        ValExpr.substList_openRec x u hu es k v]
  | .vlam τ₀ τ₁ e, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValTy.subst_openRec x u hu τ₀ k v,
        ValTy.subst_openRec x u hu τ₁ (k+1) v, ValExpr.subst_openRec x u hu e (k+1) v]
  | .ttv s e₀ e₁, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_openRec x u hu s k v,
        ValExpr.subst_openRec x u hu e₀ k v, ValExpr.subst_openRec x u hu e₁ k v]
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValSpace.subst_openRec x u hu s₀ k v,
        ValSpace.subst_openRec x u hu s₁ k v, ValExpr.subst_openRec x u hu e₀ k v,
        ValExpr.subst_openRec x u hu e₁ k v]
  | .appV e₀ e₁, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e₀ k v,
        ValExpr.subst_openRec x u hu e₁ k v]
  | .reshap e τ τ₀, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v,
        ValTy.subst_openRec x u hu τ k v, ValTy.subst_openRec x u hu τ₀ k v]
  | .vtrans e, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v]
  | .pinv e, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v]
  | .inv e, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v]
  | .svds e, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v]
  | .gsvdS e a b, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v,
        ValExpr.subst_openRec x u hu a k v, ValExpr.subst_openRec x u hu b k v]
  | .gsvdU e a b, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v,
        ValExpr.subst_openRec x u hu a k v, ValExpr.subst_openRec x u hu b k v]
  | .gsvdUI e a b, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v,
        ValExpr.subst_openRec x u hu a k v, ValExpr.subst_openRec x u hu b k v]
  | .gsvdV e a b, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v,
        ValExpr.subst_openRec x u hu a k v, ValExpr.subst_openRec x u hu b k v]
  | .gsvdVI e a b, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v,
        ValExpr.subst_openRec x u hu a k v, ValExpr.subst_openRec x u hu b k v]
  | .gpinv e a b, k, v => by
      simp only [ValExpr.openRec, ValExpr.subst, ValExpr.subst_openRec x u hu e k v,
        ValExpr.subst_openRec x u hu a k v, ValExpr.subst_openRec x u hu b k v]

theorem ValExpr.substList_openRec (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
    ∀ (es : List ValExpr) (k : Nat) (v : ValExpr),
      ValExpr.substList x u (ValExpr.openRecList k v es)
        = ValExpr.openRecList k (ValExpr.subst x u v) (ValExpr.substList x u es)
  | [], _, _ => rfl
  | e :: es, k, v => by
      simp only [ValExpr.openRecList, ValExpr.substList, ValExpr.subst_openRec x u hu e k v,
        ValExpr.substList_openRec x u hu es k v]
end

/-! ## Lemma kit (5): `close_openVar` — close after open-with-fresh recovers the body.

`x ∉ fv e → closeRec k x (openRec k (.var x τ) e) = e`. Clean under 2.2A: the
introduced `.var x τ` abstracts straight back to `bvar k` (no annotation, so the
opened-with `τ` is forgotten — exactly what we want). Structural induction; `x ∉ fv`
ensures the only `x`-occurrence is the one `openRec` introduced. -/

mutual
theorem ValSpace.close_openVar (x : VName) (τ : ValTy) :
    ∀ (s : ValSpace), x ∉ ValSpace.fv s → ∀ (k : Nat),
      ValSpace.closeRec k x (ValSpace.openRec k (.var x τ) s) = s
  | .empty, _ => fun _ => rfl
  | .real, _ => fun _ => rfl
  | .dsum s₀ s₁, h => fun k => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h
      simp only [ValSpace.openRec, ValSpace.closeRec, ValSpace.close_openVar x τ s₀ h.1 k,
        ValSpace.close_openVar x τ s₁ h.2 k]
  | .tprod s₀ s₁, h => fun k => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h
      simp only [ValSpace.openRec, ValSpace.closeRec, ValSpace.close_openVar x τ s₀ h.1 k,
        ValSpace.close_openVar x τ s₁ h.2 k]
  | .ffs p s e, h => fun k => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at h
      simp only [ValSpace.openRec, ValSpace.closeRec, ValSpace.close_openVar x τ s h.1 k,
        ValExpr.close_openVar x τ e h.2 k]

theorem ValTy.close_openVar (x : VName) (τ : ValTy) :
    ∀ (σ : ValTy), x ∉ ValTy.fv σ → ∀ (k : Nat),
      ValTy.closeRec k x (ValTy.openRec k (.var x τ) σ) = σ
  | .space s, h => fun k => by
      simp only [ValTy.fv] at h
      simp only [ValTy.openRec, ValTy.closeRec, ValSpace.close_openVar x τ s h k]
  | .piTy τ₀ τ₁, h => fun k => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at h
      simp only [ValTy.openRec, ValTy.closeRec, ValTy.close_openVar x τ τ₀ h.1 k,
        ValTy.close_openVar x τ τ₁ h.2 (k+1)]

theorem ValExpr.close_openVar (x : VName) (τ : ValTy) :
    ∀ (e : ValExpr), x ∉ ValExpr.fv e → ∀ (k : Nat),
      ValExpr.closeRec k x (ValExpr.openRec k (.var x τ) e) = e
  | .bvar i, _ => fun k => by
      by_cases hik : i = k
      · subst hik; simp only [ValExpr.openRec, ValExpr.closeRec, ↓reduceIte]
      · simp only [ValExpr.openRec, if_neg hik, ValExpr.closeRec]
  | .var y σ, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_insert, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, if_neg (Ne.symm h.1),
        ValTy.close_openVar x τ σ h.2 k]
  | .rlit _, _ => fun _ => rfl
  | .zero s, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValSpace.close_openVar x τ s h k]
  | .delta n s, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValSpace.close_openVar x τ s h k]
  | .idelta s, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValSpace.close_openVar x τ s h k]
  | .scale e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e₀ h.1 k,
        ValExpr.close_openVar x τ e₁ h.2 k]
  | .vadd s e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValSpace.close_openVar x τ s h.1.1 k,
        ValExpr.close_openVar x τ e₀ h.1.2 k,
        ValExpr.close_openVar x τ e₁ h.2 k]
  | .dsumE e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e₀ h.1 k,
        ValExpr.close_openVar x τ e₁ h.2 k]
  | .tprodE e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e₀ h.1 k,
        ValExpr.close_openVar x τ e₁ h.2 k]
  | .vkrn e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e₀ h.1 k,
        ValExpr.close_openVar x τ e₁ h.2 k]
  | .vblk e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e₀ h.1 k,
        ValExpr.close_openVar x τ e₁ h.2 k]
  | .rrefRep e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e₀ h.1 k,
        ValExpr.close_openVar x τ e₁ h.2 k]
  | .vsum s es, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValSpace.close_openVar x τ s h.1 k,
        ValExpr.closeList_openList x τ es h.2 k]
  | .vlam τ₀ τ₁ e, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValTy.close_openVar x τ τ₀ h.1.1 k,
        ValTy.close_openVar x τ τ₁ h.1.2 (k+1), ValExpr.close_openVar x τ e h.2 (k+1)]
  | .ttv s e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValSpace.close_openVar x τ s h.1.1 k,
        ValExpr.close_openVar x τ e₀ h.1.2 k, ValExpr.close_openVar x τ e₁ h.2 k]
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValSpace.close_openVar x τ s₀ h.1.1.1 k,
        ValSpace.close_openVar x τ s₁ h.1.1.2 k, ValExpr.close_openVar x τ e₀ h.1.2 k,
        ValExpr.close_openVar x τ e₁ h.2 k]
  | .appV e₀ e₁, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e₀ h.1 k,
        ValExpr.close_openVar x τ e₁ h.2 k]
  | .reshap e σ σ₀, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h.1.1 k,
        ValTy.close_openVar x τ σ h.1.2 k, ValTy.close_openVar x τ σ₀ h.2 k]
  | .vtrans e, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h k]
  | .pinv e, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h k]
  | .inv e, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h k]
  | .svds e, h => fun k => by
      simp only [ValExpr.fv] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h k]
  | .gsvdS e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h.1.1 k,
        ValExpr.close_openVar x τ a h.1.2 k, ValExpr.close_openVar x τ b h.2 k]
  | .gsvdU e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h.1.1 k,
        ValExpr.close_openVar x τ a h.1.2 k, ValExpr.close_openVar x τ b h.2 k]
  | .gsvdUI e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h.1.1 k,
        ValExpr.close_openVar x τ a h.1.2 k, ValExpr.close_openVar x τ b h.2 k]
  | .gsvdV e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h.1.1 k,
        ValExpr.close_openVar x τ a h.1.2 k, ValExpr.close_openVar x τ b h.2 k]
  | .gsvdVI e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h.1.1 k,
        ValExpr.close_openVar x τ a h.1.2 k, ValExpr.close_openVar x τ b h.2 k]
  | .gpinv e a b, h => fun k => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.close_openVar x τ e h.1.1 k,
        ValExpr.close_openVar x τ a h.1.2 k, ValExpr.close_openVar x τ b h.2 k]

theorem ValExpr.closeList_openList (x : VName) (τ : ValTy) :
    ∀ (es : List ValExpr), x ∉ ValExpr.fvList es → ∀ (k : Nat),
      ValExpr.closeRecList k x (ValExpr.openRecList k (.var x τ) es) = es
  | [], _ => fun _ => rfl
  | e :: es, h => fun k => by
      simp only [ValExpr.fvList, Finset.mem_union, not_or] at h
      simp only [ValExpr.openRecList, ValExpr.closeRecList, ValExpr.close_openVar x τ e h.1 k,
        ValExpr.closeList_openList x τ es h.2 k]
end

/-! ## Lemma kit (6): `fv` under `openRec` / `subst` (scoping subsets).

`fv (openRec k v e) ⊆ fv e ∪ fv v` and `fv (subst x u e) ⊆ fv e ∪ fv u`. Membership
form (mirrors the retired `allNames_subst_mem`); subset corollaries below. -/

mutual
theorem ValSpace.fv_openRec_mem {a : VName} {k : Nat} {v : ValExpr} :
    ∀ {s : ValSpace}, a ∈ ValSpace.fv (ValSpace.openRec k v s) → a ∈ ValSpace.fv s ∪ ValExpr.fv v
  | .empty, h => by simp [ValSpace.openRec, ValSpace.fv] at h
  | .real, h => by simp [ValSpace.openRec, ValSpace.fv] at h
  | .dsum s₀ s₁, h => by
      simp only [ValSpace.openRec, ValSpace.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValSpace.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .tprod s₀ s₁, h => by
      simp only [ValSpace.openRec, ValSpace.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValSpace.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .ffs p s e, h => by
      simp only [ValSpace.openRec, ValSpace.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · rcases Finset.mem_union.mp (ValSpace.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'

theorem ValTy.fv_openRec_mem {a : VName} {k : Nat} {v : ValExpr} :
    ∀ {τ : ValTy}, a ∈ ValTy.fv (ValTy.openRec k v τ) → a ∈ ValTy.fv τ ∪ ValExpr.fv v
  | .space s, h => by
      simp only [ValTy.openRec, ValTy.fv] at h ⊢; exact ValSpace.fv_openRec_mem h
  | .piTy τ₀ τ₁, h => by
      simp only [ValTy.openRec, ValTy.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValTy.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

theorem ValExpr.fv_openRec_mem {a : VName} {k : Nat} {v : ValExpr} :
    ∀ {e : ValExpr}, a ∈ ValExpr.fv (ValExpr.openRec k v e) → a ∈ ValExpr.fv e ∪ ValExpr.fv v
  | .bvar i, h => by
      by_cases hik : i = k
      · subst hik; simp only [ValExpr.openRec, ↓reduceIte] at h
        exact Finset.mem_union_right _ h
      · simp [ValExpr.openRec, if_neg hik, ValExpr.fv] at h
  | .var y σ, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_insert, Finset.mem_union] at h ⊢
      rcases h with rfl | h
      · exact Or.inl (Or.inl rfl)
      · rcases Finset.mem_union.mp (ValTy.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .rlit _, h => by simp [ValExpr.openRec, ValExpr.fv] at h
  | .zero s, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValSpace.fv_openRec_mem h
  | .delta n s, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValSpace.fv_openRec_mem h
  | .idelta s, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValSpace.fv_openRec_mem h
  | .scale e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .vadd s e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValSpace.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .dsumE e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .tprodE e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .vkrn e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .vblk e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .rrefRep e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .vsum s es, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union, ValExpr.openRecList_eq_map] at h ⊢
      rcases h with h | h
      · rcases Finset.mem_union.mp (ValSpace.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rw [ValExpr.mem_fvList] at h
        obtain ⟨e', hmem, he'⟩ := h
        obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hmem
        rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem he') with h' | h'
        · exact Or.inl (Or.inr (ValExpr.mem_fvList.mpr ⟨e₀, he₀, h'⟩))
        · exact Or.inr h'
  | .vlam τ₀ τ₁ e, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValTy.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValTy.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .ttv s e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValSpace.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with ((h | h) | h) | h
      · rcases Finset.mem_union.mp (ValSpace.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inl h')))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValSpace.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inr h')))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .appV e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .reshap e σ σ₀, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValTy.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValTy.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .vtrans e, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValExpr.fv_openRec_mem h
  | .pinv e, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValExpr.fv_openRec_mem h
  | .inv e, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValExpr.fv_openRec_mem h
  | .svds e, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValExpr.fv_openRec_mem h
  | .gsvdS e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .gsvdU e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .gsvdUI e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .gsvdV e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .gsvdVI e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .gpinv e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
end

theorem ValSpace.fv_openRec_subset (k : Nat) (v : ValExpr) (s : ValSpace) :
    ValSpace.fv (ValSpace.openRec k v s) ⊆ ValSpace.fv s ∪ ValExpr.fv v :=
  fun _ ha => ValSpace.fv_openRec_mem ha
theorem ValTy.fv_openRec_subset (k : Nat) (v : ValExpr) (τ : ValTy) :
    ValTy.fv (ValTy.openRec k v τ) ⊆ ValTy.fv τ ∪ ValExpr.fv v :=
  fun _ ha => ValTy.fv_openRec_mem ha
theorem ValExpr.fv_openRec_subset (k : Nat) (v : ValExpr) (e : ValExpr) :
    ValExpr.fv (ValExpr.openRec k v e) ⊆ ValExpr.fv e ∪ ValExpr.fv v :=
  fun _ ha => ValExpr.fv_openRec_mem ha

mutual
theorem ValSpace.fv_subset_openRec {a : VName} {v : ValExpr} :
    ∀ {k : Nat} {s : ValSpace}, a ∈ ValSpace.fv s → a ∈ ValSpace.fv (ValSpace.openRec k v s)
  | _, .empty, h => by simp only [ValSpace.fv] at h; exact absurd h (Finset.notMem_empty _)
  | _, .real, h => by simp only [ValSpace.fv] at h; exact absurd h (Finset.notMem_empty _)
  | _, .dsum s₀ s₁, h => by
      simp only [ValSpace.openRec, ValSpace.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValSpace.fv_subset_openRec h)
      · exact Or.inr (ValSpace.fv_subset_openRec h)
  | _, .tprod s₀ s₁, h => by
      simp only [ValSpace.openRec, ValSpace.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValSpace.fv_subset_openRec h)
      · exact Or.inr (ValSpace.fv_subset_openRec h)
  | _, .ffs p s e, h => by
      simp only [ValSpace.openRec, ValSpace.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValSpace.fv_subset_openRec h)
      · exact Or.inr (ValExpr.fv_subset_openRec h)

theorem ValTy.fv_subset_openRec {a : VName} {v : ValExpr} :
    ∀ {k : Nat} {τ : ValTy}, a ∈ ValTy.fv τ → a ∈ ValTy.fv (ValTy.openRec k v τ)
  | _, .space s, h => by
      simp only [ValTy.openRec, ValTy.fv] at h ⊢; exact ValSpace.fv_subset_openRec h
  | _, .piTy τ₀ τ₁, h => by
      simp only [ValTy.openRec, ValTy.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValTy.fv_subset_openRec h)
      · exact Or.inr (ValTy.fv_subset_openRec h)

theorem ValExpr.fv_subset_openRec {a : VName} {v : ValExpr} :
    ∀ {k : Nat} {e : ValExpr}, a ∈ ValExpr.fv e → a ∈ ValExpr.fv (ValExpr.openRec k v e)
  | _, .bvar _, h => by simp only [ValExpr.fv] at h; exact absurd h (Finset.notMem_empty _)
  | _, .rlit _, h => by simp only [ValExpr.fv] at h; exact absurd h (Finset.notMem_empty _)
  | _, .var y σ, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_insert] at h ⊢
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (ValTy.fv_subset_openRec h)
  | _, .zero s, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValSpace.fv_subset_openRec h
  | _, .delta n s, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValSpace.fv_subset_openRec h
  | _, .idelta s, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValSpace.fv_subset_openRec h
  | _, .scale e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValExpr.fv_subset_openRec h)
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .vadd s e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (ValSpace.fv_subset_openRec h))
      · exact Or.inl (Or.inr (ValExpr.fv_subset_openRec h))
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .dsumE e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValExpr.fv_subset_openRec h)
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .tprodE e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValExpr.fv_subset_openRec h)
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .vkrn e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValExpr.fv_subset_openRec h)
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .vblk e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValExpr.fv_subset_openRec h)
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .rrefRep e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValExpr.fv_subset_openRec h)
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .vsum s es, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union,
        ValExpr.openRecList_eq_map] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValSpace.fv_subset_openRec h)
      · rw [ValExpr.mem_fvList] at h
        obtain ⟨e', he', ha⟩ := h
        exact Or.inr (ValExpr.mem_fvList.mpr
          ⟨ValExpr.openRec _ v e', List.mem_map.mpr ⟨e', he', rfl⟩,
           ValExpr.fv_subset_openRec ha⟩)
  | _, .vlam τ₀ τ₁ e, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (ValTy.fv_subset_openRec h))
      · exact Or.inl (Or.inr (ValTy.fv_subset_openRec h))
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .ttv s e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (ValSpace.fv_subset_openRec h))
      · exact Or.inl (Or.inr (ValExpr.fv_subset_openRec h))
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .mtm n₀ n₁ s₀ s₁ e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (ValSpace.fv_subset_openRec h)))
      · exact Or.inl (Or.inl (Or.inr (ValSpace.fv_subset_openRec h)))
      · exact Or.inl (Or.inr (ValExpr.fv_subset_openRec h))
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .appV e₀ e₁, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (ValExpr.fv_subset_openRec h)
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .reshap e σ σ₀, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (ValExpr.fv_subset_openRec h))
      · exact Or.inl (Or.inr (ValTy.fv_subset_openRec h))
      · exact Or.inr (ValTy.fv_subset_openRec h)
  | _, .vtrans e, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValExpr.fv_subset_openRec h
  | _, .pinv e, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValExpr.fv_subset_openRec h
  | _, .inv e, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValExpr.fv_subset_openRec h
  | _, .svds e, h => by
      simp only [ValExpr.openRec, ValExpr.fv] at h ⊢; exact ValExpr.fv_subset_openRec h
  | _, .gsvdS e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (ValExpr.fv_subset_openRec h))
      · exact Or.inl (Or.inr (ValExpr.fv_subset_openRec h))
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .gsvdU e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (ValExpr.fv_subset_openRec h))
      · exact Or.inl (Or.inr (ValExpr.fv_subset_openRec h))
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .gsvdUI e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (ValExpr.fv_subset_openRec h))
      · exact Or.inl (Or.inr (ValExpr.fv_subset_openRec h))
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .gsvdV e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (ValExpr.fv_subset_openRec h))
      · exact Or.inl (Or.inr (ValExpr.fv_subset_openRec h))
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .gsvdVI e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (ValExpr.fv_subset_openRec h))
      · exact Or.inl (Or.inr (ValExpr.fv_subset_openRec h))
      · exact Or.inr (ValExpr.fv_subset_openRec h)
  | _, .gpinv e a b, h => by
      simp only [ValExpr.openRec, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (ValExpr.fv_subset_openRec h))
      · exact Or.inl (Or.inr (ValExpr.fv_subset_openRec h))
      · exact Or.inr (ValExpr.fv_subset_openRec h)
end

/-! `fv (subst x u e) ⊆ fv e ∪ fv u` — same shape as `fv_openRec_mem`, with the
`bvar`/`var` leaves adjusted for free-variable substitution. -/

mutual
theorem ValSpace.fv_subst_mem {a x : VName} {u : ValExpr} :
    ∀ {s : ValSpace}, a ∈ ValSpace.fv (ValSpace.subst x u s) → a ∈ ValSpace.fv s ∪ ValExpr.fv u
  | .empty, h => by simp [ValSpace.subst, ValSpace.fv] at h
  | .real, h => by simp [ValSpace.subst, ValSpace.fv] at h
  | .dsum s₀ s₁, h => by
      simp only [ValSpace.subst, ValSpace.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValSpace.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .tprod s₀ s₁, h => by
      simp only [ValSpace.subst, ValSpace.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValSpace.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .ffs p s e, h => by
      simp only [ValSpace.subst, ValSpace.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · rcases Finset.mem_union.mp (ValSpace.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'

theorem ValTy.fv_subst_mem {a x : VName} {u : ValExpr} :
    ∀ {τ : ValTy}, a ∈ ValTy.fv (ValTy.subst x u τ) → a ∈ ValTy.fv τ ∪ ValExpr.fv u
  | .space s, h => by
      simp only [ValTy.subst, ValTy.fv] at h ⊢; exact ValSpace.fv_subst_mem h
  | .piTy τ₀ τ₁, h => by
      simp only [ValTy.subst, ValTy.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValTy.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

theorem ValExpr.fv_subst_mem {a x : VName} {u : ValExpr} :
    ∀ {e : ValExpr}, a ∈ ValExpr.fv (ValExpr.subst x u e) → a ∈ ValExpr.fv e ∪ ValExpr.fv u
  | .bvar i, h => by simp [ValExpr.subst, ValExpr.fv] at h
  | .var y σ, h => by
      by_cases hyx : y = x
      · subst hyx; simp only [ValExpr.subst, ↓reduceIte] at h; exact Finset.mem_union_right _ h
      · simp only [ValExpr.subst, if_neg hyx, ValExpr.fv, Finset.mem_insert, Finset.mem_union] at h ⊢
        rcases h with rfl | h
        · exact Or.inl (Or.inl rfl)
        · rcases Finset.mem_union.mp (ValTy.fv_subst_mem h) with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
  | .rlit _, h => by simp [ValExpr.subst, ValExpr.fv] at h
  | .zero s, h => by
      simp only [ValExpr.subst, ValExpr.fv] at h ⊢; exact ValSpace.fv_subst_mem h
  | .delta n s, h => by
      simp only [ValExpr.subst, ValExpr.fv] at h ⊢; exact ValSpace.fv_subst_mem h
  | .idelta s, h => by
      simp only [ValExpr.subst, ValExpr.fv] at h ⊢; exact ValSpace.fv_subst_mem h
  | .scale e₀ e₁, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .vadd s e₀ e₁, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValSpace.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .dsumE e₀ e₁, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .tprodE e₀ e₁, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .vkrn e₀ e₁, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .vblk e₀ e₁, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .rrefRep e₀ e₁, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .vsum s es, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union, ValExpr.substList_eq_map] at h ⊢
      rcases h with h | h
      · rcases Finset.mem_union.mp (ValSpace.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rw [ValExpr.mem_fvList] at h
        obtain ⟨e', hmem, he'⟩ := h
        obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hmem
        rcases Finset.mem_union.mp (ValExpr.fv_subst_mem he') with h' | h'
        · exact Or.inl (Or.inr (ValExpr.mem_fvList.mpr ⟨e₀, he₀, h'⟩))
        · exact Or.inr h'
  | .vlam τ₀ τ₁ e, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValTy.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValTy.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .ttv s e₀ e₁, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValSpace.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with ((h | h) | h) | h
      · rcases Finset.mem_union.mp (ValSpace.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inl h')))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValSpace.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inr h')))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .appV e₀ e₁, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .reshap e σ σ₀, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValTy.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValTy.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .vtrans e, h => by
      simp only [ValExpr.subst, ValExpr.fv] at h ⊢; exact ValExpr.fv_subst_mem h
  | .pinv e, h => by
      simp only [ValExpr.subst, ValExpr.fv] at h ⊢; exact ValExpr.fv_subst_mem h
  | .inv e, h => by
      simp only [ValExpr.subst, ValExpr.fv] at h ⊢; exact ValExpr.fv_subst_mem h
  | .svds e, h => by
      simp only [ValExpr.subst, ValExpr.fv] at h ⊢; exact ValExpr.fv_subst_mem h
  | .gsvdS e a b, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .gsvdU e a b, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .gsvdUI e a b, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .gsvdV e a b, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .gsvdVI e a b, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .gpinv e a b, h => by
      simp only [ValExpr.subst, ValExpr.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (ValExpr.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
end

theorem ValSpace.fv_subst_subset (x : VName) (u : ValExpr) (s : ValSpace) :
    ValSpace.fv (ValSpace.subst x u s) ⊆ ValSpace.fv s ∪ ValExpr.fv u :=
  fun _ ha => ValSpace.fv_subst_mem ha
theorem ValTy.fv_subst_subset (x : VName) (u : ValExpr) (τ : ValTy) :
    ValTy.fv (ValTy.subst x u τ) ⊆ ValTy.fv τ ∪ ValExpr.fv u :=
  fun _ ha => ValTy.fv_subst_mem ha
theorem ValExpr.fv_subst_subset (x : VName) (u : ValExpr) (e : ValExpr) :
    ValExpr.fv (ValExpr.subst x u e) ⊆ ValExpr.fv e ∪ ValExpr.fv u :=
  fun _ ha => ValExpr.fv_subst_mem ha

end GLang
