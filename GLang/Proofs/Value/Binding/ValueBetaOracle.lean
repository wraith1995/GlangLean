import GLang.Proofs.Value.Binding.ValueBeta
import GLang.Proofs.Value.Binding.ValueRaise

namespace GLang

/-! Finite support proves substitution invariance from the existing oracle opening law. -/
mutual
  def ValSpace.seal (k : Nat) : ValSpace → ValSpace
    | .empty => .empty
    | .real => .real
    | .dsum s0 s1 => .dsum (ValSpace.seal k s0) (ValSpace.seal k s1)
    | .tprod s0 s1 => .tprod (ValSpace.seal k s0) (ValSpace.seal k s1)
    | .ffs p s e => .ffs p (ValSpace.seal k s) (ValExpr.seal k e)
  def ValTy.seal (k : Nat) : ValTy → ValTy
    | .space s => .space (ValSpace.seal k s)
    | .piTy t0 t1 => .piTy (ValTy.seal k t0) (ValTy.seal (k + 1) t1)
  def ValExpr.seal (k : Nat) : ValExpr → ValExpr
    | .bvar i => if k ≤ i then .rlit 0 else .bvar i
    | .var y t => .var y (ValTy.seal k t)
    | .vlam t0 t1 e => .vlam (ValTy.seal k t0) (ValTy.seal (k + 1) t1) (ValExpr.seal (k + 1) e)
    | .zero s => .zero (ValSpace.seal k s)
    | .rlit r => .rlit r
    | .scale e0 e1 => .scale (ValExpr.seal k e0) (ValExpr.seal k e1)
    | .dsumE e0 e1 => .dsumE (ValExpr.seal k e0) (ValExpr.seal k e1)
    | .tprodE e0 e1 => .tprodE (ValExpr.seal k e0) (ValExpr.seal k e1)
    | .appV e0 e1 => .appV (ValExpr.seal k e0) (ValExpr.seal k e1)
    | .vkrn e0 e1 => .vkrn (ValExpr.seal k e0) (ValExpr.seal k e1)
    | .vblk e0 e1 => .vblk (ValExpr.seal k e0) (ValExpr.seal k e1)
    | .rrefRep e0 e1 => .rrefRep (ValExpr.seal k e0) (ValExpr.seal k e1)
    | .vadd s e0 e1 => .vadd (ValSpace.seal k s) (ValExpr.seal k e0) (ValExpr.seal k e1)
    | .delta i s => .delta i (ValSpace.seal k s)
    | .idelta s => .idelta (ValSpace.seal k s)
    | .vsum s es => .vsum (ValSpace.seal k s) (ValExpr.sealList k es)
    | .ttv s e0 e1 => .ttv (ValSpace.seal k s) (ValExpr.seal k e0) (ValExpr.seal k e1)
    | .mtm i j s0 s1 e0 e1 => .mtm i j (ValSpace.seal k s0) (ValSpace.seal k s1) (ValExpr.seal k e0) (ValExpr.seal k e1)
    | .reshap e t t0 => .reshap (ValExpr.seal k e) (ValTy.seal k t) (ValTy.seal k t0)
    | .vtrans e => .vtrans (ValExpr.seal k e)
    | .pinv e => .pinv (ValExpr.seal k e)
    | .inv e => .inv (ValExpr.seal k e)
    | .svds e => .svds (ValExpr.seal k e)
    | .gsvdS e a b => .gsvdS (ValExpr.seal k e) (ValExpr.seal k a) (ValExpr.seal k b)
    | .gsvdU e a b => .gsvdU (ValExpr.seal k e) (ValExpr.seal k a) (ValExpr.seal k b)
    | .gsvdUI e a b => .gsvdUI (ValExpr.seal k e) (ValExpr.seal k a) (ValExpr.seal k b)
    | .gsvdV e a b => .gsvdV (ValExpr.seal k e) (ValExpr.seal k a) (ValExpr.seal k b)
    | .gsvdVI e a b => .gsvdVI (ValExpr.seal k e) (ValExpr.seal k a) (ValExpr.seal k b)
    | .gpinv e a b => .gpinv (ValExpr.seal k e) (ValExpr.seal k a) (ValExpr.seal k b)
  def ValExpr.sealList (k : Nat) : List ValExpr → List ValExpr
    | [] => []
    | e :: es => (ValExpr.seal k e) :: (ValExpr.sealList k es)
end

mutual
  theorem ValSpace.seal_eq_of_bmax (k : Nat) : ∀ v : ValSpace,
      ValRaise.bmaxSpace v < k → ValSpace.seal k v = v
    | .empty, h => by
        rfl
    | .real, h => by
        rfl
    | .dsum s0 s1, h => by
        simp only [ValRaise.bmaxSpace, Nat.max_lt] at h
        simp only [ValSpace.seal, ValSpace.seal_eq_of_bmax k s0 (by omega), ValSpace.seal_eq_of_bmax k s1 (by omega)]
    | .tprod s0 s1, h => by
        simp only [ValRaise.bmaxSpace, Nat.max_lt] at h
        simp only [ValSpace.seal, ValSpace.seal_eq_of_bmax k s0 (by omega), ValSpace.seal_eq_of_bmax k s1 (by omega)]
    | .ffs p s e, h => by
        simp only [ValRaise.bmaxSpace, Nat.max_lt] at h
        simp only [ValSpace.seal, ValSpace.seal_eq_of_bmax k s (by omega), ValExpr.seal_eq_of_bmax k e (by omega)]
  theorem ValTy.seal_eq_of_bmax (k : Nat) : ∀ v : ValTy,
      ValRaise.bmaxTy v < k → ValTy.seal k v = v
    | .space s, h => by
        simp only [ValRaise.bmaxTy, Nat.max_lt] at h
        simp only [ValTy.seal, ValSpace.seal_eq_of_bmax k s (by omega)]
    | .piTy t0 t1, h => by
        simp only [ValRaise.bmaxTy, Nat.max_lt] at h
        simp only [ValTy.seal, ValTy.seal_eq_of_bmax k t0 (by omega), ValTy.seal_eq_of_bmax (k + 1) t1 (by omega)]
  theorem ValExpr.seal_eq_of_bmax (k : Nat) : ∀ v : ValExpr,
      ValRaise.bmaxExpr v < k → ValExpr.seal k v = v
    | .bvar i, h => by
        have hi : i < k := h
        simp [ValExpr.seal, Nat.not_le_of_lt hi]
    | .var y t, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValTy.seal_eq_of_bmax k t (by omega)]
    | .vlam t0 t1 e, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValTy.seal_eq_of_bmax k t0 (by omega), ValTy.seal_eq_of_bmax (k + 1) t1 (by omega), ValExpr.seal_eq_of_bmax (k + 1) e (by omega)]
    | .zero s, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValSpace.seal_eq_of_bmax k s (by omega)]
    | .rlit r, h => by
        rfl
    | .scale e0 e1, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e0 (by omega), ValExpr.seal_eq_of_bmax k e1 (by omega)]
    | .dsumE e0 e1, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e0 (by omega), ValExpr.seal_eq_of_bmax k e1 (by omega)]
    | .tprodE e0 e1, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e0 (by omega), ValExpr.seal_eq_of_bmax k e1 (by omega)]
    | .appV e0 e1, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e0 (by omega), ValExpr.seal_eq_of_bmax k e1 (by omega)]
    | .vkrn e0 e1, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e0 (by omega), ValExpr.seal_eq_of_bmax k e1 (by omega)]
    | .vblk e0 e1, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e0 (by omega), ValExpr.seal_eq_of_bmax k e1 (by omega)]
    | .rrefRep e0 e1, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e0 (by omega), ValExpr.seal_eq_of_bmax k e1 (by omega)]
    | .vadd s e0 e1, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValSpace.seal_eq_of_bmax k s (by omega), ValExpr.seal_eq_of_bmax k e0 (by omega), ValExpr.seal_eq_of_bmax k e1 (by omega)]
    | .delta i s, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValSpace.seal_eq_of_bmax k s (by omega)]
    | .idelta s, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValSpace.seal_eq_of_bmax k s (by omega)]
    | .vsum s es, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValSpace.seal_eq_of_bmax k s (by omega), ValExpr.seal_eq_of_bmaxList k es (by omega)]
    | .ttv s e0 e1, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValSpace.seal_eq_of_bmax k s (by omega), ValExpr.seal_eq_of_bmax k e0 (by omega), ValExpr.seal_eq_of_bmax k e1 (by omega)]
    | .mtm i j s0 s1 e0 e1, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValSpace.seal_eq_of_bmax k s0 (by omega), ValSpace.seal_eq_of_bmax k s1 (by omega), ValExpr.seal_eq_of_bmax k e0 (by omega), ValExpr.seal_eq_of_bmax k e1 (by omega)]
    | .reshap e t t0, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega), ValTy.seal_eq_of_bmax k t (by omega), ValTy.seal_eq_of_bmax k t0 (by omega)]
    | .vtrans e, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega)]
    | .pinv e, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega)]
    | .inv e, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega)]
    | .svds e, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega)]
    | .gsvdS e a b, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega), ValExpr.seal_eq_of_bmax k a (by omega), ValExpr.seal_eq_of_bmax k b (by omega)]
    | .gsvdU e a b, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega), ValExpr.seal_eq_of_bmax k a (by omega), ValExpr.seal_eq_of_bmax k b (by omega)]
    | .gsvdUI e a b, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega), ValExpr.seal_eq_of_bmax k a (by omega), ValExpr.seal_eq_of_bmax k b (by omega)]
    | .gsvdV e a b, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega), ValExpr.seal_eq_of_bmax k a (by omega), ValExpr.seal_eq_of_bmax k b (by omega)]
    | .gsvdVI e a b, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega), ValExpr.seal_eq_of_bmax k a (by omega), ValExpr.seal_eq_of_bmax k b (by omega)]
    | .gpinv e a b, h => by
        simp only [ValRaise.bmaxExpr, Nat.max_lt] at h
        simp only [ValExpr.seal, ValExpr.seal_eq_of_bmax k e (by omega), ValExpr.seal_eq_of_bmax k a (by omega), ValExpr.seal_eq_of_bmax k b (by omega)]
  theorem ValExpr.seal_eq_of_bmaxList (k : Nat) : ∀ v : List ValExpr,
      ValRaise.bmaxExprList v < k → ValExpr.sealList k v = v
    | [], h => by
        rfl
    | e :: es, h => by
        simp only [ValRaise.bmaxExprList, Nat.max_lt] at h
        simp only [ValExpr.sealList, ValExpr.seal_eq_of_bmax k e (by omega), ValExpr.seal_eq_of_bmaxList k es (by omega)]
end

mutual
  theorem ValSpace.seal_open (k : Nat) : ∀ v : ValSpace,
      ValSpace.seal (k + 1) (ValSpace.openRec k (.rlit 0) v) = ValSpace.seal k v
    | .empty => by
        rfl
    | .real => by
        rfl
    | .dsum s0 s1 => by
        simp only [ValSpace.seal, ValSpace.openRec, ValSpace.seal_open k s0, ValSpace.seal_open k s1]
    | .tprod s0 s1 => by
        simp only [ValSpace.seal, ValSpace.openRec, ValSpace.seal_open k s0, ValSpace.seal_open k s1]
    | .ffs p s e => by
        simp only [ValSpace.seal, ValSpace.openRec, ValSpace.seal_open k s, ValExpr.seal_open k e]
  theorem ValTy.seal_open (k : Nat) : ∀ v : ValTy,
      ValTy.seal (k + 1) (ValTy.openRec k (.rlit 0) v) = ValTy.seal k v
    | .space s => by
        simp only [ValTy.seal, ValTy.openRec, ValSpace.seal_open k s]
    | .piTy t0 t1 => by
        simp only [ValTy.seal, ValTy.openRec, ValTy.seal_open k t0, ValTy.seal_open (k + 1) t1]
  theorem ValExpr.seal_open (k : Nat) : ∀ v : ValExpr,
      ValExpr.seal (k + 1) (ValExpr.openRec k (.rlit 0) v) = ValExpr.seal k v
    | .bvar i => by
        simp only [ValExpr.seal, ValExpr.openRec]
        split_ifs <;> simp_all [ValExpr.seal] <;> omega
    | .var y t => by
        simp only [ValExpr.seal, ValExpr.openRec, ValTy.seal_open k t]
    | .vlam t0 t1 e => by
        simp only [ValExpr.seal, ValExpr.openRec, ValTy.seal_open k t0, ValTy.seal_open (k + 1) t1, ValExpr.seal_open (k + 1) e]
    | .zero s => by
        simp only [ValExpr.seal, ValExpr.openRec, ValSpace.seal_open k s]
    | .rlit r => by
        rfl
    | .scale e0 e1 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e0, ValExpr.seal_open k e1]
    | .dsumE e0 e1 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e0, ValExpr.seal_open k e1]
    | .tprodE e0 e1 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e0, ValExpr.seal_open k e1]
    | .appV e0 e1 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e0, ValExpr.seal_open k e1]
    | .vkrn e0 e1 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e0, ValExpr.seal_open k e1]
    | .vblk e0 e1 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e0, ValExpr.seal_open k e1]
    | .rrefRep e0 e1 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e0, ValExpr.seal_open k e1]
    | .vadd s e0 e1 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValSpace.seal_open k s, ValExpr.seal_open k e0, ValExpr.seal_open k e1]
    | .delta i s => by
        simp only [ValExpr.seal, ValExpr.openRec, ValSpace.seal_open k s]
    | .idelta s => by
        simp only [ValExpr.seal, ValExpr.openRec, ValSpace.seal_open k s]
    | .vsum s es => by
        simp only [ValExpr.seal, ValExpr.openRec, ValSpace.seal_open k s, ValExpr.seal_openList k es]
    | .ttv s e0 e1 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValSpace.seal_open k s, ValExpr.seal_open k e0, ValExpr.seal_open k e1]
    | .mtm i j s0 s1 e0 e1 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValSpace.seal_open k s0, ValSpace.seal_open k s1, ValExpr.seal_open k e0, ValExpr.seal_open k e1]
    | .reshap e t t0 => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e, ValTy.seal_open k t, ValTy.seal_open k t0]
    | .vtrans e => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e]
    | .pinv e => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e]
    | .inv e => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e]
    | .svds e => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e]
    | .gsvdS e a b => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e, ValExpr.seal_open k a, ValExpr.seal_open k b]
    | .gsvdU e a b => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e, ValExpr.seal_open k a, ValExpr.seal_open k b]
    | .gsvdUI e a b => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e, ValExpr.seal_open k a, ValExpr.seal_open k b]
    | .gsvdV e a b => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e, ValExpr.seal_open k a, ValExpr.seal_open k b]
    | .gsvdVI e a b => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e, ValExpr.seal_open k a, ValExpr.seal_open k b]
    | .gpinv e a b => by
        simp only [ValExpr.seal, ValExpr.openRec, ValExpr.seal_open k e, ValExpr.seal_open k a, ValExpr.seal_open k b]
  theorem ValExpr.seal_openList (k : Nat) : ∀ v : List ValExpr,
      ValExpr.sealList (k + 1) (ValExpr.openRecList k (.rlit 0) v) = ValExpr.sealList k v
    | [] => by
        rfl
    | e :: es => by
        simp only [ValExpr.sealList, ValExpr.openRecList, ValExpr.seal_open k e, ValExpr.seal_openList k es]
end

mutual
  theorem ValSpace.seal_raise (n k : Nat) : ∀ v : ValSpace,
      ValSpace.seal (k + n) (ValSpace.raise n k v) = ValSpace.seal k v
    | .empty => by
        rfl
    | .real => by
        rfl
    | .dsum s0 s1 => by
        simp only [ValSpace.seal, ValSpace.raise, ValSpace.seal_raise n k s0, ValSpace.seal_raise n k s1]
    | .tprod s0 s1 => by
        simp only [ValSpace.seal, ValSpace.raise, ValSpace.seal_raise n k s0, ValSpace.seal_raise n k s1]
    | .ffs p s e => by
        simp only [ValSpace.seal, ValSpace.raise, ValSpace.seal_raise n k s, ValExpr.seal_raise n k e]
  theorem ValTy.seal_raise (n k : Nat) : ∀ v : ValTy,
      ValTy.seal (k + n) (ValTy.raise n k v) = ValTy.seal k v
    | .space s => by
        simp only [ValTy.seal, ValTy.raise, ValSpace.seal_raise n k s]
    | .piTy t0 t1 => by
        simp only [ValTy.raise, ValTy.seal]
        rw [show k + n + 1 = (k + 1) + n by omega,
          ValTy.seal_raise n k t0, ValTy.seal_raise n (k + 1) t1]
  theorem ValExpr.seal_raise (n k : Nat) : ∀ v : ValExpr,
      ValExpr.seal (k + n) (ValExpr.raise n k v) = ValExpr.seal k v
    | .bvar i => by
        simp only [ValExpr.seal, ValExpr.raise]
        split_ifs <;> simp_all [ValExpr.seal] <;> omega
    | .var y t => by
        simp only [ValExpr.seal, ValExpr.raise, ValTy.seal_raise n k t]
    | .vlam t0 t1 e => by
        simp only [ValExpr.raise, ValExpr.seal]
        rw [show k + n + 1 = (k + 1) + n by omega,
          ValTy.seal_raise n k t0, ValTy.seal_raise n (k + 1) t1,
          ValExpr.seal_raise n (k + 1) e]
    | .zero s => by
        simp only [ValExpr.seal, ValExpr.raise, ValSpace.seal_raise n k s]
    | .rlit r => by
        rfl
    | .scale e0 e1 => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e0, ValExpr.seal_raise n k e1]
    | .dsumE e0 e1 => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e0, ValExpr.seal_raise n k e1]
    | .tprodE e0 e1 => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e0, ValExpr.seal_raise n k e1]
    | .appV e0 e1 => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e0, ValExpr.seal_raise n k e1]
    | .vkrn e0 e1 => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e0, ValExpr.seal_raise n k e1]
    | .vblk e0 e1 => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e0, ValExpr.seal_raise n k e1]
    | .rrefRep e0 e1 => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e0, ValExpr.seal_raise n k e1]
    | .vadd s e0 e1 => by
        simp only [ValExpr.seal, ValExpr.raise, ValSpace.seal_raise n k s, ValExpr.seal_raise n k e0, ValExpr.seal_raise n k e1]
    | .delta i s => by
        simp only [ValExpr.seal, ValExpr.raise, ValSpace.seal_raise n k s]
    | .idelta s => by
        simp only [ValExpr.seal, ValExpr.raise, ValSpace.seal_raise n k s]
    | .vsum s es => by
        simp only [ValExpr.seal, ValExpr.raise, ValSpace.seal_raise n k s, ValExpr.seal_raiseList n k es]
    | .ttv s e0 e1 => by
        simp only [ValExpr.seal, ValExpr.raise, ValSpace.seal_raise n k s, ValExpr.seal_raise n k e0, ValExpr.seal_raise n k e1]
    | .mtm i j s0 s1 e0 e1 => by
        simp only [ValExpr.seal, ValExpr.raise, ValSpace.seal_raise n k s0, ValSpace.seal_raise n k s1, ValExpr.seal_raise n k e0, ValExpr.seal_raise n k e1]
    | .reshap e t t0 => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e, ValTy.seal_raise n k t, ValTy.seal_raise n k t0]
    | .vtrans e => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e]
    | .pinv e => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e]
    | .inv e => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e]
    | .svds e => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e]
    | .gsvdS e a b => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e, ValExpr.seal_raise n k a, ValExpr.seal_raise n k b]
    | .gsvdU e a b => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e, ValExpr.seal_raise n k a, ValExpr.seal_raise n k b]
    | .gsvdUI e a b => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e, ValExpr.seal_raise n k a, ValExpr.seal_raise n k b]
    | .gsvdV e a b => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e, ValExpr.seal_raise n k a, ValExpr.seal_raise n k b]
    | .gsvdVI e a b => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e, ValExpr.seal_raise n k a, ValExpr.seal_raise n k b]
    | .gpinv e a b => by
        simp only [ValExpr.seal, ValExpr.raise, ValExpr.seal_raise n k e, ValExpr.seal_raise n k a, ValExpr.seal_raise n k b]
  theorem ValExpr.seal_raiseList (n k : Nat) : ∀ v : List ValExpr,
      ValExpr.sealList (k + n) (ValExpr.raiseList n k v) = ValExpr.sealList k v
    | [] => by
        rfl
    | e :: es => by
        simp only [ValExpr.sealList, ValExpr.raiseList, ValExpr.seal_raise n k e, ValExpr.seal_raiseList n k es]
end

mutual
  theorem ValSpace.seal_substBound (k : Nat) (u : ValExpr) : ∀ v : ValSpace,
      ValSpace.seal k (ValSpace.substBound k u v) =
        ValSpace.openRec k (ValExpr.seal 0 u) (ValSpace.seal (k + 1) v)
    | .empty => by
        rfl
    | .real => by
        rfl
    | .dsum s0 s1 => by
        simp only [ValSpace.seal, ValSpace.substBound, ValSpace.openRec, ValSpace.seal_substBound k u s0, ValSpace.seal_substBound k u s1]
    | .tprod s0 s1 => by
        simp only [ValSpace.seal, ValSpace.substBound, ValSpace.openRec, ValSpace.seal_substBound k u s0, ValSpace.seal_substBound k u s1]
    | .ffs p s e => by
        simp only [ValSpace.seal, ValSpace.substBound, ValSpace.openRec, ValSpace.seal_substBound k u s, ValExpr.seal_substBound k u e]
  theorem ValTy.seal_substBound (k : Nat) (u : ValExpr) : ∀ v : ValTy,
      ValTy.seal k (ValTy.substBound k u v) =
        ValTy.openRec k (ValExpr.seal 0 u) (ValTy.seal (k + 1) v)
    | .space s => by
        simp only [ValTy.seal, ValTy.substBound, ValTy.openRec, ValSpace.seal_substBound k u s]
    | .piTy t0 t1 => by
        simp only [ValTy.seal, ValTy.substBound, ValTy.openRec, ValTy.seal_substBound k u t0, ValTy.seal_substBound (k + 1) u t1]
  theorem ValExpr.seal_substBound (k : Nat) (u : ValExpr) : ∀ v : ValExpr,
      ValExpr.seal k (ValExpr.substBound k u v) =
        ValExpr.openRec k (ValExpr.seal 0 u) (ValExpr.seal (k + 1) v)
    | .bvar i => by
        by_cases hi : i = k
        · subst i
          simp [ValExpr.substBound, ValExpr.seal, ValExpr.openRec,
            show ValExpr.seal k (ValExpr.raise k 0 u) = ValExpr.seal 0 u from
              (by simpa only [Nat.zero_add] using ValExpr.seal_raise k 0 u)]
        · by_cases hki : k < i
          · have hk1 : k + 1 ≤ i := by omega
            have hkm : k ≤ i - 1 := by omega
            simp [ValExpr.substBound, ValExpr.seal, ValExpr.openRec, hi, hki, hk1, hkm]
          · have hk1 : ¬ k + 1 ≤ i := by omega
            have hkm : ¬ k ≤ i := by omega
            simp [ValExpr.substBound, ValExpr.seal, ValExpr.openRec, hi, hki, hk1, hkm]
    | .var y t => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValTy.seal_substBound k u t]
    | .vlam t0 t1 e => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValTy.seal_substBound k u t0, ValTy.seal_substBound (k + 1) u t1, ValExpr.seal_substBound (k + 1) u e]
    | .zero s => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValSpace.seal_substBound k u s]
    | .rlit r => by
        rfl
    | .scale e0 e1 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e0, ValExpr.seal_substBound k u e1]
    | .dsumE e0 e1 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e0, ValExpr.seal_substBound k u e1]
    | .tprodE e0 e1 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e0, ValExpr.seal_substBound k u e1]
    | .appV e0 e1 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e0, ValExpr.seal_substBound k u e1]
    | .vkrn e0 e1 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e0, ValExpr.seal_substBound k u e1]
    | .vblk e0 e1 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e0, ValExpr.seal_substBound k u e1]
    | .rrefRep e0 e1 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e0, ValExpr.seal_substBound k u e1]
    | .vadd s e0 e1 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValSpace.seal_substBound k u s, ValExpr.seal_substBound k u e0, ValExpr.seal_substBound k u e1]
    | .delta i s => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValSpace.seal_substBound k u s]
    | .idelta s => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValSpace.seal_substBound k u s]
    | .vsum s es => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValSpace.seal_substBound k u s, ValExpr.seal_substBoundList k u es]
    | .ttv s e0 e1 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValSpace.seal_substBound k u s, ValExpr.seal_substBound k u e0, ValExpr.seal_substBound k u e1]
    | .mtm i j s0 s1 e0 e1 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValSpace.seal_substBound k u s0, ValSpace.seal_substBound k u s1, ValExpr.seal_substBound k u e0, ValExpr.seal_substBound k u e1]
    | .reshap e t t0 => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e, ValTy.seal_substBound k u t, ValTy.seal_substBound k u t0]
    | .vtrans e => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e]
    | .pinv e => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e]
    | .inv e => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e]
    | .svds e => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e]
    | .gsvdS e a b => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e, ValExpr.seal_substBound k u a, ValExpr.seal_substBound k u b]
    | .gsvdU e a b => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e, ValExpr.seal_substBound k u a, ValExpr.seal_substBound k u b]
    | .gsvdUI e a b => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e, ValExpr.seal_substBound k u a, ValExpr.seal_substBound k u b]
    | .gsvdV e a b => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e, ValExpr.seal_substBound k u a, ValExpr.seal_substBound k u b]
    | .gsvdVI e a b => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e, ValExpr.seal_substBound k u a, ValExpr.seal_substBound k u b]
    | .gpinv e a b => by
        simp only [ValExpr.seal, ValExpr.substBound, ValExpr.openRec, ValExpr.seal_substBound k u e, ValExpr.seal_substBound k u a, ValExpr.seal_substBound k u b]
  theorem ValExpr.seal_substBoundList (k : Nat) (u : ValExpr) : ∀ v : List ValExpr,
      ValExpr.sealList k (ValExpr.substBoundList k u v) =
        ValExpr.openRecList k (ValExpr.seal 0 u) (ValExpr.sealList (k + 1) v)
    | [] => by
        rfl
    | e :: es => by
        simp only [ValExpr.sealList, ValExpr.substBoundList, ValExpr.openRecList, ValExpr.seal_substBound k u e, ValExpr.seal_substBoundList k u es]
end

theorem ValRaise.oracle_seal_bounded (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc] (p : ValFFSProp) :
    ∀ (steps k : Nat) (s : ValSpace) (e : ValExpr),
      bmaxSpace s < k + steps → bmaxExpr e < k + steps →
      orc p (ValSpace.seal k s) (ValExpr.seal k e) = orc p s e
  | 0, k, s, e, hs, he => by
      simpa only [Nat.add_zero] using
        (show orc p (ValSpace.seal k s) (ValExpr.seal k e) = orc p s e by
          rw [ValSpace.seal_eq_of_bmax k s (by omega),
            ValExpr.seal_eq_of_bmax k e (by omega)])
  | steps + 1, k, s, e, hs, he => by
      rw [← ValSpace.seal_open k s, ← ValExpr.seal_open k e]
      calc
        _ = orc p (ValSpace.openRec k (.rlit 0) s) (ValExpr.openRec k (.rlit 0) e) :=
          oracle_seal_bounded orc p steps (k + 1) _ _
            (by have := bmax_open_space_le k s; dsimp [dummy] at this; omega)
            (by have := bmax_open_expr_le k e; dsimp [dummy] at this; omega)
        _ = orc p s e := FFSOracle.openRec_respect orc k (.rlit 0) p s e

theorem ValRaise.oracle_seal (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (p : ValFFSProp) (k : Nat) (s : ValSpace) (e : ValExpr) :
    orc p (ValSpace.seal k s) (ValExpr.seal k e) = orc p s e := by
  apply oracle_seal_bounded orc p (max (bmaxSpace s) (bmaxExpr e) + 1) k s e <;> omega

/-- Dependent substitution needs no additional oracle law. -/
theorem FFSOracle.substBound_respect (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (p : ValFFSProp) (k : Nat) (u : ValExpr) (s : ValSpace) (e : ValExpr) :
    orc p (ValSpace.substBound k u s) (ValExpr.substBound k u e) = orc p s e := by
  rw [← ValRaise.oracle_seal orc p k (ValSpace.substBound k u s) (ValExpr.substBound k u e),
    ValSpace.seal_substBound, ValExpr.seal_substBound,
    FFSOracle.openRec_respect orc k (ValExpr.seal 0 u) p,
    ValRaise.oracle_seal orc p (k + 1)]

/-- Bound substitution preserves the space skeleton under the existing oracle laws. -/
theorem ValSpace.skel_substBound (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (k : Nat) (u : ValExpr) : ∀ s : ValSpace,
    ValSpace.skel orc (ValSpace.substBound k u s) = ValSpace.skel orc s
  | .empty => rfl
  | .real => rfl
  | .dsum a b => by simp only [ValSpace.substBound, ValSpace.skel,
      skel_substBound orc k u a, skel_substBound orc k u b]
  | .tprod a b => by simp only [ValSpace.substBound, ValSpace.skel,
      skel_substBound orc k u a, skel_substBound orc k u b]
  | .ffs p s e => by
      simp only [ValSpace.substBound, ValSpace.skel, ValSpace.dof, ValSpace.shpOf_ffs]
      rw [FFSOracle.substBound_respect orc p k u s e]

theorem ValSpace.shapeInBounds_substBound (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc] (k : Nat) (u : ValExpr) (s : ValSpace) (i : Nat) :
    ValSpace.shapeInBounds orc (ValSpace.substBound k u s) i ↔
      ValSpace.shapeInBounds orc s i := by
  rw [ValSpace.shapeInBounds_iff_lt_dof, ValSpace.shapeInBounds_iff_lt_dof,
    ValSpace.SDEq.dof_eq orc (ValSpace.skel_substBound orc k u s)]

end GLang
