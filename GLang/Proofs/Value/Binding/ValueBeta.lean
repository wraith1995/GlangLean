import GLang.Proofs.Value.Binding.ValueScope

/-! Capture-avoiding substitution used by value application and its inferer. -/
namespace GLang

mutual
  theorem ValSpace.substBound_eq_of_raise (k : Nat) (u : ValExpr) : ∀ v : ValSpace,
      ValSpace.raise 1 k v = v → ValSpace.substBound k u v = v
    | .empty, h => by
        rfl
    | .real, h => by
        rfl
    | .dsum s0 s1, h => by
        simp only [ValSpace.raise, ValSpace.dsum.injEq, true_and, and_true] at h
        simp only [ValSpace.substBound, ValSpace.substBound_eq_of_raise k u s0 h.1, ValSpace.substBound_eq_of_raise k u s1 h.2]
    | .tprod s0 s1, h => by
        simp only [ValSpace.raise, ValSpace.tprod.injEq, true_and, and_true] at h
        simp only [ValSpace.substBound, ValSpace.substBound_eq_of_raise k u s0 h.1, ValSpace.substBound_eq_of_raise k u s1 h.2]
    | .ffs p s e, h => by
        simp only [ValSpace.raise, ValSpace.ffs.injEq, true_and, and_true] at h
        simp only [ValSpace.substBound, ValSpace.substBound_eq_of_raise k u s h.1, ValExpr.substBound_eq_of_raise k u e h.2]
  theorem ValTy.substBound_eq_of_raise (k : Nat) (u : ValExpr) : ∀ v : ValTy,
      ValTy.raise 1 k v = v → ValTy.substBound k u v = v
    | .space s, h => by
        simp only [ValTy.raise, ValTy.space.injEq, true_and, and_true] at h
        simp only [ValTy.substBound, ValSpace.substBound_eq_of_raise k u s h]
    | .piTy t0 t1, h => by
        simp only [ValTy.raise, ValTy.piTy.injEq, true_and, and_true] at h
        simp only [ValTy.substBound, ValTy.substBound_eq_of_raise k u t0 h.1, ValTy.substBound_eq_of_raise (k + 1) u t1 h.2]
  theorem ValExpr.substBound_eq_of_raise (k : Nat) (u : ValExpr) : ∀ v : ValExpr,
      ValExpr.raise 1 k v = v → ValExpr.substBound k u v = v
    | .bvar i, h => by
        have hk : ¬ k ≤ i := by
          intro hk
          simp only [ValExpr.raise, if_pos hk, ValExpr.bvar.injEq] at h
          omega
        have hi : i ≠ k := by omega
        have hi2 : ¬ k < i := by omega
        simp [ValExpr.substBound, hi, hi2]
    | .var y t, h => by
        simp only [ValExpr.raise, ValExpr.var.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValTy.substBound_eq_of_raise k u t h]
    | .vlam t0 t1 e, h => by
        simp only [ValExpr.raise, ValExpr.vlam.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValTy.substBound_eq_of_raise k u t0 h.1, ValTy.substBound_eq_of_raise (k + 1) u t1 h.2.1, ValExpr.substBound_eq_of_raise (k + 1) u e h.2.2]
    | .zero s, h => by
        simp only [ValExpr.raise, ValExpr.zero.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValSpace.substBound_eq_of_raise k u s h]
    | .rlit r, h => by
        rfl
    | .scale e0 e1, h => by
        simp only [ValExpr.raise, ValExpr.scale.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e0 h.1, ValExpr.substBound_eq_of_raise k u e1 h.2]
    | .dsumE e0 e1, h => by
        simp only [ValExpr.raise, ValExpr.dsumE.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e0 h.1, ValExpr.substBound_eq_of_raise k u e1 h.2]
    | .tprodE e0 e1, h => by
        simp only [ValExpr.raise, ValExpr.tprodE.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e0 h.1, ValExpr.substBound_eq_of_raise k u e1 h.2]
    | .appV e0 e1, h => by
        simp only [ValExpr.raise, ValExpr.appV.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e0 h.1, ValExpr.substBound_eq_of_raise k u e1 h.2]
    | .vkrn e0 e1, h => by
        simp only [ValExpr.raise, ValExpr.vkrn.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e0 h.1, ValExpr.substBound_eq_of_raise k u e1 h.2]
    | .vblk e0 e1, h => by
        simp only [ValExpr.raise, ValExpr.vblk.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e0 h.1, ValExpr.substBound_eq_of_raise k u e1 h.2]
    | .rrefRep e0 e1, h => by
        simp only [ValExpr.raise, ValExpr.rrefRep.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e0 h.1, ValExpr.substBound_eq_of_raise k u e1 h.2]
    | .vadd s e0 e1, h => by
        simp only [ValExpr.raise, ValExpr.vadd.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValSpace.substBound_eq_of_raise k u s h.1, ValExpr.substBound_eq_of_raise k u e0 h.2.1, ValExpr.substBound_eq_of_raise k u e1 h.2.2]
    | .delta i s, h => by
        simp only [ValExpr.raise, ValExpr.delta.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValSpace.substBound_eq_of_raise k u s h]
    | .idelta s, h => by
        simp only [ValExpr.raise, ValExpr.idelta.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValSpace.substBound_eq_of_raise k u s h]
    | .vsum s es, h => by
        simp only [ValExpr.raise, ValExpr.vsum.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValSpace.substBound_eq_of_raise k u s h.1, ValExpr.substBound_eq_of_raiseList k u es h.2]
    | .ttv s e0 e1, h => by
        simp only [ValExpr.raise, ValExpr.ttv.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValSpace.substBound_eq_of_raise k u s h.1, ValExpr.substBound_eq_of_raise k u e0 h.2.1, ValExpr.substBound_eq_of_raise k u e1 h.2.2]
    | .mtm i j s0 s1 e0 e1, h => by
        simp only [ValExpr.raise, ValExpr.mtm.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValSpace.substBound_eq_of_raise k u s0 h.1, ValSpace.substBound_eq_of_raise k u s1 h.2.1, ValExpr.substBound_eq_of_raise k u e0 h.2.2.1, ValExpr.substBound_eq_of_raise k u e1 h.2.2.2]
    | .reshap e t t0, h => by
        simp only [ValExpr.raise, ValExpr.reshap.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h.1, ValTy.substBound_eq_of_raise k u t h.2.1, ValTy.substBound_eq_of_raise k u t0 h.2.2]
    | .vtrans e, h => by
        simp only [ValExpr.raise, ValExpr.vtrans.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h]
    | .pinv e, h => by
        simp only [ValExpr.raise, ValExpr.pinv.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h]
    | .inv e, h => by
        simp only [ValExpr.raise, ValExpr.inv.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h]
    | .svds e, h => by
        simp only [ValExpr.raise, ValExpr.svds.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h]
    | .gsvdS e a b, h => by
        simp only [ValExpr.raise, ValExpr.gsvdS.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h.1, ValExpr.substBound_eq_of_raise k u a h.2.1, ValExpr.substBound_eq_of_raise k u b h.2.2]
    | .gsvdU e a b, h => by
        simp only [ValExpr.raise, ValExpr.gsvdU.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h.1, ValExpr.substBound_eq_of_raise k u a h.2.1, ValExpr.substBound_eq_of_raise k u b h.2.2]
    | .gsvdUI e a b, h => by
        simp only [ValExpr.raise, ValExpr.gsvdUI.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h.1, ValExpr.substBound_eq_of_raise k u a h.2.1, ValExpr.substBound_eq_of_raise k u b h.2.2]
    | .gsvdV e a b, h => by
        simp only [ValExpr.raise, ValExpr.gsvdV.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h.1, ValExpr.substBound_eq_of_raise k u a h.2.1, ValExpr.substBound_eq_of_raise k u b h.2.2]
    | .gsvdVI e a b, h => by
        simp only [ValExpr.raise, ValExpr.gsvdVI.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h.1, ValExpr.substBound_eq_of_raise k u a h.2.1, ValExpr.substBound_eq_of_raise k u b h.2.2]
    | .gpinv e a b, h => by
        simp only [ValExpr.raise, ValExpr.gpinv.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.substBound_eq_of_raise k u e h.1, ValExpr.substBound_eq_of_raise k u a h.2.1, ValExpr.substBound_eq_of_raise k u b h.2.2]
  theorem ValExpr.substBound_eq_of_raiseList (k : Nat) (u : ValExpr) : ∀ v : List ValExpr,
      ValExpr.raiseList 1 k v = v → ValExpr.substBoundList k u v = v
    | [], h => by
        rfl
    | e :: es, h => by
        simp only [ValExpr.raiseList, List.cons.injEq, true_and, and_true] at h
        simp only [ValExpr.substBoundList, ValExpr.substBound_eq_of_raise k u e h.1, ValExpr.substBound_eq_of_raiseList k u es h.2]
end

mutual
  theorem ValSpace.subst_raise (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValSpace) (n k : Nat),
      ValSpace.subst x u (ValSpace.raise n k v) =
        ValSpace.raise n k (ValSpace.subst x u v)
    | .empty, n, k => by
        rfl
    | .real, n, k => by
        rfl
    | .dsum s0 s1, n, k => by
        simp only [ValSpace.subst, ValSpace.raise, ValSpace.subst_raise x u hu s0 n k, ValSpace.subst_raise x u hu s1 n k]
    | .tprod s0 s1, n, k => by
        simp only [ValSpace.subst, ValSpace.raise, ValSpace.subst_raise x u hu s0 n k, ValSpace.subst_raise x u hu s1 n k]
    | .ffs p s e, n, k => by
        simp only [ValSpace.subst, ValSpace.raise, ValSpace.subst_raise x u hu s n k, ValExpr.subst_raise x u hu e n k]
  theorem ValTy.subst_raise (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValTy) (n k : Nat),
      ValTy.subst x u (ValTy.raise n k v) =
        ValTy.raise n k (ValTy.subst x u v)
    | .space s, n, k => by
        simp only [ValTy.subst, ValTy.raise, ValSpace.subst_raise x u hu s n k]
    | .piTy t0 t1, n, k => by
        simp only [ValTy.subst, ValTy.raise, ValTy.subst_raise x u hu t0 n k, ValTy.subst_raise x u hu t1 n (k + 1)]
  theorem ValExpr.subst_raise (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValExpr) (n k : Nat),
      ValExpr.subst x u (ValExpr.raise n k v) =
        ValExpr.raise n k (ValExpr.subst x u v)
    | .bvar i, n, k => by
        by_cases hk : k ≤ i <;> simp [ValExpr.subst, ValExpr.raise, hk]
    | .var y t, n, k => by
        by_cases hy : y = x
        · subst y
          simp [ValExpr.subst, ValExpr.raise, DirectOracleOpenPush.raiseExpr_lc hu]
        · simp only [ValExpr.subst, ValExpr.raise, if_neg hy, ValTy.subst_raise x u hu t n k]
    | .vlam t0 t1 e, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValTy.subst_raise x u hu t0 n k, ValTy.subst_raise x u hu t1 n (k + 1), ValExpr.subst_raise x u hu e n (k + 1)]
    | .zero s, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValSpace.subst_raise x u hu s n k]
    | .rlit r, n, k => by
        rfl
    | .scale e0 e1, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e0 n k, ValExpr.subst_raise x u hu e1 n k]
    | .dsumE e0 e1, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e0 n k, ValExpr.subst_raise x u hu e1 n k]
    | .tprodE e0 e1, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e0 n k, ValExpr.subst_raise x u hu e1 n k]
    | .appV e0 e1, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e0 n k, ValExpr.subst_raise x u hu e1 n k]
    | .vkrn e0 e1, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e0 n k, ValExpr.subst_raise x u hu e1 n k]
    | .vblk e0 e1, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e0 n k, ValExpr.subst_raise x u hu e1 n k]
    | .rrefRep e0 e1, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e0 n k, ValExpr.subst_raise x u hu e1 n k]
    | .vadd s e0 e1, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValSpace.subst_raise x u hu s n k, ValExpr.subst_raise x u hu e0 n k, ValExpr.subst_raise x u hu e1 n k]
    | .delta i s, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValSpace.subst_raise x u hu s n k]
    | .idelta s, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValSpace.subst_raise x u hu s n k]
    | .vsum s es, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValSpace.subst_raise x u hu s n k, ValExpr.subst_raiseList x u hu es n k]
    | .ttv s e0 e1, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValSpace.subst_raise x u hu s n k, ValExpr.subst_raise x u hu e0 n k, ValExpr.subst_raise x u hu e1 n k]
    | .mtm i j s0 s1 e0 e1, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValSpace.subst_raise x u hu s0 n k, ValSpace.subst_raise x u hu s1 n k, ValExpr.subst_raise x u hu e0 n k, ValExpr.subst_raise x u hu e1 n k]
    | .reshap e t t0, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k, ValTy.subst_raise x u hu t n k, ValTy.subst_raise x u hu t0 n k]
    | .vtrans e, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k]
    | .pinv e, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k]
    | .inv e, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k]
    | .svds e, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k]
    | .gsvdS e a b, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k, ValExpr.subst_raise x u hu a n k, ValExpr.subst_raise x u hu b n k]
    | .gsvdU e a b, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k, ValExpr.subst_raise x u hu a n k, ValExpr.subst_raise x u hu b n k]
    | .gsvdUI e a b, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k, ValExpr.subst_raise x u hu a n k, ValExpr.subst_raise x u hu b n k]
    | .gsvdV e a b, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k, ValExpr.subst_raise x u hu a n k, ValExpr.subst_raise x u hu b n k]
    | .gsvdVI e a b, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k, ValExpr.subst_raise x u hu a n k, ValExpr.subst_raise x u hu b n k]
    | .gpinv e a b, n, k => by
        simp only [ValExpr.subst, ValExpr.raise, ValExpr.subst_raise x u hu e n k, ValExpr.subst_raise x u hu a n k, ValExpr.subst_raise x u hu b n k]
  theorem ValExpr.subst_raiseList (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : List ValExpr) (n k : Nat),
      ValExpr.substList x u (ValExpr.raiseList n k v) =
        ValExpr.raiseList n k (ValExpr.substList x u v)
    | [], n, k => by
        rfl
    | e :: es, n, k => by
        simp only [ValExpr.substList, ValExpr.raiseList, ValExpr.subst_raise x u hu e n k, ValExpr.subst_raiseList x u hu es n k]
end

mutual
  theorem ValSpace.subst_substBound (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValSpace) (k : Nat) (a : ValExpr),
      ValSpace.subst x u (ValSpace.substBound k a v) =
        ValSpace.substBound k (ValExpr.subst x u a) (ValSpace.subst x u v)
    | .empty, k, arg => by
        rfl
    | .real, k, arg => by
        rfl
    | .dsum s0 s1, k, arg => by
        simp only [ValSpace.subst, ValSpace.substBound, ValSpace.subst_substBound x u hu s0 k arg, ValSpace.subst_substBound x u hu s1 k arg]
    | .tprod s0 s1, k, arg => by
        simp only [ValSpace.subst, ValSpace.substBound, ValSpace.subst_substBound x u hu s0 k arg, ValSpace.subst_substBound x u hu s1 k arg]
    | .ffs p s e, k, arg => by
        simp only [ValSpace.subst, ValSpace.substBound, ValSpace.subst_substBound x u hu s k arg, ValExpr.subst_substBound x u hu e k arg]
  theorem ValTy.subst_substBound (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValTy) (k : Nat) (a : ValExpr),
      ValTy.subst x u (ValTy.substBound k a v) =
        ValTy.substBound k (ValExpr.subst x u a) (ValTy.subst x u v)
    | .space s, k, arg => by
        simp only [ValTy.subst, ValTy.substBound, ValSpace.subst_substBound x u hu s k arg]
    | .piTy t0 t1, k, arg => by
        simp only [ValTy.subst, ValTy.substBound, ValTy.subst_substBound x u hu t0 k arg, ValTy.subst_substBound x u hu t1 (k + 1) arg]
  theorem ValExpr.subst_substBound (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValExpr) (k : Nat) (a : ValExpr),
      ValExpr.subst x u (ValExpr.substBound k a v) =
        ValExpr.substBound k (ValExpr.subst x u a) (ValExpr.subst x u v)
    | .bvar i, k, arg => by
        by_cases hi : i = k
        · simp [ValExpr.substBound, ValExpr.subst, hi, ValExpr.subst_raise x u hu arg k 0]
        · by_cases hik : k < i <;> simp [ValExpr.substBound, ValExpr.subst, hi, hik]
    | .var y t, k, arg => by
        by_cases hy : y = x
        · subst y
          simp only [ValExpr.substBound, ValExpr.subst, if_pos rfl]
          exact (ValExpr.substBound_eq_of_raise k _ u
            (DirectOracleOpenPush.raiseExpr_lc hu 1 k)).symm
        · simp only [ValExpr.subst, ValExpr.substBound, if_neg hy, ValTy.subst_substBound x u hu t k arg]
    | .vlam t0 t1 e, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValTy.subst_substBound x u hu t0 k arg, ValTy.subst_substBound x u hu t1 (k + 1) arg, ValExpr.subst_substBound x u hu e (k + 1) arg]
    | .zero s, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValSpace.subst_substBound x u hu s k arg]
    | .rlit r, k, arg => by
        rfl
    | .scale e0 e1, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e0 k arg, ValExpr.subst_substBound x u hu e1 k arg]
    | .dsumE e0 e1, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e0 k arg, ValExpr.subst_substBound x u hu e1 k arg]
    | .tprodE e0 e1, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e0 k arg, ValExpr.subst_substBound x u hu e1 k arg]
    | .appV e0 e1, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e0 k arg, ValExpr.subst_substBound x u hu e1 k arg]
    | .vkrn e0 e1, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e0 k arg, ValExpr.subst_substBound x u hu e1 k arg]
    | .vblk e0 e1, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e0 k arg, ValExpr.subst_substBound x u hu e1 k arg]
    | .rrefRep e0 e1, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e0 k arg, ValExpr.subst_substBound x u hu e1 k arg]
    | .vadd s e0 e1, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValSpace.subst_substBound x u hu s k arg, ValExpr.subst_substBound x u hu e0 k arg, ValExpr.subst_substBound x u hu e1 k arg]
    | .delta i s, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValSpace.subst_substBound x u hu s k arg]
    | .idelta s, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValSpace.subst_substBound x u hu s k arg]
    | .vsum s es, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValSpace.subst_substBound x u hu s k arg, ValExpr.subst_substBoundList x u hu es k arg]
    | .ttv s e0 e1, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValSpace.subst_substBound x u hu s k arg, ValExpr.subst_substBound x u hu e0 k arg, ValExpr.subst_substBound x u hu e1 k arg]
    | .mtm i j s0 s1 e0 e1, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValSpace.subst_substBound x u hu s0 k arg, ValSpace.subst_substBound x u hu s1 k arg, ValExpr.subst_substBound x u hu e0 k arg, ValExpr.subst_substBound x u hu e1 k arg]
    | .reshap e t t0, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg, ValTy.subst_substBound x u hu t k arg, ValTy.subst_substBound x u hu t0 k arg]
    | .vtrans e, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg]
    | .pinv e, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg]
    | .inv e, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg]
    | .svds e, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg]
    | .gsvdS e a b, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg, ValExpr.subst_substBound x u hu a k arg, ValExpr.subst_substBound x u hu b k arg]
    | .gsvdU e a b, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg, ValExpr.subst_substBound x u hu a k arg, ValExpr.subst_substBound x u hu b k arg]
    | .gsvdUI e a b, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg, ValExpr.subst_substBound x u hu a k arg, ValExpr.subst_substBound x u hu b k arg]
    | .gsvdV e a b, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg, ValExpr.subst_substBound x u hu a k arg, ValExpr.subst_substBound x u hu b k arg]
    | .gsvdVI e a b, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg, ValExpr.subst_substBound x u hu a k arg, ValExpr.subst_substBound x u hu b k arg]
    | .gpinv e a b, k, arg => by
        simp only [ValExpr.subst, ValExpr.substBound, ValExpr.subst_substBound x u hu e k arg, ValExpr.subst_substBound x u hu a k arg, ValExpr.subst_substBound x u hu b k arg]
  theorem ValExpr.subst_substBoundList (x : VName) (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : List ValExpr) (k : Nat) (a : ValExpr),
      ValExpr.substList x u (ValExpr.substBoundList k a v) =
        ValExpr.substBoundList k (ValExpr.subst x u a) (ValExpr.substList x u v)
    | [], k, arg => by
        rfl
    | e :: es, k, arg => by
        simp only [ValExpr.substList, ValExpr.substBoundList, ValExpr.subst_substBound x u hu e k arg, ValExpr.subst_substBoundList x u hu es k arg]
end

/-- Free-variable substitution commutes with the dependent application result. -/
theorem ValTy.subst_applyCodomain (x : VName) (u : ValExpr) (hu : ValExpr.lc u)
    (a : ValExpr) (c : ValTy) :
    ValTy.subst x u (ValTy.applyCodomain a c) =
      ValTy.applyCodomain (ValExpr.subst x u a) (ValTy.subst x u c) :=
  ValTy.subst_substBound x u hu c 0 a

mutual
  theorem ValSpace.openRec_substBound (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValSpace) (j k : Nat) (a : ValExpr), j ≤ k →
      ValSpace.openRec k u (ValSpace.substBound j a v) =
        ValSpace.substBound j (ValExpr.openRec (k - j) u a) (ValSpace.openRec (k + 1) u v)
    | .empty, j, k, arg, hjk => by
        simp only [ValSpace.openRec, ValSpace.substBound, Nat.add_sub_add_right]
    | .real, j, k, arg, hjk => by
        simp only [ValSpace.openRec, ValSpace.substBound, Nat.add_sub_add_right]
    | .dsum s0 s1, j, k, arg, hjk => by
        simp only [ValSpace.openRec, ValSpace.substBound, ValSpace.openRec_substBound u hu s0 j k arg hjk, ValSpace.openRec_substBound u hu s1 j k arg hjk, Nat.add_sub_add_right]
    | .tprod s0 s1, j, k, arg, hjk => by
        simp only [ValSpace.openRec, ValSpace.substBound, ValSpace.openRec_substBound u hu s0 j k arg hjk, ValSpace.openRec_substBound u hu s1 j k arg hjk, Nat.add_sub_add_right]
    | .ffs p s e, j, k, arg, hjk => by
        simp only [ValSpace.openRec, ValSpace.substBound, ValSpace.openRec_substBound u hu s j k arg hjk, ValExpr.openRec_substBound u hu e j k arg hjk, Nat.add_sub_add_right]
  theorem ValTy.openRec_substBound (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValTy) (j k : Nat) (a : ValExpr), j ≤ k →
      ValTy.openRec k u (ValTy.substBound j a v) =
        ValTy.substBound j (ValExpr.openRec (k - j) u a) (ValTy.openRec (k + 1) u v)
    | .space s, j, k, arg, hjk => by
        simp only [ValTy.openRec, ValTy.substBound, ValSpace.openRec_substBound u hu s j k arg hjk, Nat.add_sub_add_right]
    | .piTy t0 t1, j, k, arg, hjk => by
        simp only [ValTy.openRec, ValTy.substBound, ValTy.openRec_substBound u hu t0 j k arg hjk, ValTy.openRec_substBound u hu t1 (j + 1) (k + 1) arg (by omega), Nat.add_sub_add_right]
  theorem ValExpr.openRec_substBound (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValExpr) (j k : Nat) (a : ValExpr), j ≤ k →
      ValExpr.openRec k u (ValExpr.substBound j a v) =
        ValExpr.substBound j (ValExpr.openRec (k - j) u a) (ValExpr.openRec (k + 1) u v)
    | .bvar i, j, k, arg, hjk => by
        by_cases hij : i = j
        · subst i
          have hne : j ≠ k + 1 := by omega
          have hr := DirectOracleOpenPush.raiseExpr_openRec j 0 (k - j) u
            (DirectOracleOpenPush.raiseStableExpr_of_lc hu) (Nat.zero_le _) arg
          simpa [ValExpr.substBound, ValExpr.openRec, hne, Nat.sub_add_cancel hjk] using hr.symm
        · by_cases hik : i = k + 1
          · subst i
            have hji : j < k + 1 := by omega
            simp only [ValExpr.substBound, if_neg hij, if_pos hji, Nat.add_sub_cancel,
              ValExpr.openRec, if_pos rfl]
            exact (ValExpr.substBound_eq_of_raise j _ u
              (DirectOracleOpenPush.raiseExpr_lc hu 1 j)).symm
          · by_cases hji : j < i
            · have hne : i - 1 ≠ k := by omega
              simp [ValExpr.substBound, ValExpr.openRec, hij, hik, hji, hne]
            · have hik0 : i ≠ k := by omega
              simp [ValExpr.substBound, ValExpr.openRec, hij, hik, hji, hik0]
    | .var y t, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValTy.openRec_substBound u hu t j k arg hjk, Nat.add_sub_add_right]
    | .vlam t0 t1 e, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValTy.openRec_substBound u hu t0 j k arg hjk, ValTy.openRec_substBound u hu t1 (j + 1) (k + 1) arg (by omega), ValExpr.openRec_substBound u hu e (j + 1) (k + 1) arg (by omega), Nat.add_sub_add_right]
    | .zero s, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValSpace.openRec_substBound u hu s j k arg hjk, Nat.add_sub_add_right]
    | .rlit r, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, Nat.add_sub_add_right]
    | .scale e0 e1, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e0 j k arg hjk, ValExpr.openRec_substBound u hu e1 j k arg hjk, Nat.add_sub_add_right]
    | .dsumE e0 e1, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e0 j k arg hjk, ValExpr.openRec_substBound u hu e1 j k arg hjk, Nat.add_sub_add_right]
    | .tprodE e0 e1, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e0 j k arg hjk, ValExpr.openRec_substBound u hu e1 j k arg hjk, Nat.add_sub_add_right]
    | .appV e0 e1, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e0 j k arg hjk, ValExpr.openRec_substBound u hu e1 j k arg hjk, Nat.add_sub_add_right]
    | .vkrn e0 e1, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e0 j k arg hjk, ValExpr.openRec_substBound u hu e1 j k arg hjk, Nat.add_sub_add_right]
    | .vblk e0 e1, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e0 j k arg hjk, ValExpr.openRec_substBound u hu e1 j k arg hjk, Nat.add_sub_add_right]
    | .rrefRep e0 e1, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e0 j k arg hjk, ValExpr.openRec_substBound u hu e1 j k arg hjk, Nat.add_sub_add_right]
    | .vadd s e0 e1, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValSpace.openRec_substBound u hu s j k arg hjk, ValExpr.openRec_substBound u hu e0 j k arg hjk, ValExpr.openRec_substBound u hu e1 j k arg hjk, Nat.add_sub_add_right]
    | .delta i s, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValSpace.openRec_substBound u hu s j k arg hjk, Nat.add_sub_add_right]
    | .idelta s, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValSpace.openRec_substBound u hu s j k arg hjk, Nat.add_sub_add_right]
    | .vsum s es, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValSpace.openRec_substBound u hu s j k arg hjk, ValExpr.openRec_substBoundList u hu es j k arg hjk, Nat.add_sub_add_right]
    | .ttv s e0 e1, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValSpace.openRec_substBound u hu s j k arg hjk, ValExpr.openRec_substBound u hu e0 j k arg hjk, ValExpr.openRec_substBound u hu e1 j k arg hjk, Nat.add_sub_add_right]
    | .mtm n0 n1 s0 s1 e0 e1, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValSpace.openRec_substBound u hu s0 j k arg hjk, ValSpace.openRec_substBound u hu s1 j k arg hjk, ValExpr.openRec_substBound u hu e0 j k arg hjk, ValExpr.openRec_substBound u hu e1 j k arg hjk, Nat.add_sub_add_right]
    | .reshap e t t0, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, ValTy.openRec_substBound u hu t j k arg hjk, ValTy.openRec_substBound u hu t0 j k arg hjk, Nat.add_sub_add_right]
    | .vtrans e, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, Nat.add_sub_add_right]
    | .pinv e, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, Nat.add_sub_add_right]
    | .inv e, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, Nat.add_sub_add_right]
    | .svds e, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, Nat.add_sub_add_right]
    | .gsvdS e a b, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, ValExpr.openRec_substBound u hu a j k arg hjk, ValExpr.openRec_substBound u hu b j k arg hjk, Nat.add_sub_add_right]
    | .gsvdU e a b, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, ValExpr.openRec_substBound u hu a j k arg hjk, ValExpr.openRec_substBound u hu b j k arg hjk, Nat.add_sub_add_right]
    | .gsvdUI e a b, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, ValExpr.openRec_substBound u hu a j k arg hjk, ValExpr.openRec_substBound u hu b j k arg hjk, Nat.add_sub_add_right]
    | .gsvdV e a b, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, ValExpr.openRec_substBound u hu a j k arg hjk, ValExpr.openRec_substBound u hu b j k arg hjk, Nat.add_sub_add_right]
    | .gsvdVI e a b, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, ValExpr.openRec_substBound u hu a j k arg hjk, ValExpr.openRec_substBound u hu b j k arg hjk, Nat.add_sub_add_right]
    | .gpinv e a b, j, k, arg, hjk => by
        simp only [ValExpr.openRec, ValExpr.substBound, ValExpr.openRec_substBound u hu e j k arg hjk, ValExpr.openRec_substBound u hu a j k arg hjk, ValExpr.openRec_substBound u hu b j k arg hjk, Nat.add_sub_add_right]
  theorem ValExpr.openRec_substBoundList (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : List ValExpr) (j k : Nat) (a : ValExpr), j ≤ k →
      ValExpr.openRecList k u (ValExpr.substBoundList j a v) =
        ValExpr.substBoundList j (ValExpr.openRec (k - j) u a) (ValExpr.openRecList (k + 1) u v)
    | [], j, k, arg, hjk => by
        simp only [ValExpr.openRecList, ValExpr.substBoundList, Nat.add_sub_add_right]
    | e :: es, j, k, arg, hjk => by
        simp only [ValExpr.openRecList, ValExpr.substBoundList, ValExpr.openRec_substBound u hu e j k arg hjk, ValExpr.openRec_substBoundList u hu es j k arg hjk, Nat.add_sub_add_right]
end

/-- Opening an outer variable commutes with dependent application substitution. -/
theorem ValTy.openRec_applyCodomain (u : ValExpr) (hu : ValExpr.lc u)
    (c : ValTy) (a : ValExpr) (k : Nat) :
    ValTy.openRec k u (ValTy.applyCodomain a c) =
      ValTy.applyCodomain (ValExpr.openRec k u a) (ValTy.openRec (k + 1) u c) := by
  simpa only [ValTy.applyCodomain, Nat.sub_zero] using
    ValTy.openRec_substBound u hu c 0 k a (Nat.zero_le k)

mutual
  theorem ValSpace.substBound_eq_openRec (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValSpace) (k : Nat), ValSpace.raise 1 (k + 1) v = v →
      ValSpace.substBound k u v = ValSpace.openRec k u v
    | .empty, k, h => by
        rfl
    | .real, k, h => by
        rfl
    | .dsum s0 s1, k, h => by
        simp only [ValSpace.raise, ValSpace.dsum.injEq, true_and, and_true] at h
        simp only [ValSpace.substBound, ValSpace.openRec, ValSpace.substBound_eq_openRec u hu s0 k h.1, ValSpace.substBound_eq_openRec u hu s1 k h.2]
    | .tprod s0 s1, k, h => by
        simp only [ValSpace.raise, ValSpace.tprod.injEq, true_and, and_true] at h
        simp only [ValSpace.substBound, ValSpace.openRec, ValSpace.substBound_eq_openRec u hu s0 k h.1, ValSpace.substBound_eq_openRec u hu s1 k h.2]
    | .ffs p s e, k, h => by
        simp only [ValSpace.raise, ValSpace.ffs.injEq, true_and, and_true] at h
        simp only [ValSpace.substBound, ValSpace.openRec, ValSpace.substBound_eq_openRec u hu s k h.1, ValExpr.substBound_eq_openRec u hu e k h.2]
  theorem ValTy.substBound_eq_openRec (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValTy) (k : Nat), ValTy.raise 1 (k + 1) v = v →
      ValTy.substBound k u v = ValTy.openRec k u v
    | .space s, k, h => by
        simp only [ValTy.raise, ValTy.space.injEq, true_and, and_true] at h
        simp only [ValTy.substBound, ValTy.openRec, ValSpace.substBound_eq_openRec u hu s k h]
    | .piTy t0 t1, k, h => by
        simp only [ValTy.raise, ValTy.piTy.injEq, true_and, and_true] at h
        simp only [ValTy.substBound, ValTy.openRec, ValTy.substBound_eq_openRec u hu t0 k h.1, ValTy.substBound_eq_openRec u hu t1 (k + 1) h.2]
  theorem ValExpr.substBound_eq_openRec (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : ValExpr) (k : Nat), ValExpr.raise 1 (k + 1) v = v →
      ValExpr.substBound k u v = ValExpr.openRec k u v
    | .bvar i, k, h => by
        have hi : i < k + 1 := by
          by_contra hn
          have hg : k + 1 ≤ i := by omega
          simp only [ValExpr.raise, if_pos hg, ValExpr.bvar.injEq] at h
          omega
        by_cases hik : i = k
        · simp [ValExpr.substBound, ValExpr.openRec, hik, DirectOracleOpenPush.raiseExpr_lc hu]
        · have hk : ¬ k < i := by omega
          simp [ValExpr.substBound, ValExpr.openRec, hik, hk]
    | .var y t, k, h => by
        simp only [ValExpr.raise, ValExpr.var.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValTy.substBound_eq_openRec u hu t k h]
    | .vlam t0 t1 e, k, h => by
        simp only [ValExpr.raise, ValExpr.vlam.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValTy.substBound_eq_openRec u hu t0 k h.1, ValTy.substBound_eq_openRec u hu t1 (k + 1) h.2.1, ValExpr.substBound_eq_openRec u hu e (k + 1) h.2.2]
    | .zero s, k, h => by
        simp only [ValExpr.raise, ValExpr.zero.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValSpace.substBound_eq_openRec u hu s k h]
    | .rlit r, k, h => by
        rfl
    | .scale e0 e1, k, h => by
        simp only [ValExpr.raise, ValExpr.scale.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e0 k h.1, ValExpr.substBound_eq_openRec u hu e1 k h.2]
    | .dsumE e0 e1, k, h => by
        simp only [ValExpr.raise, ValExpr.dsumE.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e0 k h.1, ValExpr.substBound_eq_openRec u hu e1 k h.2]
    | .tprodE e0 e1, k, h => by
        simp only [ValExpr.raise, ValExpr.tprodE.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e0 k h.1, ValExpr.substBound_eq_openRec u hu e1 k h.2]
    | .appV e0 e1, k, h => by
        simp only [ValExpr.raise, ValExpr.appV.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e0 k h.1, ValExpr.substBound_eq_openRec u hu e1 k h.2]
    | .vkrn e0 e1, k, h => by
        simp only [ValExpr.raise, ValExpr.vkrn.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e0 k h.1, ValExpr.substBound_eq_openRec u hu e1 k h.2]
    | .vblk e0 e1, k, h => by
        simp only [ValExpr.raise, ValExpr.vblk.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e0 k h.1, ValExpr.substBound_eq_openRec u hu e1 k h.2]
    | .rrefRep e0 e1, k, h => by
        simp only [ValExpr.raise, ValExpr.rrefRep.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e0 k h.1, ValExpr.substBound_eq_openRec u hu e1 k h.2]
    | .vadd s e0 e1, k, h => by
        simp only [ValExpr.raise, ValExpr.vadd.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValSpace.substBound_eq_openRec u hu s k h.1, ValExpr.substBound_eq_openRec u hu e0 k h.2.1, ValExpr.substBound_eq_openRec u hu e1 k h.2.2]
    | .delta i s, k, h => by
        simp only [ValExpr.raise, ValExpr.delta.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValSpace.substBound_eq_openRec u hu s k h]
    | .idelta s, k, h => by
        simp only [ValExpr.raise, ValExpr.idelta.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValSpace.substBound_eq_openRec u hu s k h]
    | .vsum s es, k, h => by
        simp only [ValExpr.raise, ValExpr.vsum.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValSpace.substBound_eq_openRec u hu s k h.1, ValExpr.substBound_eq_openRecList u hu es k h.2]
    | .ttv s e0 e1, k, h => by
        simp only [ValExpr.raise, ValExpr.ttv.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValSpace.substBound_eq_openRec u hu s k h.1, ValExpr.substBound_eq_openRec u hu e0 k h.2.1, ValExpr.substBound_eq_openRec u hu e1 k h.2.2]
    | .mtm i j s0 s1 e0 e1, k, h => by
        simp only [ValExpr.raise, ValExpr.mtm.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValSpace.substBound_eq_openRec u hu s0 k h.1, ValSpace.substBound_eq_openRec u hu s1 k h.2.1, ValExpr.substBound_eq_openRec u hu e0 k h.2.2.1, ValExpr.substBound_eq_openRec u hu e1 k h.2.2.2]
    | .reshap e t t0, k, h => by
        simp only [ValExpr.raise, ValExpr.reshap.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h.1, ValTy.substBound_eq_openRec u hu t k h.2.1, ValTy.substBound_eq_openRec u hu t0 k h.2.2]
    | .vtrans e, k, h => by
        simp only [ValExpr.raise, ValExpr.vtrans.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h]
    | .pinv e, k, h => by
        simp only [ValExpr.raise, ValExpr.pinv.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h]
    | .inv e, k, h => by
        simp only [ValExpr.raise, ValExpr.inv.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h]
    | .svds e, k, h => by
        simp only [ValExpr.raise, ValExpr.svds.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h]
    | .gsvdS e a b, k, h => by
        simp only [ValExpr.raise, ValExpr.gsvdS.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h.1, ValExpr.substBound_eq_openRec u hu a k h.2.1, ValExpr.substBound_eq_openRec u hu b k h.2.2]
    | .gsvdU e a b, k, h => by
        simp only [ValExpr.raise, ValExpr.gsvdU.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h.1, ValExpr.substBound_eq_openRec u hu a k h.2.1, ValExpr.substBound_eq_openRec u hu b k h.2.2]
    | .gsvdUI e a b, k, h => by
        simp only [ValExpr.raise, ValExpr.gsvdUI.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h.1, ValExpr.substBound_eq_openRec u hu a k h.2.1, ValExpr.substBound_eq_openRec u hu b k h.2.2]
    | .gsvdV e a b, k, h => by
        simp only [ValExpr.raise, ValExpr.gsvdV.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h.1, ValExpr.substBound_eq_openRec u hu a k h.2.1, ValExpr.substBound_eq_openRec u hu b k h.2.2]
    | .gsvdVI e a b, k, h => by
        simp only [ValExpr.raise, ValExpr.gsvdVI.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h.1, ValExpr.substBound_eq_openRec u hu a k h.2.1, ValExpr.substBound_eq_openRec u hu b k h.2.2]
    | .gpinv e a b, k, h => by
        simp only [ValExpr.raise, ValExpr.gpinv.injEq, true_and, and_true] at h
        simp only [ValExpr.substBound, ValExpr.openRec, ValExpr.substBound_eq_openRec u hu e k h.1, ValExpr.substBound_eq_openRec u hu a k h.2.1, ValExpr.substBound_eq_openRec u hu b k h.2.2]
  theorem ValExpr.substBound_eq_openRecList (u : ValExpr) (hu : ValExpr.lc u) :
      ∀ (v : List ValExpr) (k : Nat), ValExpr.raiseList 1 (k + 1) v = v →
      ValExpr.substBoundList k u v = ValExpr.openRecList k u v
    | [], k, h => by
        rfl
    | e :: es, k, h => by
        simp only [ValExpr.raiseList, List.cons.injEq, true_and, and_true] at h
        simp only [ValExpr.substBoundList, ValExpr.openRecList, ValExpr.substBound_eq_openRec u hu e k h.1, ValExpr.substBound_eq_openRecList u hu es k h.2]
end

/-! ## `lc_subst` — substitution preserves local-closedness.

The value LN kit had `subst_openRec` (subst/open commutation) but not the
`lc`-preservation lemma itself. `ValSpace.lc`/`ValTy.lc`/`ValExpr.lc` are mutually
inductive, so this is one mutual recursor with three `subst`-statement motives;
the binder arms (`piTy`/`vlam`) commute `subst` past `openVar` via the two
helpers below. -/

/-- `subst` commutes past `openVar` for types (the binder-arm workhorse). -/
theorem ValTy.subst_openVar {x y : VName} {u : ValExpr} {τ₀ τ₁ : ValTy}
    (hyx : y ≠ x) (hu : ValExpr.lc u) :
    ValTy.subst x u (ValTy.openVar y τ₀ τ₁)
      = ValTy.openVar y (ValTy.subst x u τ₀) (ValTy.subst x u τ₁) := by
  rw [ValTy.openVar, ValTy.subst_openRec x u hu τ₁ 0 (.var y τ₀)]
  simp only [ValExpr.subst, if_neg hyx, ValTy.openVar]

/-- `subst` commutes past `openVar` for expressions. -/
theorem ValExpr.subst_openVar {x y : VName} {u : ValExpr} {τ₀ : ValTy} {e : ValExpr}
    (hyx : y ≠ x) (hu : ValExpr.lc u) :
    ValExpr.subst x u (ValExpr.openVar y τ₀ e)
      = ValExpr.openVar y (ValTy.subst x u τ₀) (ValExpr.subst x u e) := by
  rw [ValExpr.openVar, ValExpr.subst_openRec x u hu e 0 (.var y τ₀)]
  simp only [ValExpr.subst, if_neg hyx, ValExpr.openVar]

/-- **Substitution preserves `lc`** (all three categories, jointly via the shared
    mutual recursor). -/
theorem lc_subst_joint :
    (∀ {s : ValSpace}, ValSpace.lc s → ∀ x u, ValExpr.lc u → ValSpace.lc (ValSpace.subst x u s))
  ∧ (∀ {τ : ValTy}, ValTy.lc τ → ∀ x u, ValExpr.lc u → ValTy.lc (ValTy.subst x u τ))
  ∧ (∀ {e : ValExpr}, ValExpr.lc e → ∀ x u, ValExpr.lc u → ValExpr.lc (ValExpr.subst x u e)) := by
  refine ⟨@fun s h => ?_, @fun τ h => ?_, @fun e h => ?_⟩
  all_goals
    exact h.rec
      (motive_1 := fun s _ => ∀ x u, ValExpr.lc u → ValSpace.lc (ValSpace.subst x u s))
      (motive_2 := fun τ _ => ∀ x u, ValExpr.lc u → ValTy.lc (ValTy.subst x u τ))
      (motive_3 := fun e _ => ∀ x u, ValExpr.lc u → ValExpr.lc (ValExpr.subst x u e))
      -- ValSpace
      (by intro _ _ _; exact .empty)
      (by intro _ _ _; exact .real)
      (by intros; rename_i ih₀ ih₁; intro x u hu; exact .dsum (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih₀ ih₁; intro x u hu; exact .tprod (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih_s ih_e; intro x u hu; exact .ffs (ih_s x u hu) (ih_e x u hu))
      -- ValTy
      (by intros; rename_i ih; intro x u hu; exact .space (ih x u hu))
      (by intros; rename_i L hτ₀ hcod ih_τ₀ ih_cod; intro x u hu;
          refine ValTy.lc.piTy (insert x L) (ih_τ₀ x u hu) (fun y hy => ?_)
          simp only [Finset.mem_insert, not_or] at hy
          rw [← ValTy.subst_openVar hy.1 hu]; exact ih_cod y hy.2 x u hu)
      -- ValExpr
      (by intros; rename_i xv _τv _hτ ih_τ; intro x u hu;
          by_cases h : xv = x
          · subst h; simp only [ValExpr.subst, if_pos rfl]; exact hu
          · simp only [ValExpr.subst, if_neg h]; exact .var (ih_τ x u hu))
      (by intros; rename_i L hτ₀ hT he ih_τ₀ ih_T ih_e; intro x u hu;
          refine ValExpr.lc.vlam (insert x L) (ih_τ₀ x u hu) (fun y hy => ?_) (fun y hy => ?_)
          · simp only [Finset.mem_insert, not_or] at hy
            rw [← ValTy.subst_openVar hy.1 hu]; exact ih_T y hy.2 x u hu
          · simp only [Finset.mem_insert, not_or] at hy
            rw [← ValExpr.subst_openVar hy.1 hu]; exact ih_e y hy.2 x u hu)
      (by intros; rename_i ih_s; intro x u hu; exact .zero (ih_s x u hu))
      (by intros; intro x u _; exact .rlit)
      (by intros; rename_i ih₀ ih₁; intro x u hu; exact .scale (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih_s ih₀ ih₁; intro x u hu;
          exact .vadd (ih_s x u hu) (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih₀ ih₁; intro x u hu; exact .dsumE (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih₀ ih₁; intro x u hu; exact .tprodE (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih_s; intro x u hu; exact .delta (ih_s x u hu))
      (by intros; rename_i ih_s; intro x u hu; exact .idelta (ih_s x u hu))
      (by intros; rename_i ih_s ih_es; intro x u hu;
          refine ValExpr.lc.vsum (ih_s x u hu) (fun e' he' => ?_)
          simp only [ValExpr.substList_eq_map, List.mem_map] at he'
          obtain ⟨e, hmem, rfl⟩ := he'
          exact ih_es e hmem x u hu)
      (by intros; rename_i ih_s ih₀ ih₁; intro x u hu; exact .ttv (ih_s x u hu) (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih_s₀ ih_s₁ ih₀ ih₁; intro x u hu;
          exact .mtm (ih_s₀ x u hu) (ih_s₁ x u hu) (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih₀ ih₁; intro x u hu; exact .appV (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih₀ ih₁; intro x u hu; exact .vkrn (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih₀ ih₁; intro x u hu; exact .vblk (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih_e ih_τ ih_τ₀; intro x u hu;
          exact .reshap (ih_e x u hu) (ih_τ x u hu) (ih_τ₀ x u hu))
      (by intros; rename_i ih; intro x u hu; exact .vtrans (ih x u hu))
      (by intros; rename_i ih_e ih_a ih_b; intro x u hu; exact .gsvdS (ih_e x u hu) (ih_a x u hu) (ih_b x u hu))
      (by intros; rename_i ih_e ih_a ih_b; intro x u hu; exact .gsvdU (ih_e x u hu) (ih_a x u hu) (ih_b x u hu))
      (by intros; rename_i ih_e ih_a ih_b; intro x u hu; exact .gsvdUI (ih_e x u hu) (ih_a x u hu) (ih_b x u hu))
      (by intros; rename_i ih_e ih_a ih_b; intro x u hu; exact .gsvdV (ih_e x u hu) (ih_a x u hu) (ih_b x u hu))
      (by intros; rename_i ih_e ih_a ih_b; intro x u hu; exact .gsvdVI (ih_e x u hu) (ih_a x u hu) (ih_b x u hu))
      (by intros; rename_i ih; intro x u hu; exact .pinv (ih x u hu))
      (by intros; rename_i ih_e ih_a ih_b; intro x u hu; exact .gpinv (ih_e x u hu) (ih_a x u hu) (ih_b x u hu))
      (by intros; rename_i ih₀ ih₁; intro x u hu; exact .rrefRep (ih₀ x u hu) (ih₁ x u hu))
      (by intros; rename_i ih; intro x u hu; exact .inv (ih x u hu))
      (by intros; rename_i ih; intro x u hu; exact .svds (ih x u hu))

/-- `ValExpr.subst` preserves `lc`. -/
theorem ValExpr.lc_subst {e : ValExpr} (h : ValExpr.lc e) (x : VName) (u : ValExpr)
    (hu : ValExpr.lc u) : ValExpr.lc (ValExpr.subst x u e) :=
  lc_subst_joint.2.2 h x u hu

/-- On a closed argument and a locally closed function type, full beta
substitution agrees with the existing locally nameless instantiation. -/
theorem ValTy.applyCodomain_eq_instantiate {d c : ValTy} {a : ValExpr}
    (hf : ValTy.lc (.piTy d c)) (ha : ValExpr.lc a) :
    ValTy.applyCodomain a c = ValTy.instantiate a c := by
  have hr := DirectOracleOpenPush.raiseTy_lc hf 1 0
  have hc : ValTy.raise 1 1 c = c := by
    simpa only [ValTy.raise, ValTy.piTy.injEq, DirectOracleOpenPush.raiseTy_lc
      (by cases hf; assumption) 1 0, true_and] using hr
  exact ValTy.substBound_eq_openRec a ha c 0 hc

/-- Substituting a closed argument in a closed function type gives a closed type. -/
theorem ValTy.applyCodomain_lc {d c : ValTy} {a : ValExpr}
    (hf : ValTy.lc (.piTy d c)) (ha : ValExpr.lc a) :
    ValTy.lc (ValTy.applyCodomain a c) := by
  rw [ValTy.applyCodomain_eq_instantiate hf ha]
  cases hf with
  | piTy L hd hb =>
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ c.fv)
    simp only [Finset.mem_union, not_or] at hx
    have h := lc_subst_joint.2.1 (hb x hx.1) x a ha
    simpa only [ValTy.openVar, ← ValTy.subst_intro x a d c hx.2 0] using h

end GLang
