import GLang.Proofs.Value.Binding.ValueBeta

set_option maxHeartbeats 2000000
namespace GLang
mutual
  theorem ValSpace.fv_substBound_subset (u : ValExpr) :
      ∀ (v : ValSpace) (k : Nat),
      ValSpace.fv (ValSpace.substBound k u v) ⊆ ValSpace.fv v ∪ u.fv
    | .empty, k => by
        intro z hz
        simp only [ValSpace.substBound, ValSpace.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .real, k => by
        intro z hz
        simp only [ValSpace.substBound, ValSpace.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .dsum s0 s1, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s0 k z
        have h1 := @ValSpace.fv_substBound_subset u s1 k z
        simp only [ValSpace.substBound, ValSpace.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .tprod s0 s1, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s0 k z
        have h1 := @ValSpace.fv_substBound_subset u s1 k z
        simp only [ValSpace.substBound, ValSpace.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .ffs p s e, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s k z
        have h1 := @ValExpr.fv_substBound_subset u e k z
        simp only [ValSpace.substBound, ValSpace.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
  theorem ValTy.fv_substBound_subset (u : ValExpr) :
      ∀ (v : ValTy) (k : Nat),
      ValTy.fv (ValTy.substBound k u v) ⊆ ValTy.fv v ∪ u.fv
    | .space s, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s k z
        simp only [ValTy.substBound, ValTy.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .piTy t0 t1, k => by
        intro z hz
        have h0 := @ValTy.fv_substBound_subset u t0 k z
        have h1 := @ValTy.fv_substBound_subset u t1 (k + 1) z
        simp only [ValTy.substBound, ValTy.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
  theorem ValExpr.fv_substBound_subset (u : ValExpr) :
      ∀ (v : ValExpr) (k : Nat),
      ValExpr.fv (ValExpr.substBound k u v) ⊆ ValExpr.fv v ∪ u.fv
    | .bvar i, k => by
        by_cases hi : i = k
        · simp [ValExpr.substBound, hi, ValExpr.fv_raise, ValExpr.fv]
        · by_cases hk : k < i <;> simp [ValExpr.substBound, hi, hk, ValExpr.fv]
    | .var y t, k => by
        intro z hz
        have h0 := @ValTy.fv_substBound_subset u t k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .vlam t0 t1 e, k => by
        intro z hz
        have h0 := @ValTy.fv_substBound_subset u t0 k z
        have h1 := @ValTy.fv_substBound_subset u t1 (k + 1) z
        have h2 := @ValExpr.fv_substBound_subset u e (k + 1) z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .zero s, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .rlit r, k => by
        intro z hz
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .scale e0 e1, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e0 k z
        have h1 := @ValExpr.fv_substBound_subset u e1 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .dsumE e0 e1, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e0 k z
        have h1 := @ValExpr.fv_substBound_subset u e1 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .tprodE e0 e1, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e0 k z
        have h1 := @ValExpr.fv_substBound_subset u e1 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .appV e0 e1, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e0 k z
        have h1 := @ValExpr.fv_substBound_subset u e1 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .vkrn e0 e1, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e0 k z
        have h1 := @ValExpr.fv_substBound_subset u e1 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .vblk e0 e1, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e0 k z
        have h1 := @ValExpr.fv_substBound_subset u e1 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .rrefRep e0 e1, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e0 k z
        have h1 := @ValExpr.fv_substBound_subset u e1 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .vadd s e0 e1, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s k z
        have h1 := @ValExpr.fv_substBound_subset u e0 k z
        have h2 := @ValExpr.fv_substBound_subset u e1 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .delta i s, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .idelta s, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .vsum s es, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s k z
        have h1 := @ValExpr.fv_substBound_subsetList u es k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .ttv s e0 e1, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s k z
        have h1 := @ValExpr.fv_substBound_subset u e0 k z
        have h2 := @ValExpr.fv_substBound_subset u e1 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .mtm i j s0 s1 e0 e1, k => by
        intro z hz
        have h0 := @ValSpace.fv_substBound_subset u s0 k z
        have h1 := @ValSpace.fv_substBound_subset u s1 k z
        have h2 := @ValExpr.fv_substBound_subset u e0 k z
        have h3 := @ValExpr.fv_substBound_subset u e1 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .reshap e t t0, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        have h1 := @ValTy.fv_substBound_subset u t k z
        have h2 := @ValTy.fv_substBound_subset u t0 k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .vtrans e, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .pinv e, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .inv e, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .svds e, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .gsvdS e a b, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        have h1 := @ValExpr.fv_substBound_subset u a k z
        have h2 := @ValExpr.fv_substBound_subset u b k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .gsvdU e a b, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        have h1 := @ValExpr.fv_substBound_subset u a k z
        have h2 := @ValExpr.fv_substBound_subset u b k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .gsvdUI e a b, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        have h1 := @ValExpr.fv_substBound_subset u a k z
        have h2 := @ValExpr.fv_substBound_subset u b k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .gsvdV e a b, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        have h1 := @ValExpr.fv_substBound_subset u a k z
        have h2 := @ValExpr.fv_substBound_subset u b k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .gsvdVI e a b, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        have h1 := @ValExpr.fv_substBound_subset u a k z
        have h2 := @ValExpr.fv_substBound_subset u b k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | .gpinv e a b, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        have h1 := @ValExpr.fv_substBound_subset u a k z
        have h2 := @ValExpr.fv_substBound_subset u b k z
        simp only [ValExpr.substBound, ValExpr.fv, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
  theorem ValExpr.fv_substBound_subsetList (u : ValExpr) :
      ∀ (v : List ValExpr) (k : Nat),
      ValExpr.fvList (ValExpr.substBoundList k u v) ⊆ ValExpr.fvList v ∪ u.fv
    | [], k => by
        intro z hz
        simp only [ValExpr.substBoundList, ValExpr.fvList, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
    | e :: es, k => by
        intro z hz
        have h0 := @ValExpr.fv_substBound_subset u e k z
        have h1 := @ValExpr.fv_substBound_subsetList u es k z
        simp only [ValExpr.substBoundList, ValExpr.fvList, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty] at *
        all_goals first | tauto | aesop
end
end GLang
