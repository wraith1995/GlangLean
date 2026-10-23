import GLang.Proofs.Adequacy.Raw.Conversion.RawCobAdequacyCore

/-!
# Product change-of-basis arms for raw adequacy

The direct-sum and tensor-product COB constructors combine two recursive
change-of-basis facts.  Their operational arrays are respectively block
diagonal and Kronecker products.  This module proves those two numerical
facts directly over `RawMCobSubctx` and pairs them with the clean inference
arms from `RawCobAdequacyCore`.
-/

namespace GLang

open scoped BigOperators TensorProduct
open Basis (BasisValid)

/-! ## Finite-sum and basis-list algebra -/

private theorem raw_products_fin_sum_cast_of_eq
    {M : Type} [AddCommMonoid M] {n m : Nat}
    (h : n = m) (f : Fin n -> M) :
    (∑ i, f i) = ∑ i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  rfl

private theorem raw_products_sum_prod_left
    {ι A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset ι) (g : ι -> A) :
    (∑ i ∈ s, (g i, (0 : B))) = (∑ i ∈ s, g i, 0) := by
  classical
  induction s using Finset.induction with
  | empty => apply Prod.ext <;> simp
  | insert a s ha ih => apply Prod.ext <;> simp [ha, ih]

private theorem raw_products_sum_prod_right
    {ι A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset ι) (g : ι -> B) :
    (∑ i ∈ s, ((0 : A), g i)) = (0, ∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => apply Prod.ext <;> simp
  | insert a s ha ih => apply Prod.ext <;> simp [ha, ih]

private theorem raw_products_dsum_getD_left
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) (i : Nat) (hi : i < vs0.length) :
    (HSpace.dsumOfLists V0 V1 vs0 vs1).getD i 0 =
      (vs0.getD i 0, 0) := by
  unfold HSpace.dsumOfLists
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  change (vs0.map (fun x => (x, 0))).getD i ((0, 0)) = _
  rw [show ((0, 0) : V0.carrier × V1.carrier) =
      (fun x => (x, 0)) 0 by rfl, List.getD_map]

private theorem raw_products_dsum_getD_right
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) (i : Nat) (_hi : i < vs1.length) :
    (HSpace.dsumOfLists V0 V1 vs0 vs1).getD (vs0.length + i) 0 =
      (0, vs1.getD i 0) := by
  unfold HSpace.dsumOfLists
  have hmaplen :
      (vs0.map (LinearMap.inl ℝ V0.carrier V1.carrier)).length =
        vs0.length := List.length_map _
  rw [← hmaplen]
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]
  change (vs1.map (fun x => (0, x))).getD i ((0, 0)) = _
  rw [show ((0, 0) : V0.carrier × V1.carrier) =
      (fun x => (0, x)) 0 by rfl, List.getD_map]

private theorem raw_products_dsum_coeff_sum
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) {N0 N1 : Nat}
    (hl0 : vs0.length = N0) (hl1 : vs1.length = N1)
    (c : Fin (N0 + N1) -> ℝ) :
    (∑ i, c i • (HSpace.dsumOfLists V0 V1 vs0 vs1).getD i 0) =
      (∑ i : Fin N0, c (Fin.castAdd N1 i) • vs0.getD i 0,
       ∑ i : Fin N1, c (Fin.natAdd N0 i) • vs1.getD i 0) := by
  subst hl0
  subst hl1
  rw [Fin.sum_univ_add]
  have h0 : (∑ i : Fin vs0.length,
      c (Fin.castAdd vs1.length i) •
        (HSpace.dsumOfLists V0 V1 vs0 vs1).getD
          (Fin.castAdd vs1.length i) 0) =
      (∑ i : Fin vs0.length,
        c (Fin.castAdd vs1.length i) • vs0.getD i 0, 0) := by
    rw [← raw_products_sum_prod_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.val_castAdd,
      raw_products_dsum_getD_left _ _ _ _ _ i.isLt]
    apply Prod.ext <;> simp
  have h1 : (∑ i : Fin vs1.length,
      c (Fin.natAdd vs0.length i) •
        (HSpace.dsumOfLists V0 V1 vs0 vs1).getD
          (Fin.natAdd vs0.length i) 0) =
      (0, ∑ i : Fin vs1.length,
        c (Fin.natAdd vs0.length i) • vs1.getD i 0) := by
    rw [← raw_products_sum_prod_right]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.val_natAdd,
      raw_products_dsum_getD_right _ _ _ _ _ i.isLt]
    apply Prod.ext <;> simp
  rw [h0, h1]
  ext <;> simp

private theorem raw_products_sum_range_mul_div_mod
    {M : Type} [AddCommMonoid M]
    (m n : Nat) (g : Nat -> Nat -> M) :
    (∑ k ∈ Finset.range (m * n), g (k / n) (k % n)) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, g i j := by
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro i
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro j
  have hnpos : 0 < n := Nat.zero_lt_of_lt j.isLt
  change g ((j.val + n * i.val) / n) ((j.val + n * i.val) % n) =
    g i.val j.val
  rw [Nat.add_mul_div_left _ _ hnpos, Nat.div_eq_of_lt j.isLt,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  simp

private theorem raw_products_tprod_coeff_sum_range
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) (c0 c1 : Nat -> ℝ) :
    (∑ k ∈ Finset.range (vs0.length * vs1.length),
      (c0 (k / vs1.length) * c1 (k % vs1.length)) •
        (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0) =
      (∑ i ∈ Finset.range vs0.length, c0 i • vs0.getD i 0) ⊗ₜ[ℝ]
        (∑ j ∈ Finset.range vs1.length, c1 j • vs1.getD j 0) := by
  by_cases hn : vs1.length = 0
  · rw [hn, Nat.mul_zero]
    simp
  have hnpos : 0 < vs1.length := Nat.pos_of_ne_zero hn
  calc
    (∑ k ∈ Finset.range (vs0.length * vs1.length),
      (c0 (k / vs1.length) * c1 (k % vs1.length)) •
        (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0) =
        ∑ k ∈ Finset.range (vs0.length * vs1.length),
          (c0 (k / vs1.length) * c1 (k % vs1.length)) •
            (vs0.getD (k / vs1.length) 0 ⊗ₜ[ℝ]
              vs1.getD (k % vs1.length) 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hklist : k < (HSpace.tprodOfLists V0 V1 vs0 vs1).length := by
        rw [HSpace.tprodOfLists_length]
        exact hk'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklist,
        HSpace.tprodOfLists_getElem vs0 vs1 k hk' hnpos]
      have hi : k / vs1.length < vs0.length :=
        (Nat.div_lt_iff_lt_mul hnpos).2 hk'
      have hj : k % vs1.length < vs1.length := Nat.mod_lt _ hnpos
      rw [List.getD_eq_getElem vs0 0 hi,
        List.getD_eq_getElem vs1 0 hj]
      simp only [Option.getD_some]
    _ = ∑ i ∈ Finset.range vs0.length,
          ∑ j ∈ Finset.range vs1.length,
            (c0 i * c1 j) • (vs0.getD i 0 ⊗ₜ[ℝ] vs1.getD j 0) := by
      exact raw_products_sum_range_mul_div_mod vs0.length vs1.length
        (fun i j => (c0 i * c1 j) •
          (vs0.getD i 0 ⊗ₜ[ℝ] vs1.getD j 0))
    _ = (∑ i ∈ Finset.range vs0.length, c0 i • vs0.getD i 0) ⊗ₜ[ℝ]
          (∑ j ∈ Finset.range vs1.length, c1 j • vs1.getD j 0) := by
      rw [TensorProduct.sum_tmul]
      apply Finset.sum_congr rfl
      intro i _
      rw [TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [TensorProduct.smul_tmul_smul]

private theorem raw_products_tprod_coeff_sum
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) {N0 N1 : Nat}
    (hl0 : vs0.length = N0) (hl1 : vs1.length = N1)
    (c : Fin (N0 * N1) -> ℝ) (c0 c1 : Nat -> ℝ)
    (hc : forall k : Fin (N0 * N1),
      c k = c0 (k / N1) * c1 (k % N1)) :
    (∑ k, c k • (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0) =
      (∑ i : Fin N0, c0 i • vs0.getD i 0) ⊗ₜ[ℝ]
        (∑ j : Fin N1, c1 j • vs1.getD j 0) := by
  subst hl0
  subst hl1
  simp only [hc]
  rw [Fin.sum_univ_eq_sum_range
      (fun k => (c0 (k / vs1.length) * c1 (k % vs1.length)) •
        (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0),
    Fin.sum_univ_eq_sum_range (fun i => c0 i • vs0.getD i 0),
    Fin.sum_univ_eq_sum_range (fun j => c1 j • vs1.getD j 0)]
  exact raw_products_tprod_coeff_sum_range V0 V1 vs0 vs1 c0 c1

private theorem raw_products_tprod_getD
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) (k : Nat)
    (hk : k < vs0.length * vs1.length) (hpos : 0 < vs1.length) :
    (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0 =
      vs0.getD (k / vs1.length) 0 ⊗ₜ[ℝ]
        vs1.getD (k % vs1.length) 0 := by
  have hklist : k < (HSpace.tprodOfLists V0 V1 vs0 vs1).length := by
    rw [HSpace.tprodOfLists_length]
    exact hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklist,
    HSpace.tprodOfLists_getElem vs0 vs1 k hk hpos]
  have hi : k / vs1.length < vs0.length :=
    (Nat.div_lt_iff_lt_mul hpos).2 hk
  have hj : k % vs1.length < vs1.length := Nat.mod_lt _ hpos
  rw [List.getD_eq_getElem vs0 0 hi,
    List.getD_eq_getElem vs1 0 hj]
  simp only [Option.getD_some]

private theorem raw_products_pos_right_of_lt_mul
    {N0 N1 j : Nat} (hj : j < N0 * N1) : 0 < N1 := by
  rcases Nat.eq_zero_or_pos N1 with h | h
  · rw [h, Nat.mul_zero] at hj
    exact absurd hj (Nat.not_lt_zero _)
  · exact h

/-! ## Tensor-product COB -/

private theorem raw_products_vkrn_get
    (orc : FFSOracleSem) (rho : ValEnvSem)
    {env0 env1 : ValExpr} {a a0 a1 : FlatArray}
    {sa sb sc sd : ValSpace} {N0 N1 : Nat}
    (henv0 : denotValB_semS orc rho [] [] env0 = .ok (.array a0))
    (henv1 : denotValB_semS orc rho [] [] env1 = .ok (.array a1))
    (hout : denotValB_semS orc rho [] [] (.vkrn env0 env1) =
      .ok (.array a))
    (hsab : ValExpr.inferSpaceCtx [] env0 = .tprod sa sb)
    (hscd : ValExpr.inferSpaceCtx [] env1 = .tprod sc sd)
    (ha : ValSpace.dof (orc rho [] []) sa = N0)
    (hb : ValSpace.dof (orc rho [] []) sb = N0)
    (hc : ValSpace.dof (orc rho [] []) sc = N1)
    (hd : ValSpace.dof (orc rho [] []) sd = N1)
    {j i : Nat} (hj : j < N0 * N1) (hi : i < N0 * N1) :
    a.get (j * (N0 * N1) + i) =
      a0.get (N0 * (j / N1) + i / N1) *
        a1.get (N1 * (j % N1) + i % N1) := by
  obtain ⟨hdiv, hmod⟩ := Nat.raw_rowMajor_div_mod hj hi
  have hlt := Nat.raw_rowMajor_lt hj hi
  rw [denotValB_semS.eq_14, henv0, henv1] at hout
  simp only [ValValSem.bindArrays, ValValSem.bindArray] at hout
  split at hout <;> try contradiction
  injection hout with hout
  injection hout with hout
  subst a
  simp only [ValExpr.inferSpaceCtx, hsab, hscd,
    ValSpace.dof_tprod, ha, hb, hc, hd, FlatArray.get_ofFn,
    hlt, if_true, hdiv, hmod]

private theorem raw_products_cobAgree_tprodOfLists
    (V0 V1 : HSpace) (S0 T0 : List V0.carrier)
    (S1 T1 : List V1.carrier) (a a0 a1 : FlatArray)
    (hT0len : T0.length = S0.length)
    (hT1len : T1.length = S1.length)
    (hsum0 : forall j : Fin S0.length,
      S0.getD j.val 0 = ∑ i : Fin S0.length,
        a0.get (j.val * S0.length + i.val) • T0.getD i.val 0)
    (hsum1 : forall j : Fin S1.length,
      S1.getD j.val 0 = ∑ i : Fin S1.length,
        a1.get (j.val * S1.length + i.val) • T1.getD i.val 0)
    (halen : a.length =
      (S0.length * S1.length) * (S0.length * S1.length))
    (hget : forall j i,
      j < S0.length * S1.length -> i < S0.length * S1.length ->
      a.get (j * (S0.length * S1.length) + i) =
        a0.get (S0.length * (j / S1.length) + i / S1.length) *
          a1.get (S1.length * (j % S1.length) + i % S1.length)) :
    (HSpace.tprodOfLists V0 V1 T0 T1).length =
        (HSpace.tprodOfLists V0 V1 S0 S1).length ∧
    a.length = (HSpace.tprodOfLists V0 V1 S0 S1).length *
        (HSpace.tprodOfLists V0 V1 S0 S1).length ∧
    forall j : Fin (HSpace.tprodOfLists V0 V1 S0 S1).length,
      (HSpace.tprodOfLists V0 V1 S0 S1).getD j.val 0 =
        ∑ i : Fin (HSpace.tprodOfLists V0 V1 S0 S1).length,
          a.get (j.val * (HSpace.tprodOfLists V0 V1 S0 S1).length +
            i.val) •
          (HSpace.tprodOfLists V0 V1 T0 T1).getD i.val 0 := by
  have hN : (HSpace.tprodOfLists V0 V1 S0 S1).length =
      S0.length * S1.length := HSpace.tprodOfLists_length _ _
  refine ⟨by
      rw [HSpace.tprodOfLists_length, HSpace.tprodOfLists_length,
        hT0len, hT1len], by rw [halen, hN], ?_⟩
  intro j
  have hj : j.val < S0.length * S1.length := hN ▸ j.isLt
  have hpos : 0 < S1.length := raw_products_pos_right_of_lt_mul hj
  have hj0 : j.val / S1.length < S0.length :=
    (Nat.div_lt_iff_lt_mul hpos).2 hj
  have hj1 : j.val % S1.length < S1.length := Nat.mod_lt _ hpos
  have e0 : S0.getD (j.val / S1.length) 0 =
      ∑ i : Fin S0.length,
        a0.get (S0.length * (j.val / S1.length) + i) •
          T0.getD i 0 := by
    rw [Nat.mul_comm S0.length]
    exact hsum0 ⟨_, hj0⟩
  have e1 : S1.getD (j.val % S1.length) 0 =
      ∑ i : Fin S1.length,
        a1.get (S1.length * (j.val % S1.length) + i) •
          T1.getD i 0 := by
    rw [Nat.mul_comm S1.length]
    exact hsum1 ⟨_, hj1⟩
  have hc : forall k : Fin (S0.length * S1.length),
      a.get (j.val * (HSpace.tprodOfLists V0 V1 S0 S1).length +
        k.val) =
        a0.get (S0.length * (j.val / S1.length) +
          k.val / S1.length) *
        a1.get (S1.length * (j.val % S1.length) +
          k.val % S1.length) := by
    intro k
    have hidx :
        j.val * (HSpace.tprodOfLists V0 V1 S0 S1).length + k.val =
          j.val * (S0.length * S1.length) + k.val :=
      congrArg (fun n => j.val * n + k.val) hN
    rw [hidx]
    exact hget _ _ hj k.isLt
  have key := raw_products_tprod_coeff_sum V0 V1 T0 T1
    hT0len hT1len
    (fun k : Fin (S0.length * S1.length) =>
      a.get (j.val * (HSpace.tprodOfLists V0 V1 S0 S1).length +
        k.val))
    (fun i => a0.get (S0.length * (j.val / S1.length) + i))
    (fun i => a1.get (S1.length * (j.val % S1.length) + i)) hc
  rw [raw_products_tprod_getD V0 V1 S0 S1 j.val hj hpos,
    e0, e1]
  refine key.symm.trans ?_
  rw [raw_products_fin_sum_cast_of_eq hN]
  simp only [Fin.val_cast]

theorem raw_arm_cob_tprod
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b0' b1' : Basis} {env0 env1 : ValExpr}
    (hinfer0 : RawCobInferSubctx orc Gamma Psi env0 b0')
    (hinfer1 : RawCobInferSubctx orc Gamma Psi env1 b1')
    (_hbS : BasisValid Gamma (.tprod b0' b1'))
    (_hbT : BasisValid Gamma (.tprod b0 b1))
    (h0 : S.Cob Gamma Psi b0' env0 b0)
    (h1 : S.Cob Gamma Psi b1' env1 b1)
    (ih0 : RawMCobSubctx orc Gamma Psi b0' env0 b0)
    (ih1 : RawMCobSubctx orc Gamma Psi b1' env1 b1) :
    RawMCobSubctx orc Gamma Psi (.tprod b0' b1')
      (.vkrn env0 env1) (.tprod b0 b1) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hsof0 := S.Cob.sof_eq h0
  have hsof1 := S.Cob.sof_eq h1
  obtain ⟨sa, sb, hsab, hNa, hNb⟩ :=
    hinfer0 hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sc, sd, hscd, hNc, hNd⟩ :=
    hinfer1 hsub rho Delta' Gamma' sigma GammaV hle hc
  have hA0 := ih0 hsub rho Delta' Gamma' sigma GammaV hle hc
  have hA1 := ih1 hsub rho Delta' Gamma' sigma GammaV hle hc
  unfold CobAgree at hA0 hA1 ⊢
  dsimp only at hA0 hA1 ⊢
  obtain ⟨hT0len, a0, ha0, ha0Len, hsum0⟩ := hA0
  obtain ⟨hT1len, a1, ha1, ha1Len, hsum1⟩ := hA1
  have hS : (denotBasis sigma (.tprod b0' b1')).atSpace
      (denotSpace sigma (Basis.sof (.tprod b0' b1'))) =
      HSpace.tprodOfLists
        (denotSpace sigma (Basis.sof b0'))
        (denotSpace sigma (Basis.sof b1'))
        ((denotBasis sigma b0').atSpace
          (denotSpace sigma (Basis.sof b0')))
        ((denotBasis sigma b1').atSpace
          (denotSpace sigma (Basis.sof b1'))) := by
    show BasisDenot.atSpace
      (HSpace.tprod (denotSpace sigma (Basis.sof b0'))
        (denotSpace sigma (Basis.sof b1')))
      (denotBasis sigma (.tprod b0' b1')) = _
    simp only [denotBasis]
    exact BasisDenot.atSpace_vecs_self _ _
  have hT : (denotBasis sigma (.tprod b0 b1)).atSpace
      (denotSpace sigma (Basis.sof (.tprod b0' b1'))) =
      HSpace.tprodOfLists
        (denotSpace sigma (Basis.sof b0'))
        (denotSpace sigma (Basis.sof b1'))
        ((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0')))
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1'))) := by
    show BasisDenot.atSpace
      (HSpace.tprod (denotSpace sigma (Basis.sof b0'))
        (denotSpace sigma (Basis.sof b1')))
      (denotBasis sigma (.tprod b0 b1)) = _
    rw [show denotBasis sigma (.tprod b0 b1) =
        BasisDenot.vecs
          (HSpace.tprod (denotSpace sigma (Basis.sof b0'))
            (denotSpace sigma (Basis.sof b1')))
          (HSpace.tprodOfLists
            (denotSpace sigma (Basis.sof b0'))
            (denotSpace sigma (Basis.sof b1'))
            ((denotBasis sigma b0).atSpace
              (denotSpace sigma (Basis.sof b0')))
            ((denotBasis sigma b1).atSpace
              (denotSpace sigma (Basis.sof b1'))))
      from by simp only [denotBasis]; rw [← hsof0, ← hsof1]]
    exact BasisDenot.atSpace_vecs_self _ _
  rw [hS, hT]
  set S0 := (denotBasis sigma b0').atSpace
    (denotSpace sigma (Basis.sof b0')) with hS0
  set S1 := (denotBasis sigma b1').atSpace
    (denotSpace sigma (Basis.sof b1')) with hS1
  set T0 := (denotBasis sigma b0).atSpace
    (denotSpace sigma (Basis.sof b0')) with hT0
  set T1 := (denotBasis sigma b1).atSpace
    (denotSpace sigma (Basis.sof b1')) with hT1
  have hn : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.vkrn env0 env1)) =
      (S0.length * S1.length) * (S0.length * S1.length) := by
    simp only [ValExpr.inferSpaceCtx, hsab, hscd,
      ValSpace.dof_tprod, hNa, hNb, hNc, hNd]
  have hguard : ValueShape.matrices (orc rho [] [])
      (ValExpr.inferSpaceCtx [] env0) (ValExpr.inferSpaceCtx [] env1) a0 a1 := by
    simp only [ValueShape.matrices, ValueShape.tensor, hsab, hscd,
      hNa, hNb, hNc, hNd]
    exact ⟨ha0Len, ha1Len⟩
  obtain ⟨a, hval⟩ : exists a,
      denotValB_semS orc rho [] [] (.vkrn env0 env1) =
        .ok (.array a) := by
    rw [denotValB_semS.eq_14, ha0, ha1]
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hguard]
    exact ⟨_, rfl⟩
  have halen : a.length =
      (S0.length * S1.length) * (S0.length * S1.length) := by
    rw [denotValB_semS.eq_14, ha0, ha1] at hval
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hguard] at hval
    injection hval with hval
    injection hval with hval
    subst a
    simp [hn]
  have hget : forall j i,
      j < S0.length * S1.length -> i < S0.length * S1.length ->
      a.get (j * (S0.length * S1.length) + i) =
        a0.get (S0.length * (j / S1.length) + i / S1.length) *
          a1.get (S1.length * (j % S1.length) + i % S1.length) := by
    intro j i hj hi
    exact raw_products_vkrn_get orc rho ha0 ha1 hval hsab hscd
      hNa hNb hNc hNd hj hi
  obtain ⟨h1, h2, h3⟩ := raw_products_cobAgree_tprodOfLists
    (denotSpace sigma (Basis.sof b0'))
    (denotSpace sigma (Basis.sof b1'))
    S0 T0 S1 T1 a a0 a1 hT0len hT1len hsum0 hsum1 halen hget
  exact ⟨h1, a, hval, h2, h3⟩

theorem raw_arm_cob_facts_tprod
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b0' b1' : Basis} {env0 env1 : ValExpr}
    (hbS : BasisValid Gamma (.tprod b0' b1'))
    (hbT : BasisValid Gamma (.tprod b0 b1))
    (h0 : S.Cob Gamma Psi b0' env0 b0)
    (h1 : S.Cob Gamma Psi b1' env1 b1)
    (ih0 : RawCobFactsSubctx orc Gamma Psi b0' env0 b0)
    (ih1 : RawCobFactsSubctx orc Gamma Psi b1' env1 b1) :
    RawCobFactsSubctx orc Gamma Psi (.tprod b0' b1')
      (.vkrn env0 env1) (.tprod b0 b1) :=
  ⟨raw_arm_cob_tprod ih0.infer ih1.infer hbS hbT h0 h1
      ih0.agree ih1.agree,
    raw_arm_cob_infer_tprod (b0 := b0) (b1 := b1)
      ih0.infer ih1.infer⟩

/-! ## Direct-sum COB -/

private theorem raw_products_vblk_get
    (orc : FFSOracleSem) (rho : ValEnvSem)
    {env0 env1 : ValExpr} {a a0 a1 : FlatArray}
    {sa sb sc sd : ValSpace} {N0 N1 : Nat}
    (henv0 : denotValB_semS orc rho [] [] env0 = .ok (.array a0))
    (henv1 : denotValB_semS orc rho [] [] env1 = .ok (.array a1))
    (hout : denotValB_semS orc rho [] [] (.vblk env0 env1) =
      .ok (.array a))
    (hsab : ValExpr.inferSpaceCtx [] env0 = .tprod sa sb)
    (hscd : ValExpr.inferSpaceCtx [] env1 = .tprod sc sd)
    (ha : ValSpace.dof (orc rho [] []) sa = N0)
    (hb : ValSpace.dof (orc rho [] []) sb = N0)
    (hc : ValSpace.dof (orc rho [] []) sc = N1)
    (hd : ValSpace.dof (orc rho [] []) sd = N1)
    {j i : Nat} (hj : j < N0 + N1) (hi : i < N0 + N1) :
    a.get (j * (N0 + N1) + i) =
      if j < N0 then
        (if i < N0 then a0.get (N0 * j + i) else 0)
      else
        (if i < N0 then 0
          else a1.get (N1 * (j - N0) + (i - N0))) := by
  obtain ⟨hdiv, hmod⟩ := Nat.raw_rowMajor_div_mod hj hi
  have hlt := Nat.raw_rowMajor_lt hj hi
  rw [denotValB_semS.eq_15, henv0, henv1] at hout
  simp only [ValValSem.bindArrays, ValValSem.bindArray] at hout
  split at hout <;> try contradiction
  injection hout with hout
  injection hout with hout
  subst a
  simp only [ValExpr.inferSpaceCtx, hsab, hscd,
    ValSpace.dof_tprod, ValSpace.dof_dsum,
    ha, hb, hc, hd, FlatArray.get_ofFn,
    hlt, if_true, hdiv, hmod]

private theorem raw_products_cobAgree_dsumOfLists
    (V0 V1 : HSpace) (S0 T0 : List V0.carrier)
    (S1 T1 : List V1.carrier) (a a0 a1 : FlatArray)
    (hT0len : T0.length = S0.length)
    (hT1len : T1.length = S1.length)
    (hsum0 : forall j : Fin S0.length,
      S0.getD j.val 0 = ∑ i : Fin S0.length,
        a0.get (j.val * S0.length + i.val) • T0.getD i.val 0)
    (hsum1 : forall j : Fin S1.length,
      S1.getD j.val 0 = ∑ i : Fin S1.length,
        a1.get (j.val * S1.length + i.val) • T1.getD i.val 0)
    (halen : a.length =
      (S0.length + S1.length) * (S0.length + S1.length))
    (hget : forall j i,
      j < S0.length + S1.length -> i < S0.length + S1.length ->
      a.get (j * (S0.length + S1.length) + i) =
        if j < S0.length then
          (if i < S0.length then
            a0.get (S0.length * j + i) else 0)
        else
          (if i < S0.length then 0
            else a1.get
              (S1.length * (j - S0.length) + (i - S0.length)))) :
    (HSpace.dsumOfLists V0 V1 T0 T1).length =
        (HSpace.dsumOfLists V0 V1 S0 S1).length ∧
    a.length = (HSpace.dsumOfLists V0 V1 S0 S1).length *
        (HSpace.dsumOfLists V0 V1 S0 S1).length ∧
    forall j : Fin (HSpace.dsumOfLists V0 V1 S0 S1).length,
      (HSpace.dsumOfLists V0 V1 S0 S1).getD j.val 0 =
        ∑ i : Fin (HSpace.dsumOfLists V0 V1 S0 S1).length,
          a.get (j.val * (HSpace.dsumOfLists V0 V1 S0 S1).length +
            i.val) •
          (HSpace.dsumOfLists V0 V1 T0 T1).getD i.val 0 := by
  have hN : (HSpace.dsumOfLists V0 V1 S0 S1).length =
      S0.length + S1.length := HSpace.dsumOfLists_length _ _
  refine ⟨by
      rw [HSpace.dsumOfLists_length, HSpace.dsumOfLists_length,
        hT0len, hT1len], by rw [halen, hN], ?_⟩
  intro j
  have hj : j.val < S0.length + S1.length := hN ▸ j.isLt
  have hidx : forall i : Nat,
      j.val * (HSpace.dsumOfLists V0 V1 S0 S1).length + i =
        j.val * (S0.length + S1.length) + i :=
    fun i => congrArg (fun n => j.val * n + i) hN
  rw [raw_products_fin_sum_cast_of_eq hN]
  simp only [Fin.val_cast]
  rw [raw_products_dsum_coeff_sum V0 V1 T0 T1 hT0len hT1len]
  by_cases hjl : j.val < S0.length
  · have e0 : S0.getD j.val 0 =
        ∑ i : Fin S0.length,
          a0.get (j.val * S0.length + i) • T0.getD i 0 :=
      hsum0 ⟨_, hjl⟩
    rw [raw_products_dsum_getD_left _ _ _ _ _ hjl, e0]
    refine Prod.ext ?_ ?_
    · dsimp only
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.val_castAdd, hidx,
        hget _ _ hj (lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)),
        if_pos hjl, if_pos i.isLt, Nat.mul_comm S0.length]
    · dsimp only
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [Fin.val_natAdd, hidx,
        hget _ _ hj (Nat.add_lt_add_left i.isLt _), if_pos hjl,
        if_neg (not_lt.mpr (Nat.le_add_right _ _)), zero_smul]
  · have hj' : j.val - S0.length < S1.length := by omega
    have hjv : j.val = S0.length + (j.val - S0.length) := by omega
    have e1 : S1.getD (j.val - S0.length) 0 =
        ∑ i : Fin S1.length,
          a1.get ((j.val - S0.length) * S1.length + i) •
            T1.getD i 0 := hsum1 ⟨_, hj'⟩
    conv_lhs => rw [hjv]
    rw [raw_products_dsum_getD_right _ _ _ _ _ hj', e1]
    refine Prod.ext ?_ ?_
    · dsimp only
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [Fin.val_castAdd, hidx,
        hget _ _ hj (lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)),
        if_neg hjl, if_pos i.isLt, zero_smul]
    · dsimp only
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.val_natAdd, hidx,
        hget _ _ hj (Nat.add_lt_add_left i.isLt _), if_neg hjl,
        if_neg (not_lt.mpr (Nat.le_add_right _ _)),
        Nat.add_sub_cancel_left, Nat.mul_comm S1.length]

theorem raw_arm_cob_dsum
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b0' b1' : Basis} {env0 env1 : ValExpr}
    (hinfer0 : RawCobInferSubctx orc Gamma Psi env0 b0')
    (hinfer1 : RawCobInferSubctx orc Gamma Psi env1 b1')
    (_hbS : BasisValid Gamma (.dsum b0' b1'))
    (_hbT : BasisValid Gamma (.dsum b0 b1))
    (h0 : S.Cob Gamma Psi b0' env0 b0)
    (h1 : S.Cob Gamma Psi b1' env1 b1)
    (ih0 : RawMCobSubctx orc Gamma Psi b0' env0 b0)
    (ih1 : RawMCobSubctx orc Gamma Psi b1' env1 b1) :
    RawMCobSubctx orc Gamma Psi (.dsum b0' b1')
      (.vblk env0 env1) (.dsum b0 b1) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hsof0 := S.Cob.sof_eq h0
  have hsof1 := S.Cob.sof_eq h1
  obtain ⟨sa, sb, hsab, hNa, hNb⟩ :=
    hinfer0 hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sc, sd, hscd, hNc, hNd⟩ :=
    hinfer1 hsub rho Delta' Gamma' sigma GammaV hle hc
  have hA0 := ih0 hsub rho Delta' Gamma' sigma GammaV hle hc
  have hA1 := ih1 hsub rho Delta' Gamma' sigma GammaV hle hc
  unfold CobAgree at hA0 hA1 ⊢
  dsimp only at hA0 hA1 ⊢
  obtain ⟨hT0len, a0, ha0, ha0Len, hsum0⟩ := hA0
  obtain ⟨hT1len, a1, ha1, ha1Len, hsum1⟩ := hA1
  have hS : (denotBasis sigma (.dsum b0' b1')).atSpace
      (denotSpace sigma (Basis.sof (.dsum b0' b1'))) =
      HSpace.dsumOfLists
        (denotSpace sigma (Basis.sof b0'))
        (denotSpace sigma (Basis.sof b1'))
        ((denotBasis sigma b0').atSpace
          (denotSpace sigma (Basis.sof b0')))
        ((denotBasis sigma b1').atSpace
          (denotSpace sigma (Basis.sof b1'))) := by
    show BasisDenot.atSpace
      (HSpace.dsum (denotSpace sigma (Basis.sof b0'))
        (denotSpace sigma (Basis.sof b1')))
      (denotBasis sigma (.dsum b0' b1')) = _
    simp only [denotBasis]
    exact BasisDenot.atSpace_vecs_self _ _
  have hT : (denotBasis sigma (.dsum b0 b1)).atSpace
      (denotSpace sigma (Basis.sof (.dsum b0' b1'))) =
      HSpace.dsumOfLists
        (denotSpace sigma (Basis.sof b0'))
        (denotSpace sigma (Basis.sof b1'))
        ((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0')))
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1'))) := by
    show BasisDenot.atSpace
      (HSpace.dsum (denotSpace sigma (Basis.sof b0'))
        (denotSpace sigma (Basis.sof b1')))
      (denotBasis sigma (.dsum b0 b1)) = _
    rw [show denotBasis sigma (.dsum b0 b1) =
        BasisDenot.vecs
          (HSpace.dsum (denotSpace sigma (Basis.sof b0'))
            (denotSpace sigma (Basis.sof b1')))
          (HSpace.dsumOfLists
            (denotSpace sigma (Basis.sof b0'))
            (denotSpace sigma (Basis.sof b1'))
            ((denotBasis sigma b0).atSpace
              (denotSpace sigma (Basis.sof b0')))
            ((denotBasis sigma b1).atSpace
              (denotSpace sigma (Basis.sof b1'))))
      from by simp only [denotBasis]; rw [← hsof0, ← hsof1]]
    exact BasisDenot.atSpace_vecs_self _ _
  rw [hS, hT]
  set S0 := (denotBasis sigma b0').atSpace
    (denotSpace sigma (Basis.sof b0')) with hS0
  set S1 := (denotBasis sigma b1').atSpace
    (denotSpace sigma (Basis.sof b1')) with hS1
  set T0 := (denotBasis sigma b0).atSpace
    (denotSpace sigma (Basis.sof b0')) with hT0
  set T1 := (denotBasis sigma b1).atSpace
    (denotSpace sigma (Basis.sof b1')) with hT1
  have hn : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.vblk env0 env1)) =
      (S0.length + S1.length) * (S0.length + S1.length) := by
    simp only [ValExpr.inferSpaceCtx, hsab, hscd,
      ValSpace.dof_tprod, ValSpace.dof_dsum,
      hNa, hNb, hNc, hNd]
  have hguard : ValueShape.matrices (orc rho [] [])
      (ValExpr.inferSpaceCtx [] env0) (ValExpr.inferSpaceCtx [] env1) a0 a1 := by
    simp only [ValueShape.matrices, ValueShape.tensor, hsab, hscd,
      hNa, hNb, hNc, hNd]
    exact ⟨ha0Len, ha1Len⟩
  obtain ⟨a, hval⟩ : exists a,
      denotValB_semS orc rho [] [] (.vblk env0 env1) =
        .ok (.array a) := by
    rw [denotValB_semS.eq_15, ha0, ha1]
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hguard]
    exact ⟨_, rfl⟩
  have halen : a.length =
      (S0.length + S1.length) * (S0.length + S1.length) := by
    rw [denotValB_semS.eq_15, ha0, ha1] at hval
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hguard] at hval
    injection hval with hval
    injection hval with hval
    subst a
    simp [hn]
  have hget : forall j i,
      j < S0.length + S1.length -> i < S0.length + S1.length ->
      a.get (j * (S0.length + S1.length) + i) =
        if j < S0.length then
          (if i < S0.length then a0.get (S0.length * j + i) else 0)
        else
          (if i < S0.length then 0
            else a1.get
              (S1.length * (j - S0.length) + (i - S0.length))) := by
    intro j i hj hi
    exact raw_products_vblk_get orc rho ha0 ha1 hval hsab hscd
      hNa hNb hNc hNd hj hi
  obtain ⟨h1, h2, h3⟩ := raw_products_cobAgree_dsumOfLists
    (denotSpace sigma (Basis.sof b0'))
    (denotSpace sigma (Basis.sof b1'))
    S0 T0 S1 T1 a a0 a1 hT0len hT1len hsum0 hsum1 halen hget
  exact ⟨h1, a, hval, h2, h3⟩

theorem raw_arm_cob_facts_dsum
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 b0' b1' : Basis} {env0 env1 : ValExpr}
    (hbS : BasisValid Gamma (.dsum b0' b1'))
    (hbT : BasisValid Gamma (.dsum b0 b1))
    (h0 : S.Cob Gamma Psi b0' env0 b0)
    (h1 : S.Cob Gamma Psi b1' env1 b1)
    (ih0 : RawCobFactsSubctx orc Gamma Psi b0' env0 b0)
    (ih1 : RawCobFactsSubctx orc Gamma Psi b1' env1 b1) :
    RawCobFactsSubctx orc Gamma Psi (.dsum b0' b1')
      (.vblk env0 env1) (.dsum b0 b1) :=
  ⟨raw_arm_cob_dsum ih0.infer ih1.infer hbS hbT h0 h1
      ih0.agree ih1.agree,
    raw_arm_cob_infer_dsum (b0 := b0) (b1 := b1)
      ih0.infer ih1.infer⟩

end GLang
