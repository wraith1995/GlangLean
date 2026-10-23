import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCob

namespace GLang.PartialAdequacy
open scoped TensorProduct
open PartialValueEval

private theorem partial_cob_fin_sum_cast_of_eq
    {M : Type} [AddCommMonoid M] {n m : Nat}
    (h : n = m) (f : Fin n -> M) :
    (∑ i, f i) = ∑ i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  rfl

private theorem partial_cob_sum_prod_left
    {ι A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset ι) (g : ι -> A) :
    (∑ i ∈ s, (g i, (0 : B))) = (∑ i ∈ s, g i, 0) := by
  classical
  induction s using Finset.induction with
  | empty => apply Prod.ext <;> simp
  | insert a s ha ih => apply Prod.ext <;> simp [ha, ih]

private theorem partial_cob_sum_prod_right
    {ι A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset ι) (g : ι -> B) :
    (∑ i ∈ s, ((0 : A), g i)) = (0, ∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => apply Prod.ext <;> simp
  | insert a s ha ih => apply Prod.ext <;> simp [ha, ih]

private theorem partial_cob_dsum_getD_left
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) (i : Nat) (hi : i < vs0.length) :
    (HSpace.dsumOfLists V0 V1 vs0 vs1).getD i 0 =
      (vs0.getD i 0, 0) := by
  unfold HSpace.dsumOfLists
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  change (vs0.map (fun x => (x, 0))).getD i ((0, 0)) = _
  rw [show ((0, 0) : V0.carrier × V1.carrier) =
      (fun x => (x, 0)) 0 by rfl, List.getD_map]

private theorem partial_cob_dsum_getD_right
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

private theorem partial_cob_dsum_coeff_sum
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
    rw [← partial_cob_sum_prod_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.val_castAdd,
      partial_cob_dsum_getD_left _ _ _ _ _ i.isLt]
    apply Prod.ext <;> simp
  have h1 : (∑ i : Fin vs1.length,
      c (Fin.natAdd vs0.length i) •
        (HSpace.dsumOfLists V0 V1 vs0 vs1).getD
          (Fin.natAdd vs0.length i) 0) =
      (0, ∑ i : Fin vs1.length,
        c (Fin.natAdd vs0.length i) • vs1.getD i 0) := by
    rw [← partial_cob_sum_prod_right]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.val_natAdd,
      partial_cob_dsum_getD_right _ _ _ _ _ i.isLt]
    apply Prod.ext <;> simp
  rw [h0, h1]
  ext <;> simp

private theorem partial_cob_sum_range_mul_div_mod
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

private theorem partial_cob_tprod_coeff_sum_range
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
      exact partial_cob_sum_range_mul_div_mod vs0.length vs1.length
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

private theorem partial_cob_tprod_coeff_sum
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
  exact partial_cob_tprod_coeff_sum_range V0 V1 vs0 vs1 c0 c1

private theorem partial_cob_tprod_getD
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

private theorem partial_cob_pos_right_of_lt_mul
    {N0 N1 j : Nat} (hj : j < N0 * N1) : 0 < N1 := by
  rcases Nat.eq_zero_or_pos N1 with h | h
  · rw [h, Nat.mul_zero] at hj
    exact absurd hj (Nat.not_lt_zero _)
  · exact h

private theorem partial_cob_cobAgree_tprodOfLists
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
  have hpos : 0 < S1.length := partial_cob_pos_right_of_lt_mul hj
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
  have key := partial_cob_tprod_coeff_sum V0 V1 T0 T1
    hT0len hT1len
    (fun k : Fin (S0.length * S1.length) =>
      a.get (j.val * (HSpace.tprodOfLists V0 V1 S0 S1).length +
        k.val))
    (fun i => a0.get (S0.length * (j.val / S1.length) + i))
    (fun i => a1.get (S1.length * (j.val % S1.length) + i)) hc
  rw [partial_cob_tprod_getD V0 V1 S0 S1 j.val hj hpos,
    e0, e1]
  refine key.symm.trans ?_
  rw [partial_cob_fin_sum_cast_of_eq hN]
  simp only [Fin.val_cast]

private theorem partial_cob_cobAgree_dsumOfLists
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
  rw [partial_cob_fin_sum_cast_of_eq hN]
  simp only [Fin.val_cast]
  rw [partial_cob_dsum_coeff_sum V0 V1 T0 T1 hT0len hT1len]
  by_cases hjl : j.val < S0.length
  · have e0 : S0.getD j.val 0 =
        ∑ i : Fin S0.length,
          a0.get (j.val * S0.length + i) • T0.getD i 0 :=
      hsum0 ⟨_, hjl⟩
    rw [partial_cob_dsum_getD_left _ _ _ _ _ hjl, e0]
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
    rw [partial_cob_dsum_getD_right _ _ _ _ _ hj', e1]
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

variable {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
  {Γ : List ValTy} {Δ : List ValValSem}

theorem eval_vkrn_square {e₀ e₁ : ValExpr} {a₀ a₁ : FlatArray}
    {sa sb sc sd : ValSpace} {m n : Nat}
    (he₀ : denotValB_partial orc ρ Γ Δ e₀ = .ok (.array a₀))
    (he₁ : denotValB_partial orc ρ Γ Δ e₁ = .ok (.array a₁))
    (hi₀ : ValExpr.inferSpaceCtx Γ e₀ = .tprod sa sb)
    (hi₁ : ValExpr.inferSpaceCtx Γ e₁ = .tprod sc sd)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok m)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok m)
    (hc : sc.dofPartial (orc ρ Γ Δ) = .ok n)
    (hd : sd.dofPartial (orc ρ Γ Δ) = .ok n)
    (hlen₀ : a₀.length = m*m) (hlen₁ : a₁.length = n*n) :
    denotValB_partial orc ρ Γ Δ (.vkrn e₀ e₁) =
      .ok (.array (FlatArray.ofFn ((m*n)*(m*n)) (fun i =>
        a₀.get (m*((i/(m*n))/n)+(i%(m*n))/n) *
          a₁.get (n*((i/(m*n))%n)+(i%(m*n))%n)))) := by
  have hab := dof_tprod_ok ha hb
  have hcd := dof_tprod_ok hc hd
  have hac := dof_tprod_ok ha hc
  have hbd := dof_tprod_ok hb hd
  have hout := dof_tprod_ok hac hbd
  rw [denotValB_partial]
  simp only [ValExpr.inferSpaceCtx,hi₀,hi₁]
  rw [guard_ok (by
    intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨_,hab⟩
    · exact ⟨_,hcd⟩
    · exact ⟨_,hout⟩)]
  have hshape : ValueShape.matrices (numbers (orc ρ Γ Δ))
      (.tprod sa sb) (.tprod sc sd) a₀ a₁ := by
    simp only [ValueShape.matrices,ValueShape.tensor,
      dof_numbers _ _ _ ha,dof_numbers _ _ _ hb,dof_numbers _ _ _ hc,
      dof_numbers _ _ _ hd,hlen₀,hlen₁,and_self]
  simp only [he₀,he₁,ValValSem.bindArrays,ValValSem.bindArray,if_pos hshape,
    dof_numbers _ _ _ hb,dof_numbers _ _ _ hc,dof_numbers _ _ _ hd,
    dof_numbers _ _ _ hout,ValValSem.arrayOf]

theorem cob_tprod {V₀ V₁ : HSpace}
    {S₀ T₀ : List V₀.carrier} {S₁ T₁ : List V₁.carrier}
    {e₀ e₁ : ValExpr} {sa sb sc sd : ValSpace}
    (hi₀ : ValExpr.inferSpaceCtx Γ e₀ = .tprod sa sb)
    (hi₁ : ValExpr.inferSpaceCtx Γ e₁ = .tprod sc sd)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok S₀.length)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok S₀.length)
    (hc : sc.dofPartial (orc ρ Γ Δ) = .ok S₁.length)
    (hd : sd.dofPartial (orc ρ Γ Δ) = .ok S₁.length)
    (h₀ : CobResult orc ρ Γ Δ S₀ T₀ e₀)
    (h₁ : CobResult orc ρ Γ Δ S₁ T₁ e₁) :
    CobResult orc ρ Γ Δ (HSpace.tprodOfLists V₀ V₁ S₀ S₁)
      (HSpace.tprodOfLists V₀ V₁ T₀ T₁) (.vkrn e₀ e₁) := by
  obtain ⟨a₀,he₀,ht₀,hl₀,hr₀⟩ := h₀
  obtain ⟨a₁,he₁,ht₁,hl₁,hr₁⟩ := h₁
  refine ⟨_,eval_vkrn_square he₀ he₁ hi₀ hi₁ ha hb hc hd hl₀ hl₁,?_⟩
  apply partial_cob_cobAgree_tprodOfLists V₀ V₁ S₀ T₀ S₁ T₁ _ a₀ a₁
    ht₀ ht₁ hr₀ hr₁ (FlatArray.length_ofFn _ _)
  intro j i hj hi
  rw [FlatArray.get_ofFn_lt _ _ _ (Nat.raw_rowMajor_lt hj hi)]
  obtain ⟨hdiv,hmod⟩ := Nat.raw_rowMajor_div_mod hj hi
  rw [hdiv,hmod]

private theorem dof_dsum_ok {s t : ValSpace} {m n : Nat}
    (hs : s.dofPartial (orc ρ Γ Δ) = .ok m)
    (ht : t.dofPartial (orc ρ Γ Δ) = .ok n) :
    ValSpace.dofPartial (orc ρ Γ Δ) (.dsum s t) = .ok (m+n) := by
  rw [ValSpace.dofPartial, ValSpace.shpOfPartial, hs]
  simp [ht, bind, Except.bind, pure, Except.pure]

theorem eval_vblk_square {e₀ e₁ : ValExpr} {a₀ a₁ : FlatArray}
    {sa sb sc sd : ValSpace} {m n : Nat}
    (he₀ : denotValB_partial orc ρ Γ Δ e₀ = .ok (.array a₀))
    (he₁ : denotValB_partial orc ρ Γ Δ e₁ = .ok (.array a₁))
    (hi₀ : ValExpr.inferSpaceCtx Γ e₀ = .tprod sa sb)
    (hi₁ : ValExpr.inferSpaceCtx Γ e₁ = .tprod sc sd)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok m)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok m)
    (hc : sc.dofPartial (orc ρ Γ Δ) = .ok n)
    (hd : sd.dofPartial (orc ρ Γ Δ) = .ok n)
    (hlen₀ : a₀.length = m*m) (hlen₁ : a₁.length = n*n) :
    denotValB_partial orc ρ Γ Δ (.vblk e₀ e₁) =
      .ok (.array (FlatArray.ofFn ((m+n)*(m+n)) (fun i =>
        if i/(m+n) < m then
          if i%(m+n) < m then a₀.get (m*(i/(m+n))+i%(m+n)) else 0
        else if i%(m+n) < m then 0
        else a₁.get (n*(i/(m+n)-m)+(i%(m+n)-m))))) := by
  have hab := dof_tprod_ok ha hb
  have hcd := dof_tprod_ok hc hd
  have hac := dof_dsum_ok ha hc
  have hbd := dof_dsum_ok hb hd
  have hout := dof_tprod_ok hac hbd
  rw [denotValB_partial]
  simp only [ValExpr.inferSpaceCtx,hi₀,hi₁]
  rw [guard_ok (by
    intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨_,hab⟩
    · exact ⟨_,hcd⟩
    · exact ⟨_,hout⟩)]
  have hshape : ValueShape.matrices (numbers (orc ρ Γ Δ))
      (.tprod sa sb) (.tprod sc sd) a₀ a₁ := by
    simp only [ValueShape.matrices,ValueShape.tensor,
      dof_numbers _ _ _ ha,dof_numbers _ _ _ hb,dof_numbers _ _ _ hc,
      dof_numbers _ _ _ hd,hlen₀,hlen₁,and_self]
  simp only [he₀,he₁,ValValSem.bindArrays,ValValSem.bindArray,if_pos hshape,
    dof_numbers _ _ _ ha,dof_numbers _ _ _ hb,dof_numbers _ _ _ hd,
    dof_numbers _ _ _ hout,ValValSem.arrayOf]

theorem cob_dsum {V₀ V₁ : HSpace}
    {S₀ T₀ : List V₀.carrier} {S₁ T₁ : List V₁.carrier}
    {e₀ e₁ : ValExpr} {sa sb sc sd : ValSpace}
    (hi₀ : ValExpr.inferSpaceCtx Γ e₀ = .tprod sa sb)
    (hi₁ : ValExpr.inferSpaceCtx Γ e₁ = .tprod sc sd)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok S₀.length)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok S₀.length)
    (hc : sc.dofPartial (orc ρ Γ Δ) = .ok S₁.length)
    (hd : sd.dofPartial (orc ρ Γ Δ) = .ok S₁.length)
    (h₀ : CobResult orc ρ Γ Δ S₀ T₀ e₀)
    (h₁ : CobResult orc ρ Γ Δ S₁ T₁ e₁) :
    CobResult orc ρ Γ Δ (HSpace.dsumOfLists V₀ V₁ S₀ S₁)
      (HSpace.dsumOfLists V₀ V₁ T₀ T₁) (.vblk e₀ e₁) := by
  obtain ⟨a₀,he₀,ht₀,hl₀,hr₀⟩ := h₀
  obtain ⟨a₁,he₁,ht₁,hl₁,hr₁⟩ := h₁
  refine ⟨_,eval_vblk_square he₀ he₁ hi₀ hi₁ ha hb hc hd hl₀ hl₁,?_⟩
  apply partial_cob_cobAgree_dsumOfLists V₀ V₁ S₀ T₀ S₁ T₁ _ a₀ a₁
    ht₀ ht₁ hr₀ hr₁ (FlatArray.length_ofFn _ _)
  intro j i hj hi
  rw [FlatArray.get_ofFn_lt _ _ _ (Nat.raw_rowMajor_lt hj hi)]
  obtain ⟨hdiv,hmod⟩ := Nat.raw_rowMajor_div_mod hj hi
  rw [hdiv,hmod]

end GLang.PartialAdequacy
