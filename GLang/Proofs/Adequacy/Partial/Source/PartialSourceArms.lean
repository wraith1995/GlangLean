import GLang.Proofs.Adequacy.Agreement

/-! Primitive source-agreement arms for the actual error-preserving evaluator. -/
namespace GLang.PartialAdequacy
open PartialValueEval

variable {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
  {Ds : List DVal} {Γ : List ValTy} {Δ : List ValValSem}

/-- Once a dimension has succeeded, source coordinates are precisely the
usual finite linear combination. -/
theorem agree_space_iff {s : Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {a : FlatArray} {n : Nat}
    (hdim : sv.dofPartial (orc ρ Γ Δ) = .ok n) :
    Agree orc σ ρ Ds Γ Δ (.space s) (.space sv) B x (.array a) ↔
      (B.atSpace (denotSpaceAux σ Ds s)).length = n ∧ a.length = n ∧
      x.atSpace (denotSpaceAux σ Ds s) =
        ∑ i : Fin n, a.get i.val • (B.atSpace (denotSpaceAux σ Ds s)).getD i.val 0 := by
  simp only [Agree, hdim, Except.ok.injEq]
  constructor
  · rintro ⟨m, hm, h⟩
    subst m
    exact h
  · intro h
    exact ⟨n, rfl, h⟩

private theorem guard_one {sv : ValSpace} {n : Nat}
    (h : sv.dofPartial (orc ρ Γ Δ) = .ok n)
    (f : FFSOracle → Except DimError ValValSem) :
    withDimensions (orc ρ Γ Δ) [sv] f = f (numbers (orc ρ Γ Δ)) := by
  simp [withDimensions, dimensions, h, bind, Except.bind]

theorem zero {s : Space} {sv : ValSpace} {B : BasisDenot} {n : Nat}
    (hdim : sv.dofPartial (orc ρ Γ Δ) = .ok n)
    (hB : (B.atSpace (denotSpaceAux σ Ds s)).length = n) :
    ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) B
      (.hil ⟨denotSpaceAux σ Ds s, 0⟩)
      (denotValB_partial orc ρ Γ Δ (.zero sv)) := by
  rw [denotValB_partial, ValExpr.inferSpaceCtx, guard_one hdim]
  rw [dof_numbers _ _ _ hdim]
  refine ⟨_, rfl, ?_⟩
  simp only [ValValSem.arrayOf, Agree]
  refine ⟨n, hdim, hB, FlatArray.length_ofFn _ _, ?_⟩
  rw [DVal.atSpace_hil_self]
  symm
  apply Finset.sum_eq_zero
  intro i _
  rw [FlatArray.get_ofFn_lt _ _ _ i.isLt, zero_smul]

theorem real (r : ℝ) :
    ResultAgree orc σ ρ Ds Γ Δ (.space .real) (.space .real)
      (.vecs HSpace.real [1]) (.hil ⟨HSpace.real, r⟩)
      (denotValB_partial orc ρ Γ Δ (.rlit r)) := by
  have hd : ValSpace.dofPartial (orc ρ Γ Δ) .real = .ok 1 := by
    simp [ValSpace.dofPartial, ValSpace.shpOfPartial, bind, Except.bind, pure, Except.pure]
  rw [denotValB_partial, ValExpr.inferSpaceCtx, guard_one hd]
  rw [dof_numbers _ _ _ hd]
  refine ⟨_, rfl, ?_⟩
  simp only [ValValSem.arrayOf, Agree, denotSpaceAux,
    BasisDenot.atSpace_vecs_self, DVal.atSpace_hil_self]
  refine ⟨1, hd, rfl, FlatArray.length_ofFn _ _, ?_⟩
  rw [Fin.sum_univ_one]
  change r = r * 1
  ring

theorem add {s : Space} {sv sv₀ sv₁ : ValSpace} {B : BasisDenot}
    {x₀ x₁ : DVal} {e₀ e₁ : ValExpr} {n : Nat}
    (hdim : sv.dofPartial (orc ρ Γ Δ) = .ok n)
    (hB : (B.atSpace (denotSpaceAux σ Ds s)).length = n)
    (hx₀ : x₀.matchesShape (.hil (denotSpaceAux σ Ds s)))
    (hx₁ : x₁.matchesShape (.hil (denotSpaceAux σ Ds s)))
    (h₀ : ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv₀) B x₀
      (denotValB_partial orc ρ Γ Δ e₀))
    (h₁ : ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv₁) B x₁
      (denotValB_partial orc ρ Γ Δ e₁)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) B (x₀.addAt x₁)
      (denotValB_partial orc ρ Γ Δ (.vadd sv e₀ e₁)) := by
  obtain ⟨v₀, he₀, h₀⟩ := h₀
  obtain ⟨v₁, he₁, h₁⟩ := h₁
  cases v₀ with
  | fn _ _ => simp only [Agree] at h₀
  | array a₀ =>
    cases v₁ with
    | fn _ _ => simp only [Agree] at h₁
    | array a₁ =>
      simp only [Agree] at h₀ h₁
      obtain ⟨n₀, _, hb₀, ha₀, hc₀⟩ := h₀
      obtain ⟨n₁, _, hb₁, ha₁, hc₁⟩ := h₁
      have hn₀ : n₀ = n := hb₀.symm.trans hB
      have hn₁ : n₁ = n := hb₁.symm.trans hB
      subst n₀; subst n₁
      rw [hB] at ha₀ ha₁ hc₀ hc₁
      rw [denotValB_partial, guard_one hdim, he₀, he₁]
      simp only [ValValSem.bindArrays, ValValSem.bindArray, dof_numbers _ _ _ hdim,
        ha₀, ha₁, dite_true]
      refine ⟨_, rfl, ?_⟩
      simp only [Agree]
      refine ⟨n, hdim, hB, rfl, ?_⟩
      rw [DVal.addAt_atSpace_eq_add hx₀ hx₁, hc₀, hc₁, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← add_smul, FlatArray.zipWith, FlatArray.get_ofFn_lt _ _ _ i.isLt]

theorem scale {s : Space} {sv : ValSpace} {B : BasisDenot}
    {r : ℝ} {x : (denotSpaceAux σ Ds s).carrier} {e₀ e₁ : ValExpr}
    (hinfer : ValExpr.inferSpaceCtx Γ e₁ = sv)
    (h₀ : ResultAgree orc σ ρ Ds Γ Δ (.space .real) (.space .real)
      (.vecs HSpace.real [1]) (.hil ⟨HSpace.real, r⟩)
      (denotValB_partial orc ρ Γ Δ e₀))
    (h₁ : ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) B
      (.hil ⟨denotSpaceAux σ Ds s, x⟩) (denotValB_partial orc ρ Γ Δ e₁)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) B
      (.hil ⟨denotSpaceAux σ Ds s, r • x⟩)
      (denotValB_partial orc ρ Γ Δ (.scale e₀ e₁)) := by
  obtain ⟨v₀, he₀, h₀⟩ := h₀
  obtain ⟨v₁, he₁, h₁⟩ := h₁
  cases v₀ with
  | fn _ _ => simp only [Agree] at h₀
  | array a₀ =>
    cases v₁ with
    | fn _ _ => simp only [Agree] at h₁
    | array a₁ =>
      simp only [Agree, denotSpaceAux, BasisDenot.atSpace_vecs_self,
        DVal.atSpace_hil_self] at h₀
      obtain ⟨n₀, _, hb₀, ha₀, hc₀⟩ := h₀
      have hn₀ : n₀ = 1 := hb₀.symm
      subst n₀
      simp only [List.length_singleton] at hc₀ ha₀
      change r = ∑ i : Fin 1, a₀.get i.val • ([1] : List ℝ).getD i.val 0 at hc₀
      rw [Fin.sum_univ_one] at hc₀
      have hr : r = a₀.get 0 := by simpa using hc₀
      simp only [Agree] at h₁
      obtain ⟨n, hd, hb, ha, hc⟩ := h₁
      rw [DVal.atSpace_hil_self] at hc
      rw [denotValB_partial, hinfer, guard_one hd, he₀, he₁]
      have hs : ValueShape.scale (numbers (orc ρ Γ Δ)) sv a₀ a₁ :=
        ⟨ha₀, ha.trans (dof_numbers _ _ _ hd).symm⟩
      simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hs,
        ValExpr.inferSpaceCtx, hinfer, dof_numbers _ _ _ hd]
      refine ⟨_, rfl, ?_⟩
      simp only [Agree, ValValSem.arrayOf]
      refine ⟨n, hd, hb, FlatArray.length_ofFn _ _, ?_⟩
      rw [DVal.atSpace_hil_self, hr, hc, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, FlatArray.get_ofFn_lt _ _ _ i.isLt]

open scoped TensorProduct

private theorem partial_sum_prod_left
    {iota A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset iota) (g : iota -> A) :
    (∑ i ∈ s, (g i, (0 : B))) = (∑ i ∈ s, g i, 0) := by
  classical
  induction s using Finset.induction with
  | empty => apply Prod.ext <;> simp
  | insert a s ha ih => apply Prod.ext <;> simp [ha, ih]

private theorem partial_sum_prod_right
    {iota A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset iota) (g : iota -> B) :
    (∑ i ∈ s, ((0 : A), g i)) = (0, ∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => apply Prod.ext <;> simp
  | insert a s ha ih => apply Prod.ext <;> simp [ha, ih]

private theorem partial_dsum_getD_left
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) (i : Nat) (hi : i < vs0.length) :
    (HSpace.dsumOfLists V0 V1 vs0 vs1).getD i 0 =
      (vs0.getD i 0, 0) := by
  unfold HSpace.dsumOfLists
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  change (vs0.map (fun x => (x, 0))).getD i ((0, 0)) = _
  rw [show ((0, 0) : V0.carrier × V1.carrier) =
      (fun x => (x, 0)) 0 by rfl, List.getD_map]

private theorem partial_dsum_getD_right
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

private theorem partial_dsum_coeff_sum
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
    rw [← partial_sum_prod_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.val_castAdd,
      partial_dsum_getD_left _ _ _ _ _ i.isLt]
    apply Prod.ext <;> simp
  have h1 : (∑ i : Fin vs1.length,
      c (Fin.natAdd vs0.length i) •
        (HSpace.dsumOfLists V0 V1 vs0 vs1).getD
          (Fin.natAdd vs0.length i) 0) =
      (0, ∑ i : Fin vs1.length,
        c (Fin.natAdd vs0.length i) • vs1.getD i 0) := by
    rw [← partial_sum_prod_right]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.val_natAdd,
      partial_dsum_getD_right _ _ _ _ _ i.isLt]
    apply Prod.ext <;> simp
  rw [h0, h1]
  ext <;> simp

private theorem partial_sum_range_mul_div_mod
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

private theorem partial_tprod_coeff_sum_range
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
      have hklist : k <
          (HSpace.tprodOfLists V0 V1 vs0 vs1).length := by
        rw [HSpace.tprodOfLists_length]
        exact hk'
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hklist,
        HSpace.tprodOfLists_getElem vs0 vs1 k hk' hnpos]
      have hi : k / vs1.length < vs0.length :=
        (Nat.div_lt_iff_lt_mul hnpos).2 hk'
      have hj : k % vs1.length < vs1.length :=
        Nat.mod_lt _ hnpos
      rw [List.getD_eq_getElem vs0 0 hi,
        List.getD_eq_getElem vs1 0 hj]
      simp only [Option.getD_some]
    _ = ∑ i ∈ Finset.range vs0.length,
          ∑ j ∈ Finset.range vs1.length,
          (c0 i * c1 j) • (vs0.getD i 0 ⊗ₜ[ℝ] vs1.getD j 0) := by
      exact partial_sum_range_mul_div_mod vs0.length vs1.length
        (fun i j => (c0 i * c1 j) •
          (vs0.getD i 0 ⊗ₜ[ℝ] vs1.getD j 0))
    _ = (∑ i ∈ Finset.range vs0.length,
          c0 i • vs0.getD i 0) ⊗ₜ[ℝ]
        (∑ j ∈ Finset.range vs1.length,
          c1 j • vs1.getD j 0) := by
      rw [TensorProduct.sum_tmul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [TensorProduct.smul_tmul_smul]

private theorem partial_tprod_coeff_sum
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
  exact partial_tprod_coeff_sum_range V0 V1 vs0 vs1 c0 c1

theorem Agree.array {s : Space} {sv : ValSpace} {B : BasisDenot} {x : DVal}
    {v : ValValSem} (h : Agree orc σ ρ Ds Γ Δ (.space s) (.space sv) B x v) :
    ∃ a n, v = .array a ∧ sv.dofPartial (orc ρ Γ Δ) = .ok n ∧
      (B.atSpace (denotSpaceAux σ Ds s)).length = n ∧ a.length = n ∧
      x.atSpace (denotSpaceAux σ Ds s) =
        ∑ i : Fin n, a.get i.val • (B.atSpace (denotSpaceAux σ Ds s)).getD i.val 0 := by
  cases v with
  | fn _ _ => simp only [Agree] at h
  | array a =>
    simp only [Agree] at h
    obtain ⟨n, h⟩ := h
    exact ⟨a,n,rfl,h⟩

private theorem guard_pair {sv₀ sv₁ : ValSpace} {n₀ n₁ : Nat}
    (h₀ : sv₀.dofPartial (orc ρ Γ Δ) = .ok n₀)
    (h₁ : sv₁.dofPartial (orc ρ Γ Δ) = .ok n₁)
    (f : FFSOracle → Except DimError ValValSem) :
    withDimensions (orc ρ Γ Δ) [sv₀,sv₁] f = f (numbers (orc ρ Γ Δ)) := by
  simp [withDimensions, dimensions, h₀, h₁, bind, Except.bind]

theorem dsum {s₀ s₁ : Space} {sv₀ sv₁ : ValSpace} {B₀ B₁ : BasisDenot}
    {x₀ : (denotSpaceAux σ Ds s₀).carrier} {x₁ : (denotSpaceAux σ Ds s₁).carrier}
    {e₀ e₁ : ValExpr}
    (hi₀ : ValExpr.inferSpaceCtx Γ e₀ = sv₀)
    (hi₁ : ValExpr.inferSpaceCtx Γ e₁ = sv₁)
    (h₀ : ResultAgree orc σ ρ Ds Γ Δ (.space s₀) (.space sv₀) B₀
      (.hil ⟨denotSpaceAux σ Ds s₀, x₀⟩) (denotValB_partial orc ρ Γ Δ e₀))
    (h₁ : ResultAgree orc σ ρ Ds Γ Δ (.space s₁) (.space sv₁) B₁
      (.hil ⟨denotSpaceAux σ Ds s₁, x₁⟩) (denotValB_partial orc ρ Γ Δ e₁)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space (.dsum s₀ s₁)) (.space (.dsum sv₀ sv₁))
      (.vecs (HSpace.dsum (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁))
        (HSpace.dsumOfLists _ _ (B₀.atSpace (denotSpaceAux σ Ds s₀))
          (B₁.atSpace (denotSpaceAux σ Ds s₁))))
      (.hil ⟨HSpace.dsum (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁), (x₀,x₁)⟩)
      (denotValB_partial orc ρ Γ Δ (.dsumE e₀ e₁)) := by
  obtain ⟨v₀, he₀, h₀⟩ := h₀
  obtain ⟨v₁, he₁, h₁⟩ := h₁
  obtain ⟨a₀,n₀,rfl,hd₀,hb₀,ha₀,hc₀⟩ := h₀.array
  obtain ⟨a₁,n₁,rfl,hd₁,hb₁,ha₁,hc₁⟩ := h₁.array
  rw [DVal.atSpace_hil_self] at hc₀ hc₁
  have hd : ValSpace.dofPartial (orc ρ Γ Δ) (.dsum sv₀ sv₁) = .ok (n₀+n₁) := by
    rw [ValSpace.dofPartial, ValSpace.shpOfPartial, hd₀]
    simp [hd₁, bind, Except.bind, pure, Except.pure]
  rw [denotValB_partial, hi₀, hi₁, guard_pair hd₀ hd₁, he₀, he₁]
  have hs : ValueShape.pair (numbers (orc ρ Γ Δ)) sv₀ sv₁ a₀ a₁ :=
    ⟨ha₀.trans (dof_numbers _ _ _ hd₀).symm, ha₁.trans (dof_numbers _ _ _ hd₁).symm⟩
  simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hs,
    ValExpr.inferSpaceCtx, hi₀, hi₁, dof_numbers _ _ _ hd, dof_numbers _ _ _ hd₀]
  refine ⟨_,rfl,?_⟩
  simp only [Agree, denotSpaceAux, BasisDenot.atSpace_vecs_self, ValValSem.arrayOf]
  refine ⟨n₀+n₁, hd, ?_, FlatArray.length_ofFn _ _, ?_⟩
  · rw [HSpace.dsumOfLists_length, hb₀, hb₁]
  · rw [DVal.atSpace_hil_self]
    change (x₀,x₁) = ∑ i : Fin (n₀+n₁),
      (FlatArray.ofFn (n₀+n₁) (fun j => if j < n₀ then a₀.get j else a₁.get (j-n₀))).get i.val •
        (HSpace.dsumOfLists _ _ (B₀.atSpace (denotSpaceAux σ Ds s₀))
          (B₁.atSpace (denotSpaceAux σ Ds s₁))).getD i.val 0
    rw [partial_dsum_coeff_sum _ _ _ _ hb₀ hb₁
      (fun i : Fin (n₀+n₁) => (FlatArray.ofFn (n₀+n₁)
        (fun j => if j < n₀ then a₀.get j else a₁.get (j-n₀))).get i.val)]
    apply Prod.ext
    · simp only
      rw [hc₀]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [FlatArray.get_ofFn_lt _ _ _ (by simp only [Fin.val_castAdd]; omega)]
      simp [i.isLt]
    · simp only
      rw [hc₁]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [FlatArray.get_ofFn_lt _ _ _ (by simp only [Fin.val_natAdd]; omega)]
      simp [show ¬ n₀ + i.val < n₀ by omega]

theorem tprod {s₀ s₁ : Space} {sv₀ sv₁ : ValSpace} {B₀ B₁ : BasisDenot}
    {x₀ : (denotSpaceAux σ Ds s₀).carrier} {x₁ : (denotSpaceAux σ Ds s₁).carrier}
    {e₀ e₁ : ValExpr}
    (hi₀ : ValExpr.inferSpaceCtx Γ e₀ = sv₀)
    (hi₁ : ValExpr.inferSpaceCtx Γ e₁ = sv₁)
    (h₀ : ResultAgree orc σ ρ Ds Γ Δ (.space s₀) (.space sv₀) B₀
      (.hil ⟨denotSpaceAux σ Ds s₀, x₀⟩) (denotValB_partial orc ρ Γ Δ e₀))
    (h₁ : ResultAgree orc σ ρ Ds Γ Δ (.space s₁) (.space sv₁) B₁
      (.hil ⟨denotSpaceAux σ Ds s₁, x₁⟩) (denotValB_partial orc ρ Γ Δ e₁)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space (.tprod s₀ s₁)) (.space (.tprod sv₀ sv₁))
      (.vecs (HSpace.tprod (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁))
        (HSpace.tprodOfLists _ _ (B₀.atSpace (denotSpaceAux σ Ds s₀))
          (B₁.atSpace (denotSpaceAux σ Ds s₁))))
      (.hil ⟨HSpace.tprod (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁), (x₀ ⊗ₜ[ℝ] x₁)⟩)
      (denotValB_partial orc ρ Γ Δ (.tprodE e₀ e₁)) := by
  obtain ⟨v₀, he₀, h₀⟩ := h₀
  obtain ⟨v₁, he₁, h₁⟩ := h₁
  obtain ⟨a₀,n₀,rfl,hd₀,hb₀,ha₀,hc₀⟩ := h₀.array
  obtain ⟨a₁,n₁,rfl,hd₁,hb₁,ha₁,hc₁⟩ := h₁.array
  rw [DVal.atSpace_hil_self] at hc₀ hc₁
  have hd : ValSpace.dofPartial (orc ρ Γ Δ) (.tprod sv₀ sv₁) = .ok (n₀*n₁) := by
    rw [ValSpace.dofPartial, ValSpace.shpOfPartial, hd₀]
    simp [hd₁, bind, Except.bind, pure, Except.pure]
  rw [denotValB_partial, hi₀, hi₁, guard_pair hd₀ hd₁, he₀, he₁]
  have hs : ValueShape.pair (numbers (orc ρ Γ Δ)) sv₀ sv₁ a₀ a₁ :=
    ⟨ha₀.trans (dof_numbers _ _ _ hd₀).symm, ha₁.trans (dof_numbers _ _ _ hd₁).symm⟩
  simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hs,
    ValExpr.inferSpaceCtx, hi₀, hi₁, dof_numbers _ _ _ hd, dof_numbers _ _ _ hd₁]
  refine ⟨_,rfl,?_⟩
  simp only [Agree, denotSpaceAux, BasisDenot.atSpace_vecs_self, ValValSem.arrayOf]
  refine ⟨n₀*n₁, hd, ?_, FlatArray.length_ofFn _ _, ?_⟩
  · rw [HSpace.tprodOfLists_length, hb₀, hb₁]
  · rw [DVal.atSpace_hil_self]
    change x₀ ⊗ₜ[ℝ] x₁ = ∑ i : Fin (n₀*n₁),
      (FlatArray.ofFn (n₀*n₁) (fun j => a₀.get (j/n₁) * a₁.get (j%n₁))).get i.val •
        (HSpace.tprodOfLists _ _ (B₀.atSpace (denotSpaceAux σ Ds s₀))
          (B₁.atSpace (denotSpaceAux σ Ds s₁))).getD i.val 0
    rw [partial_tprod_coeff_sum _ _ _ _ hb₀ hb₁
      (fun i : Fin (n₀*n₁) => (FlatArray.ofFn (n₀*n₁)
        (fun j => a₀.get (j/n₁) * a₁.get (j%n₁))).get i.val)
      a₀.get a₁.get (fun i => FlatArray.get_ofFn_lt _ _ _ i.isLt)]
    rw [hc₀, hc₁]

private theorem partial_fin_sum_cast_of_eq
    {M : Type} [AddCommMonoid M] {n m : Nat}
    (h : n = m) (f : Fin n -> M) :
    (∑ i, f i) = ∑ i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  rfl

private theorem partial_dualOfList_getD_eq_dualVec
    (V : HSpace) (vs : List V.carrier) {i : Nat}
    (hi : i < vs.length) :
    (V.dualOfList vs).getD i 0 = V.dualVec vs ⟨i, hi⟩ := by
  have hdualLen : (V.dualOfList vs).length = vs.length :=
    HSpace.dualOfList_length V vs
  have hiDual : i < (V.dualOfList vs).length := hdualLen.symm ▸ hi
  rw [List.getD_eq_getElem (V.dualOfList vs) 0 hiDual]
  change (V.dualOfList vs).get ⟨i, hiDual⟩ = _
  refine (List.get_of_eq
    (HSpace.dualOfList_eq_finRange_map V vs) ⟨i, hiDual⟩).trans ?_
  simp

private theorem partial_tprodOfLists_diag_sum
    (W : HSpace) (ws : List W.carrier) {N : Nat}
    (hl : ws.length = N) (c : Fin (N * N) -> ℝ)
    (hc : forall k : Fin (N * N),
      c k = if (k : Nat) / N = (k : Nat) % N then 1 else 0) :
    (∑ k, c k • (HSpace.tprodOfLists W W ws ws).getD k 0) =
      ∑ i : Fin N, ws.getD i 0 ⊗ₜ[ℝ] ws.getD i 0 := by
  subst hl
  simp only [hc]
  rw [Fin.sum_univ_eq_sum_range
      (fun k => (if k / ws.length = k % ws.length then (1 : ℝ) else 0) •
        (HSpace.tprodOfLists W W ws ws).getD k 0),
    Fin.sum_univ_eq_sum_range
      (fun i => ws.getD i 0 ⊗ₜ[ℝ] ws.getD i 0)]
  by_cases hn : ws.length = 0
  · rw [hn]
    simp
  have hnpos : 0 < ws.length := Nat.pos_of_ne_zero hn
  calc
    (∑ k ∈ Finset.range (ws.length * ws.length),
      (if k / ws.length = k % ws.length then (1 : ℝ) else 0) •
        (HSpace.tprodOfLists W W ws ws).getD k 0) =
        ∑ k ∈ Finset.range (ws.length * ws.length),
          (if k / ws.length = k % ws.length then (1 : ℝ) else 0) •
            (ws.getD (k / ws.length) 0 ⊗ₜ[ℝ]
              ws.getD (k % ws.length) 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hklist : k < (HSpace.tprodOfLists W W ws ws).length := by
        rw [HSpace.tprodOfLists_length]
        exact hk'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklist,
        HSpace.tprodOfLists_getElem ws ws k hk' hnpos]
      have hi : k / ws.length < ws.length :=
        (Nat.div_lt_iff_lt_mul hnpos).2 hk'
      have hj : k % ws.length < ws.length := Nat.mod_lt _ hnpos
      rw [List.getD_eq_getElem ws 0 hi, List.getD_eq_getElem ws 0 hj]
      simp only [Option.getD_some]
    _ = ∑ i ∈ Finset.range ws.length, ∑ j ∈ Finset.range ws.length,
          (if i = j then (1 : ℝ) else 0) •
            (ws.getD i 0 ⊗ₜ[ℝ] ws.getD j 0) := by
      exact partial_sum_range_mul_div_mod ws.length ws.length
        (fun i j => (if i = j then (1 : ℝ) else 0) •
          (ws.getD i 0 ⊗ₜ[ℝ] ws.getD j 0))
    _ = ∑ i ∈ Finset.range ws.length,
        ws.getD i 0 ⊗ₜ[ℝ] ws.getD i 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, hi, if_true]

theorem inner {s : Space} {sv : ValSpace} {n : Nat}
    {vs : List (denotSpaceAux σ Ds s).carrier}
    (hd : sv.dofPartial (orc ρ Γ Δ) = .ok n)
    (hlen : vs.length = n)
    (hb : IsListBasis (denotSpaceAux σ Ds s) vs)
    (horth : ∀ i j : Fin vs.length,
      (denotSpaceAux σ Ds s).innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0) :
    ResultAgree orc σ ρ Ds Γ Δ (.space (.tprod (.dual s) (.dual s)))
      (.space (.tprod sv sv))
      (.vecs (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s))
          (HSpace.dual (denotSpaceAux σ Ds s)))
        (HSpace.tprodOfLists _ _ ((denotSpaceAux σ Ds s).dualOfList vs)
          ((denotSpaceAux σ Ds s).dualOfList vs)))
      ((denotSpaceAux σ Ds s).innerTensor (denotSpaceAux σ Ds s).innerProduct)
      (denotValB_partial orc ρ Γ Δ (.idelta sv)) := by
  have hd₂ : ValSpace.dofPartial (orc ρ Γ Δ) (.tprod sv sv) = .ok (n*n) := by
    rw [ValSpace.dofPartial, ValSpace.shpOfPartial, hd]
    simp [bind, Except.bind, pure, Except.pure]
  rw [denotValB_partial, guard_one hd]
  simp only [ValExpr.inferSpaceCtx, dof_numbers _ _ _ hd₂, dof_numbers _ _ _ hd]
  refine ⟨_,rfl,?_⟩
  simp only [Agree, denotSpaceAux, BasisDenot.atSpace_vecs_self, ValValSem.arrayOf]
  refine ⟨n*n,hd₂,?_,FlatArray.length_ofFn _ _,?_⟩
  · rw [HSpace.tprodOfLists_length, HSpace.dualOfList_length, hlen]
  · change ((denotSpaceAux σ Ds s).innerTensor (denotSpaceAux σ Ds s).innerProduct).atSpace
      (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s))
        (HSpace.dual (denotSpaceAux σ Ds s))) =
      ∑ i : Fin (n*n), (FlatArray.ofFn (n*n) (fun j =>
        if n = 0 then 0 else if j < n*n then
          if j/n = j%n ∧ j/n < n then 1 else 0 else 0)).get i.val •
        (HSpace.tprodOfLists _ _ ((denotSpaceAux σ Ds s).dualOfList vs)
          ((denotSpaceAux σ Ds s).dualOfList vs)).getD i.val 0
    rw [IsListBasis.innerTensor_atSpace_eq_sum_dual_tmul hb horth]
    rw [partial_tprodOfLists_diag_sum _ _
      ((HSpace.dualOfList_length _ _).trans hlen) _ ?_]
    · rw [partial_fin_sum_cast_of_eq hlen]
      apply Finset.sum_congr rfl
      intro i _
      rw [partial_dualOfList_getD_eq_dualVec _ _ (by rw [hlen]; exact i.isLt)]
      rfl
    · intro k
      rw [FlatArray.get_ofFn_lt _ _ _ k.isLt]
      have hn : n ≠ 0 := by
        intro h
        have hk := k.isLt
        have hz : n*n = 0 := by simp [h]
        omega
      rw [if_neg hn, if_pos k.isLt]
      simp only [(Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hn)).mpr k.isLt, and_true]

end GLang.PartialAdequacy
