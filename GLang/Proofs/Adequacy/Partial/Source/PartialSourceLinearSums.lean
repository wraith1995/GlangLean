import GLang.Proofs.Adequacy.Raw.RawLlamSource
import GLang.Proofs.Adequacy.Raw.RawSpaceFFSAdequacy
import GLang.Proofs.Value.Partial.PartialValueSumAt
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceArms
import Mathlib.Data.Fin.Tuple.Take
namespace GLang.PartialAdequacy
open scoped BigOperators TensorProduct
open PartialValueEval
private theorem sequenceArrays_ok
    (as : List FlatArray) :
    ValValSem.sequenceArrays (as.map (fun a =>
      (Except.ok (.array a) : Except DimError ValValSem))) = .ok as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, ValValSem.sequenceArrays, ih]

theorem vsum_rows_ok
    {orc : PartialFFSOracleSem} {rho : ValEnvSem} {sIndex : ValSpace}
    {n outN count : Nat}
    (hindex : sIndex.dofPartial (orc rho [] []) = .ok count) (hn : count ≤ n)
    (summand : Fin n → ValExpr)
    (rows : Fin (count) → FlatArray)
    (heval : forall i,
      denotValB_partial orc rho [] [] (summand (Fin.castLE hn i)) =
        .ok (.array (rows i)))
    (hinfer : (ValExpr.inferSpaceCtx [] (.vsum sIndex (List.ofFn summand))).dofPartial
        (orc rho [] []) = .ok outN)
    (hrows : ∀ i, (rows i).length = outN) :
    denotValB_partial orc rho [] []
        (.vsum sIndex (List.ofFn summand)) =
      .ok (.array (FlatArray.ofFn outN
        (fun j => ∑ i : Fin (count),
          (rows i).get j))) := by
  rw [denotValB_partial]
  have hg : dimensions (orc rho [] [])
      [sIndex, ValExpr.inferSpaceCtx [] (.vsum sIndex (List.ofFn summand))] = .ok () := by
    simp [dimensions, hindex, hinfer, bind, Except.bind]
  rw [withDimensions, hg]
  dsimp only
  rw [dof_numbers _ _ _ hindex, dof_numbers _ _ _ hinfer]
  simp only [List.length_ofFn, if_pos hn]
  rw [← Fin.ofFn_take_eq_take_ofFn hn]
  simp only [List.attach_map_val, List.map_ofFn, Fin.take_apply,
    Function.comp_apply]
  rw [show
      List.ofFn (denotValB_partial orc rho [] [] ∘
        Fin.take (count) hn summand) =
          List.ofFn (fun i =>
            (Except.ok (.array (rows i)) : Except DimError ValValSem)) by
        apply congrArg List.ofFn
        funext i
        exact heval i]
  have hseq : ValValSem.sequenceArrays
      (List.ofFn fun i =>
        (Except.ok (.array (rows i)) : Except DimError ValValSem)) =
      .ok (List.ofFn rows) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      sequenceArrays_ok (List.ofFn rows)
  rw [hseq]
  simp only
  have hfamily : ValueShape.family (count) outN
      (List.ofFn rows) := by
    constructor
    · simp
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hrows i
  rw [if_pos hfamily]
  congr 2
  funext j
  let f : Nat → ℝ := fun i => match (List.ofFn rows)[i]? with
    | some a => a.get j
    | none => 0
  calc
    (∑ i ∈ Finset.range (count),
        match (List.ofFn rows)[i]? with
        | some a => a.get j
        | none => 0) =
        ∑ i : Fin (count), f i.val := by
          exact (Fin.sum_univ_eq_sum_range f _).symm
    _ = ∑ i : Fin (count),
        (rows i).get j := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [f, List.getElem?_ofFn, i.isLt, ↓reduceDIte]

theorem raw_llam_linearFunctional_dual_sum
    (V : HSpace) (vs : List V.carrier) {N : Nat}
    (hlen : vs.length = N) (hvs : IsListBasis V vs)
    (phi : V.carrier →ₗ[ℝ] ℝ) (coeff : Fin N → ℝ)
    (hcol : forall i : Fin N, phi (vs.getD i.val 0) = coeff i) :
    phi = ∑ i : Fin N, coeff i • (V.dualOfList vs).getD i.val 0 := by
  subst N
  apply LinearMap.ext
  intro x
  change phi x = _
  calc
    phi x = ∑ i : Fin vs.length,
        (V.dualVec vs i x) • phi (vs.get i) :=
      hvs.map_eq_sum_dual_smul (W := HSpace.real) phi x
    _ = _ := by
      rw [LinearMap.sum_apply]
      apply Fintype.sum_congr
      intro i
      have hiDual : i.val < (V.dualOfList vs).length := by
        rw [HSpace.dualOfList_length]
        exact i.isLt
      have hdual : (V.dualOfList vs).getD i.val 0 =
          V.dualVec vs i := by
        rw [List.getD_eq_getElem _ _ hiDual]
        refine (List.get_of_eq
          (HSpace.dualOfList_eq_finRange_map V vs) ⟨i.val, hiDual⟩).trans ?_
        simp
      have hc : phi (vs.get i) = coeff i := by
        simpa [List.getD_eq_getElem vs 0 i.isLt] using hcol i
      rw [hdual, LinearMap.smul_apply, hc]
      change (V.dualVec vs i x) * coeff i =
        coeff i * V.dualVec vs i x
      exact mul_comm _ _

theorem raw_llam_sum_range_mul_div_mod
    {A : Type} [AddCommMonoid A]
    (m n : Nat) (g : Nat → Nat → A) :
    (∑ k ∈ Finset.range (m * n), g (k / n) (k % n)) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, g i j := by
  rw [← Fin.sum_univ_eq_sum_range, ← finProdFinEquiv.sum_comp]
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

/-- Row-major coefficient form of the tensor that encodes a linear map. -/
theorem raw_llam_linearMap_tensor_coeff_sum (V W : HSpace)
    (vs : List V.carrier) (ws : List W.carrier)
    (hvs : IsListBasis V vs) (f : V.carrier →ₗ[ℝ] W.carrier)
    (a : Nat → Nat → ℝ)
    (hrow : ∀ i < vs.length,
      f (vs.getD i 0) = ∑ j ∈ Finset.range ws.length,
        a i j • ws.getD j 0) :
    (dualTensorHomEquiv ℝ V.carrier W.carrier).symm f =
      ∑ k ∈ Finset.range
          (HSpace.tprodOfLists (HSpace.dual V) W
            (V.dualOfList vs) ws).length,
        a (k / ws.length) (k % ws.length) •
          (HSpace.tprodOfLists (HSpace.dual V) W
            (V.dualOfList vs) ws).getD k 0 := by
  rw [hvs.dualTensorHomEquiv_symm_eq_sum₂ (ws := ws) f
    (fun i j => a i.val j.val) (fun i => by
      have hc := hrow i.val i.isLt
      rw [← Fin.sum_univ_eq_sum_range] at hc
      simpa [List.getD_eq_getElem vs 0 i.isLt,
        List.getD_eq_getElem ws 0] using hc)]
  calc
    (∑ i : Fin vs.length, ∑ j : Fin ws.length,
        a i.val j.val • (V.dualVec vs i ⊗ₜ[ℝ] ws.get j)) =
        ∑ i ∈ Finset.range vs.length, ∑ j ∈ Finset.range ws.length,
          a i j • ((V.dualOfList vs).getD i 0 ⊗ₜ[ℝ] ws.getD j 0) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Fintype.sum_congr
      intro i
      rw [← Fin.sum_univ_eq_sum_range]
      apply Fintype.sum_congr
      intro j
      rw [RawSpaceFFS.dualOfList_getD_eq_dualVec V vs i.isLt,
        List.getD_eq_getElem ws 0 j.isLt]
      congr
    _ = ∑ k ∈ Finset.range (vs.length * ws.length),
        a (k / ws.length) (k % ws.length) •
          ((V.dualOfList vs).getD (k / ws.length) 0 ⊗ₜ[ℝ]
            ws.getD (k % ws.length) 0) := by
      exact (raw_llam_sum_range_mul_div_mod vs.length ws.length
        (fun i j => a i j •
          ((V.dualOfList vs).getD i 0 ⊗ₜ[ℝ] ws.getD j 0))).symm
    _ = ∑ k ∈ Finset.range
          (HSpace.tprodOfLists (HSpace.dual V) W
            (V.dualOfList vs) ws).length,
        a (k / ws.length) (k % ws.length) •
          (HSpace.tprodOfLists (HSpace.dual V) W
            (V.dualOfList vs) ws).getD k 0 := by
      rw [HSpace.tprodOfLists_length, HSpace.dualOfList_length]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < vs.length * ws.length := Finset.mem_range.mp hk
      have hw : ws.length ≠ 0 := by
        intro hz
        simp [hz] at hk'
      rw [RawSpaceFFS.tprodOfLists_getD _ _ _ _ k
        (by rw [HSpace.dualOfList_length]; exact hk')
        (Nat.pos_of_ne_zero hw)]

/-- Successful base reshape preserves the complete array. -/
theorem reshapeBase_ok {orc : PartialFFSOracleSem} {rho : ValEnvSem}
    {e : ValExpr} {s : ValSpace} {a : FlatArray}
    (he : denotValB_partial orc rho [] [] e = .ok (.array a))
    (hs : s.dofPartial (orc rho [] []) = .ok a.length) :
    denotValB_partial orc rho [] [] (ValExpr.reshapBase e s) = .ok (.array a) := by
  simp only [ValExpr.reshapBase, denotValB_partial, he, reshapeInferred, reshapeBetween, reshapeArray, hs]
  simp [bind, Except.bind, pure, Except.pure]

theorem delta_ok {orc : PartialFFSOracleSem} {rho : ValEnvSem} {sv : ValSpace} {n : Nat}
    (hn : sv.dofPartial (orc rho [] []) = .ok n) (i : Nat) :
    denotValB_partial orc rho [] [] (.delta i sv) =
      .ok (.arrayOf n fun j => if j = i ∧ i < n then 1 else 0) := by
  rw [denotValB_partial]
  simp only [withDimensions, dimensions, hn, bind, Except.bind, ValExpr.inferSpaceCtx]
  rw [dof_numbers _ _ _ hn]

theorem vsum_same_infer {orc : PartialFFSOracleSem} {rho : ValEnvSem}
    {sv : ValSpace} {n count : Nat} (hn : count ≤ n)
    (hd : sv.dofPartial (orc rho [] []) = .ok count)
    (summand : Fin n → ValExpr)
    (hi : ∀ i, ValExpr.inferSpaceCtx [] (summand i) = sv) :
    (ValExpr.inferSpaceCtx [] (.vsum sv (List.ofFn summand))).dofPartial (orc rho [] []) = .ok count := by
  cases n with
  | zero =>
    have hc : count = 0 := Nat.eq_zero_of_le_zero hn
    simp [hc, ValExpr.inferSpaceCtx, ValSpace.dofPartial, ValSpace.shpOfPartial,
      bind, Except.bind, pure, Except.pure]
  | succ n => simpa [List.ofFn_succ, ValExpr.inferSpaceCtx, hi] using hd

end GLang.PartialAdequacy
