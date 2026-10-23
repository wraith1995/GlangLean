import GLang.Proofs.Adequacy.Raw.RawSpaceFFSAdequacy
import GLang.Proofs.Adequacy.Raw.RawDofAdequacyCore
import GLang.Numerics.Spectral.BasisFSV
import GLang.Proofs.Source.InnerProduct

namespace GLang

open scoped BigOperators TensorProduct
open Basis (BasisValid)

namespace RawTermEmbed

/-! ## Clean coordinate read-off helpers -/

private theorem tprod_right_tof_eq {Gamma : NLCtx} {b0 b1 : Basis}
    (h : BasisValid Gamma (.tprod b0 b1)) :
    Basis.tof b1 = .space (Basis.sof b1) := by
  cases h with
  | tprod _ _ _ htof1 => exact htof1

private theorem fin_sum_eq_zero_of_length_zero
    {M : Type} [AddCommMonoid M] {n : Nat} (hn : n = 0)
    (f : Fin n → M) : (∑ i, f i) = 0 := by
  subst n
  simp

private theorem sum_range_mul_div_mod
    {M : Type} [AddCommMonoid M]
    (m n : Nat) (g : Nat → Nat → M) :
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

private theorem rowMajor_lt {m n i j : Nat} (hi : i < m) (hj : j < n) :
    i * n + j < m * n := by
  calc
    i * n + j < i * n + n := Nat.add_lt_add_left hj _
    _ = (i + 1) * n := by ring
    _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr hi)

private theorem rowMajor_div_mod {n i j : Nat} (hj : j < n) :
    (i * n + j) / n = i ∧ (i * n + j) % n = j := by
  have h := RawSpaceFFS.rowMajor_div_mod (i := i) hj
  simpa only [Nat.add_comm, Nat.mul_comm] using h

private theorem dualOfList_get_cast (V : HSpace) (vs : List V.carrier)
    (i : Fin vs.length) :
    (V.dualOfList vs).get
        (Fin.cast (HSpace.dualOfList_length V vs).symm i) =
      V.dualVec vs i := by
  have heq := HSpace.dualOfList_eq_finRange_map V vs
  refine (List.get_of_eq heq
    (Fin.cast (HSpace.dualOfList_length V vs).symm i)).trans ?_
  simp

/-- A trace at `b0* ⊗ b1` presents its linear map row by row. -/
theorem trace_linear_map_rows
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b0 b1 : Basis} {e : Term} {env : ValExpr} {sv0 sv1 : ValSpace}
    (hdom : IsListBasis (denotSpace sigma (Basis.sof b0))
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (Basis.sof b0))))
    (hcod : IsListBasis (denotSpace sigma (Basis.sof b1))
      ((denotBasis sigma b1).atSpace
        (denotSpace sigma (Basis.sof b1))))
    (htrace : RawTermTraceAt orc sigma rho env
      (Basis.tof (.tprod (.dual b0) b1)) (.space (.tprod sv0 sv1))
      (denotBasis sigma (.tprod (.dual b0) b1)) (denotTerm sigma e)) :
    exists a : FlatArray,
      denotValB_semS orc rho [] [] env = .ok (.array a) ∧
      a.length =
        ((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0))).length *
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1))).length ∧
      forall j : Fin
          ((denotBasis sigma b0).atSpace
            (denotSpace sigma (Basis.sof b0))).length,
        (denotTerm sigma e).asLinMap
            (denotSpace sigma (Basis.sof b0))
            (denotSpace sigma (Basis.sof b1))
            (((denotBasis sigma b0).atSpace
              (denotSpace sigma (Basis.sof b0))).get j) =
          ∑ i : Fin
              ((denotBasis sigma b1).atSpace
                (denotSpace sigma (Basis.sof b1))).length,
            a.get (j.val *
                ((denotBasis sigma b1).atSpace
                  (denotSpace sigma (Basis.sof b1))).length + i.val) •
              ((denotBasis sigma b1).atSpace
                (denotSpace sigma (Basis.sof b1))).get i := by
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S := (denotBasis sigma b0).atSpace V0
  let T := (denotBasis sigma b1).atSpace V1
  obtain ⟨a, heval, hbLen, haLen, hcoords⟩ :=
    RawSpaceFFS.trace_array_coords (b := .tprod (.dual b0) b1)
      (v := env) (svb := .tprod sv0 sv1) rfl htrace
  simp only [Basis.sof, denotSpace, denotSpaceAux] at hbLen hcoords
  have hN : ValSpace.dof (orc rho [] []) (.tprod sv0 sv1) =
      S.length * T.length := by
    rw [RawSpaceFFS.denotBasis_tprod_dual_atSpace,
      HSpace.tprodOfLists_length, HSpace.dualOfList_length] at hbLen
    exact hbLen.symm
  have haLen' : a.length = S.length * T.length := haLen.trans hN
  rw [hN, RawSpaceFFS.denotBasis_tprod_dual_atSpace] at hcoords
  refine ⟨a, heval, haLen', ?_⟩
  intro j
  change (denotTerm sigma e).asLinMap V0 V1 (S.get j) =
    ∑ i : Fin T.length, a.get (j.val * T.length + i.val) • T.get i
  by_cases hz : T.length = 0
  · have hzero :
        (denotTerm sigma e).asLinMap V0 V1 (S.get j) = 0 := by
      calc
        _ = ∑ i : Fin T.length,
              (V1.dualVec T i
                ((denotTerm sigma e).asLinMap V0 V1 (S.get j))) •
                T.get i := hcod.sum_dual_smul _
        _ = 0 := fin_sum_eq_zero_of_length_zero hz _
    rw [hzero]
    exact (fin_sum_eq_zero_of_length_zero hz _).symm
  · have hpos : 0 < T.length := Nat.pos_of_ne_zero hz
    rw [RawSpaceFFS.asLinMap_eq_dualTensorHom_atSpace, hcoords,
      map_sum, LinearMap.sum_apply,
      ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · apply Finset.sum_congr rfl
      intro i _
      have hk :
          ((finProdFinEquiv (j, i) : Fin (S.length * T.length)) : Nat) =
            i.val + T.length * j.val := rfl
      have hlt : i.val + T.length * j.val <
          (V0.dualOfList S).length * T.length := by
        rw [HSpace.dualOfList_length]
        exact (finProdFinEquiv (j, i)).isLt
      obtain ⟨hdiv, hmod⟩ :=
        RawSpaceFFS.rowMajor_div_mod (i := j.val) i.isLt
      rw [hk]
      change (dualTensorHom ℝ V0.carrier V1.carrier
          (a.get (i.val + T.length * j.val) •
            (HSpace.tprodOfLists (HSpace.dual V0) V1
              (V0.dualOfList S) T).getD
                (i.val + T.length * j.val) 0)) (S.get j) = _
      rw [map_smul, LinearMap.smul_apply,
        RawSpaceFFS.tprodOfLists_getD _ _ _ _ _ hlt hpos,
        hdiv, hmod,
        RawSpaceFFS.dualOfList_getD_eq_dualVec V0 S j.isLt,
        List.getD_eq_getElem T 0 i.isLt, dualTensorHom_apply,
        hdom.dual_delta j j, if_pos rfl, smul_smul, mul_one,
        Nat.add_comm, Nat.mul_comm T.length j.val,
        List.get_eq_getElem]
    · intro i _ hij
      apply Finset.sum_eq_zero
      intro k _
      have hk :
          ((finProdFinEquiv (i, k) : Fin (S.length * T.length)) : Nat) =
            k.val + T.length * i.val := rfl
      have hlt : k.val + T.length * i.val <
          (V0.dualOfList S).length * T.length := by
        rw [HSpace.dualOfList_length]
        exact (finProdFinEquiv (i, k)).isLt
      obtain ⟨hdiv, hmod⟩ :=
        RawSpaceFFS.rowMajor_div_mod (i := i.val) k.isLt
      rw [hk]
      change (dualTensorHom ℝ V0.carrier V1.carrier
          (a.get (k.val + T.length * i.val) •
            (HSpace.tprodOfLists (HSpace.dual V0) V1
              (V0.dualOfList S) T).getD
                (k.val + T.length * i.val) 0)) (S.get j) = 0
      rw [map_smul, LinearMap.smul_apply,
        RawSpaceFFS.tprodOfLists_getD _ _ _ _ _ hlt hpos,
        hdiv, hmod,
        RawSpaceFFS.dualOfList_getD_eq_dualVec V0 S i.isLt,
        List.getD_eq_getElem T 0 k.isLt, dualTensorHom_apply,
        hdom.dual_delta i j, if_neg hij]
      simp
    · exact fun hmem => absurd (Finset.mem_univ j) hmem

/-- The evaluator's row-major witness matrix is the transpose of the usual
codomain-by-domain coordinate matrix. -/
theorem trace_witness_matrix
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b0 b1 : Basis} {e : Term} {env : ValExpr} {sv0 sv1 : ValSpace}
    (hdom : IsListBasis (denotSpace sigma (Basis.sof b0))
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (Basis.sof b0))))
    (hcod : IsListBasis (denotSpace sigma (Basis.sof b1))
      ((denotBasis sigma b1).atSpace
        (denotSpace sigma (Basis.sof b1))))
    (htrace : RawTermTraceAt orc sigma rho env
      (Basis.tof (.tprod (.dual b0) b1)) (.space (.tprod sv0 sv1))
      (denotBasis sigma (.tprod (.dual b0) b1)) (denotTerm sigma e)) :
    exists a : FlatArray,
      denotValB_semS orc rho [] [] env = .ok (.array a) ∧
      a.length =
        ((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0))).length *
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1))).length ∧
      (denotAsMatrix
        ((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0))).length
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1))).length a.get).transpose =
        hdom.coordMatrix hcod
          ((denotTerm sigma e).asLinMap
            (denotSpace sigma (Basis.sof b0))
            (denotSpace sigma (Basis.sof b1))) := by
  obtain ⟨a, ha, halen, hrows⟩ :=
    trace_linear_map_rows hdom hcod htrace
  refine ⟨a, ha, halen, ?_⟩
  ext i j
  simp only [Matrix.transpose_apply, denotAsMatrix,
    IsListBasis.coordMatrix, LinearMap.toMatrix_apply,
    IsListBasis.toBasis_apply]
  have hc := congrFun (hcod.coords_sum_smul
    (fun k => a.get (j.val *
      ((denotBasis sigma b1).atSpace
        (denotSpace sigma (Basis.sof b1))).length + k.val))) i
  simp only [IsListBasis.coords] at hc
  rw [← hrows j] at hc
  simpa [Nat.mul_comm] using hc.symm

/-- In a basis and its Gram-corrected dual, the matrix of the intrinsic
Riesz map is the transpose of the Gram matrix. -/
theorem coordMatrix_inner_dual_entry
    {V : HSpace} {vs : List V.carrier} (hb : IsListBasis V vs)
    (i j : Fin vs.length) :
    hb.coordMatrix hb.dual V.innerProduct
        (Fin.cast (HSpace.dualOfList_length V vs).symm i) j =
      IsListBasis.gram V vs j i := by
  classical
  simp only [IsListBasis.coordMatrix, LinearMap.toMatrix_apply,
    IsListBasis.toBasis_apply]
  have hsum := hb.dual.sum_coords_smul (V.innerProduct (vs.get j))
  have heval := congrArg (fun phi => phi (vs.get i)) hsum
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at heval
  have hcollapse :
      (∑ k : Fin (V.dualOfList vs).length,
        (hb.dual.coords (V.innerProduct (vs.get j))) k *
          (V.dualOfList vs).get k (vs.get i)) =
        (hb.dual.coords (V.innerProduct (vs.get j)))
          (Fin.cast (HSpace.dualOfList_length V vs).symm i) := by
    rw [Finset.sum_eq_single
      (Fin.cast (HSpace.dualOfList_length V vs).symm i)]
    · rw [dualOfList_get_cast, hb.dual_delta i i, if_pos rfl, mul_one]
    · intro k _ hki
      have hk : k.val < vs.length := by
        rw [← HSpace.dualOfList_length V vs]
        exact k.isLt
      have hget : (V.dualOfList vs).get k =
          V.dualVec vs ⟨k.val, hk⟩ := by
        rw [← dualOfList_get_cast V vs ⟨k.val, hk⟩]
        congr
      rw [hget, hb.dual_delta]
      have hne : (⟨k.val, hk⟩ : Fin vs.length) ≠ i := by
        intro hEq
        apply hki
        apply Fin.ext
        exact Fin.mk.inj hEq
      rw [if_neg hne, mul_zero]
    · exact fun hmem => absurd (Finset.mem_univ _) hmem
  rw [hcollapse] at heval
  have hcoord :
      (hb.dual.coords (V.innerProduct (vs.get j)))
          (Fin.cast (HSpace.dualOfList_length V vs).symm i) =
        V.innerProduct (vs.get j) (vs.get i) := heval
  simpa only [IsListBasis.gram] using hcoord

private theorem get_eq_dualVec_of_eq
    {V : HSpace} {vs : List V.carrier}
    {ds : List (HSpace.dual V).carrier}
    (hds : ds = V.dualOfList vs) (i : Fin ds.length) :
    ds.get i = V.dualVec vs
      (Fin.cast ((congrArg (fun xs => xs.length) hds).trans
        (HSpace.dualOfList_length V vs)) i) := by
  subst ds
  let j : Fin vs.length :=
    Fin.cast (HSpace.dualOfList_length V vs) i
  have h := dualOfList_get_cast V vs j
  convert h using 1 <;> apply Fin.ext <;> rfl

theorem coordMatrix_inner_of_dual_eq
    {V : HSpace} {vs : List V.carrier}
    {ds : List (HSpace.dual V).carrier}
    (hb : IsListBasis V vs) (hd : IsListBasis (HSpace.dual V) ds)
    (hds : ds = V.dualOfList vs) (i : Fin ds.length)
    (j : Fin vs.length) :
    hb.coordMatrix hd V.innerProduct i j =
      IsListBasis.gram V vs j
        (Fin.cast ((congrArg (fun xs => xs.length) hds).trans
          (HSpace.dualOfList_length V vs)) i) := by
  classical
  simp only [IsListBasis.coordMatrix, LinearMap.toMatrix_apply,
    IsListBasis.toBasis_apply]
  have hsum := hd.sum_coords_smul (V.innerProduct (vs.get j))
  have heval := congrArg
    (fun phi => phi (vs.get (Fin.cast
      ((congrArg (fun xs => xs.length) hds).trans
        (HSpace.dualOfList_length V vs)) i))) hsum
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at heval
  have hcollapse :
      (∑ k : Fin ds.length,
        (hd.coords (V.innerProduct (vs.get j))) k *
          ds.get k (vs.get (Fin.cast
            ((congrArg (fun xs => xs.length) hds).trans
              (HSpace.dualOfList_length V vs)) i))) =
        (hd.coords (V.innerProduct (vs.get j))) i := by
    rw [Finset.sum_eq_single i]
    · rw [get_eq_dualVec_of_eq hds]
      rw [hb.dual_delta, if_pos rfl, mul_one]
    · intro k _ hki
      rw [get_eq_dualVec_of_eq hds, hb.dual_delta]
      have hne :
          Fin.cast ((congrArg (fun xs => xs.length) hds).trans
            (HSpace.dualOfList_length V vs)) k ≠
            Fin.cast ((congrArg (fun xs => xs.length) hds).trans
              (HSpace.dualOfList_length V vs)) i := by
        intro heq
        apply hki
        apply Fin.ext
        exact Fin.mk.inj heq
      rw [if_neg hne, mul_zero]
    · exact fun hmem => absurd (Finset.mem_univ i) hmem
  rw [hcollapse] at heval
  simpa only [IsListBasis.gram] using heval

/-- An adequate realization of `.inner s` supplies exactly the Gram matrix
of the denoted basis, even when that basis is not standard. -/
theorem trace_inner_matrix
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b : Basis} {env : ValExpr} {sv : ValSpace}
    (hb : IsListBasis (denotSpace sigma (Basis.sof b))
      ((denotBasis sigma b).atSpace
        (denotSpace sigma (Basis.sof b))))
    (hdual : IsListBasis (denotSpace sigma (Basis.sof (.dual b)))
      ((denotBasis sigma (.dual b)).atSpace
        (denotSpace sigma (Basis.sof (.dual b)))))
    (htrace : RawTermTraceAt orc sigma rho env
      (Basis.tof (.tprod (.dual b) (.dual b)))
      (.space (.tprod sv sv))
      (denotBasis sigma (.tprod (.dual b) (.dual b)))
      (denotTerm sigma (.inner (Basis.sof b)))) :
    exists a : FlatArray,
      denotValB_semS orc rho [] [] env = .ok (.array a) ∧
      a.length =
        ((denotBasis sigma b).atSpace
          (denotSpace sigma (Basis.sof b))).length ^ 2 ∧
      denotAsMatrix
        ((denotBasis sigma b).atSpace
          (denotSpace sigma (Basis.sof b))).length
        ((denotBasis sigma b).atSpace
          (denotSpace sigma (Basis.sof b))).length a.get =
        IsListBasis.gram (denotSpace sigma (Basis.sof b))
          ((denotBasis sigma b).atSpace
            (denotSpace sigma (Basis.sof b))) := by
  let V := denotSpace sigma (Basis.sof b)
  let S := (denotBasis sigma b).atSpace V
  let D := (denotBasis sigma (.dual b)).atSpace (HSpace.dual V)
  have hD : D = V.dualOfList S := by
    exact RawSpaceFFS.denotBasis_dual_atSpace sigma b
  have hDlen : D.length = S.length := by
    rw [hD, HSpace.dualOfList_length]
  have hdualD : IsListBasis (HSpace.dual V) D := hdual
  obtain ⟨a, ha, halen, hmatrix⟩ :=
    trace_witness_matrix (b0 := b) (b1 := .dual b) hb hdualD htrace
  have hinner :
      (denotTerm sigma (.inner (Basis.sof b))).asLinMap V
          (HSpace.dual V) = V.innerProduct := by
    exact asLinMap_innerTensor V V.innerProduct
  refine ⟨a, ha, ?_, ?_⟩
  · change a.length = S.length ^ 2
    rw [pow_two]
    change a.length = S.length * D.length at halen
    exact halen.trans (congrArg (S.length * ·) hDlen)
  · change denotAsMatrix S.length S.length a.get =
      IsListBasis.gram V S
    ext i j
    change (denotAsMatrix S.length D.length a.get).transpose =
        hb.coordMatrix hdualD
          ((denotTerm sigma (.inner (Basis.sof b))).asLinMap V
            (HSpace.dual V)) at hmatrix
    let jD : Fin D.length := Fin.cast hDlen.symm j
    have hm := congrFun (congrFun hmatrix jD) i
    simp only [Matrix.transpose_apply] at hm
    rw [hinner] at hm
    have hc := coordMatrix_inner_of_dual_eq hb hdualD hD jD i
    have hcast :
        Fin.cast ((congrArg (fun xs => xs.length) hD).trans
          (HSpace.dualOfList_length V S)) jD = j := by
      apply Fin.ext
      rfl
    rw [hcast] at hc
    have hm' : denotAsMatrix S.length S.length a.get i j =
        hb.coordMatrix hdualD V.innerProduct jD i := by
      simpa [denotAsMatrix, jD, hDlen] using hm
    exact hm'.trans hc

/-- Row-major coefficient form of a tensor encoding a linear map. -/
theorem linearMap_tensor_coeff_sum (V W : HSpace)
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
      exact (sum_range_mul_div_mod vs.length ws.length
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
      have hwpos : 0 < ws.length := Nat.pos_of_ne_zero hw
      rw [RawSpaceFFS.tprodOfLists_getD _ _ _ _ k
        (by rw [HSpace.dualOfList_length]; exact hk') hwpos]

/-- If the basis of a subspace is obtained by lifting an ambient list whose
columns are `U`, then the inclusion tensor has exactly those columns as its
row-major coefficients.  This is the common coordinate endpoint of all four
fundamental-subspace embedding arms. -/
theorem subtype_tensor_ofCoords
    (V : HSpace) (K : Submodule ℝ V.carrier)
    (S : List V.carrier) {k : Nat}
    (U : Matrix (Fin S.length) (Fin k) ℝ)
    (raw : List V.carrier)
    (hraw : raw = List.ofCoords S U)
    (hsub : ∀ x ∈ raw, x ∈ K)
    (hbsub : IsListBasis (HSpace.ofSubmodule V K)
      (HSpace.liftToSubmodule K raw))
    (out : FlatArray)
    (hget : ∀ (j : Fin k) (i : Fin S.length),
      out.get (j.val * S.length + i.val) = U i j) :
    (dualTensorHomEquiv ℝ (HSpace.ofSubmodule V K).carrier V.carrier).symm
        K.subtype =
      ∑ q ∈ Finset.range
          (HSpace.tprodOfLists (HSpace.dual (HSpace.ofSubmodule V K)) V
            ((HSpace.ofSubmodule V K).dualOfList
              (HSpace.liftToSubmodule K raw)) S).length,
        out.get q •
          (HSpace.tprodOfLists (HSpace.dual (HSpace.ofSubmodule V K)) V
            ((HSpace.ofSubmodule V K).dualOfList
              (HSpace.liftToSubmodule K raw)) S).getD q 0 := by
  let L := HSpace.liftToSubmodule K raw
  have hL : L.length = raw.length :=
    HSpace.liftToSubmodule_length_of_subset K raw hsub
  have hrawLen : raw.length = k := by
    rw [hraw, List.ofCoords_length]
  have hrows : ∀ j < L.length,
      K.subtype (L.getD j 0) =
        ∑ i ∈ Finset.range S.length,
          out.get (j * S.length + i) • S.getD i 0 := by
    intro j hj
    have hjraw : j < raw.length := by omega
    have hjk : j < k := by omega
    rw [List.getD_eq_getElem L 0 hj]
    change ((L.get ⟨j, hj⟩ : K) : V.carrier) = _
    let jraw : Fin raw.length := ⟨j, hjraw⟩
    let jcoords : Fin (List.ofCoords S U).length :=
      Fin.cast (congrArg List.length hraw) jraw
    let jU : Fin k := Fin.cast (List.ofCoords_length S U) jcoords
    calc
      ((L.get ⟨j, hj⟩ : K) : V.carrier) = raw.get jraw := by
        exact HSpace.liftToSubmodule_get_val_of_subset K raw hsub ⟨j, hj⟩
      _ = (List.ofCoords S U).get jcoords := by
        exact List.get_of_eq hraw jraw
      _ = ∑ i : Fin S.length, U i jU • S.get i := by
        exact List.ofCoords_get S U jcoords
      _ = ∑ i ∈ Finset.range S.length,
          out.get (j * S.length + i) • S.getD i 0 := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Fintype.sum_congr
        intro i
        rw [List.getD_eq_getElem S 0 i.isLt, ← hget jU i]
        congr
  have htensor := linearMap_tensor_coeff_sum
    (HSpace.ofSubmodule V K) V L S hbsub K.subtype
      (fun i j => out.get (i * S.length + j)) hrows
  rw [htensor]
  apply Finset.sum_congr rfl
  intro q hq
  congr 2
  have hqeq : (q / S.length) * S.length + q % S.length = q := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod q S.length
  exact congrArg out.get hqeq

/-! ## Canonical-FSV evaluator read-off -/

/-- The rank seen by the FFS oracle is the column count recorded by the
canonical selection that realizes the source fundamental-space bases. -/
theorem ffs_oracle_block_dims
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {rho : ValEnvSem} {v : ValExpr} {sa sb : ValSpace}
    {V0 V1 : HSpace} {S0 : List V0.carrier} {S1 : List V1.carrier}
    (hb0 : IsListBasis V0 S0) (hb1 : IsListBasis V1 S1)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) {ae : FlatArray}
    (heval : denotValB_semS orc rho [] [] v = .ok (.array ae))
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hf : ValueQueryDependencies.Finite (.expr [] v))
    (hd0 : ValSpace.dof (orc rho [] []) sa = S0.length)
    (hd1 : ValSpace.dof (orc rho [] []) sb = S1.length)
    (hmatrix : (denotAsMatrix S0.length S1.length ae.get).transpose =
      hb0.coordMatrix hb1 f) :
    orc rho [] [] .kernel (.tprod sa sb) v =
        S0.length - (hb0.canonical hb1 f).r ∧
    orc rho [] [] .cokernel (.tprod sa sb) v = (hb0.canonical hb1 f).r ∧
    orc rho [] [] .image (.tprod sa sb) v = (hb0.canonical hb1 f).r ∧
    orc rho [] [] .coimage (.tprod sa sb) v =
      S1.length - (hb0.canonical hb1 f).r := by
  have hrank : ffsOperandRank orc rho [] [] (.tprod sa sb) v =
      (hb0.canonical hb1 f).r := by
    unfold ffsOperandRank
    simp only [ValSpace.shpOf_tprod, heval]
    rw [hd0, hd1]
    have hcoord : (denotAsMatrix S0.length S1.length ae.get).rank =
        Module.finrank ℝ (LinearMap.range f) := by
      rw [← RawSpaceFFS.coordMatrix_rank hb0 hb1 f,
        ← Matrix.rank_transpose (denotAsMatrix S0.length S1.length ae.get),
        hmatrix]
    exact hcoord.trans (RawSpaceFFS.coordMatrix_rank hb0 hb1 f).symm
  rw [hspec.rank rho .kernel (.tprod sa sb) v hinfer ((hinfer ▸ hf.inferSpace).ffs hf),
    hspec.rank rho .cokernel (.tprod sa sb) v hinfer ((hinfer ▸ hf.inferSpace).ffs hf),
    hspec.rank rho .image (.tprod sa sb) v hinfer ((hinfer ▸ hf.inferSpace).ffs hf),
    hspec.rank rho .coimage (.tprod sa sb) v hinfer ((hinfer ▸ hf.inferSpace).ffs hf)]
  simp only [ValSpace.shpOf_tprod, ffsDim, hrank, hd0, hd1]
  simp

private theorem pack_castColumns {m k l : ℕ} (h : k = l)
    (M : Matrix (Fin m) (Fin k) ℝ) :
    (ValueCanonicalFSV.ResultMatrix.mk m l (BasisSpectral.castColumns h M)) =
      ⟨m, k, M⟩ := by
  subst l
  rfl

/-- The transposed `canonicalFSV .kernel` value is the kernel-coordinate block in
subspace-major order. -/
theorem eval_vtrans_canonicalUI
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {v env0 env1 : ValExpr} {sa sb : ValSpace}
    {d0 d1 : Nat} {M : Matrix (Fin d1) (Fin d0) ℝ}
    {MW : Matrix (Fin d0) (Fin d0) ℝ}
    {MV : Matrix (Fin d1) (Fin d1) ℝ}
    {ae a0 a1 : FlatArray}
    (he : denotValB_semS orc rho [] [] v = .ok (.array ae))
    (he0 : denotValB_semS orc rho [] [] env0 = .ok (.array a0))
    (he1 : denotValB_semS orc rho [] [] env1 = .ok (.array a1))
    (haelen : ae.length = d0 * d1)
    (ha0len : a0.length = d0 * d0)
    (ha1len : a1.length = d1 * d1)
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hd0 : ValSpace.dof (orc rho [] []) sa = d0)
    (hd1 : ValSpace.dof (orc rho [] []) sb = d1)
    (hM : (denotAsMatrix d0 d1 ae.get).transpose = M)
    (hMW : denotAsMatrix d0 d0 a0.get = MW)
    (hMV : denotAsMatrix d1 d1 a1.get = MV)
    (hG : MW.PosDef) (hH : MV.PosDef)
    (hker : orc rho [] [] .kernel (.tprod sa sb) v =
      d0 - M.rank) :
    exists out : FlatArray,
      denotValB_semS orc rho [] [] (.vtrans (.gsvdUI v env0 env1)) =
        .ok (.array out) ∧
      out.length = (d0 - M.rank) * d0 ∧
      forall (j : Fin (d0 - M.rank)) (i : Fin d0),
        out.get (j.val * d0 + i.val) = (BasisSpectral.canonicalBlocks M MW MV hG hH).UI i j := by
  have hleaf : ValueCanonicalFSV.eval .kernel d0 d1 ae a0 a1 =
      .ok ⟨d0, d0 - M.rank, (BasisSpectral.canonicalBlocks M MW MV hG hH).UI⟩ := by
    rw [ValueCanonicalFSV.eval_ok _ _ _ _ _ _ ⟨haelen, ha0len, ha1len⟩
      (hMW.symm ▸ hG) (hMV.symm ▸ hH)]
    simp only [hM, hMW, hMV]
    congr 1
  have heval := denotValB_semS_gsvdUI_ok orc rho [] []
    v env0 env1 ae a0 a1 sa sb _ he he0 he1 hinfer (by simpa only [hd0, hd1] using hleaf)
    (by simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient,
      ValSpace.dof_tprod, ValSpace.dof_ffs, hker, hd0, hd1])
  rw [denotValB_semS.eq_11, heval]
  simp only [ValValSem.bindArray]
  rw [if_pos (by simp [ValueShape.tensor, ValExpr.inferSpaceCtx, hinfer,
    ValFFSProp.ambient, ValSpace.dof_ffs, hker, hd0, hd1,
    ValueCanonicalFSV.ResultMatrix.flatten])]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [FlatArray.length_ofFn, ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient,
      ValSpace.dof_tprod, ValSpace.dof_ffs, hker, hd0]
  · intro j i
    simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient, ValSpace.dof_tprod,
      ValSpace.dof_ffs, hker, hd0, hd1]
    have hout : j.val * d0 + i.val <
        (d0 - M.rank) * d0 :=
      rowMajor_lt j.isLt i.isLt
    obtain ⟨hdiv, hmod⟩ := rowMajor_div_mod (i := j.val) i.isLt
    have hin : i.val * (d0 - M.rank) + j.val <
        d0 * (d0 - M.rank) :=
      rowMajor_lt i.isLt j.isLt
    simp only [FlatArray.get_ofFn, hout, Nat.not_le.mpr hout, if_true,
      if_false, hdiv, hmod, hin, Nat.not_le.mpr hin]
    simp only [ValueCanonicalFSV.ResultMatrix.flatten, FlatArray.get_ofFn, matrixAsDenot]
    by_cases hz : d0 - M.rank = 0
    · exact Fin.elim0 (hz ▸ j)
    · obtain ⟨hdiv', hmod'⟩ :=
        rowMajor_div_mod (i := i.val) j.isLt
      have hswap :
          (d0 - M.rank) * i.val + j.val =
            i.val * (d0 - M.rank) + j.val := by
        rw [Nat.mul_comm]
      simp only [hz, if_false, hswap, hin, hdiv', hmod', i.isLt,
        j.isLt, if_true]
      simp

/-- The transposed `canonicalFSV .cokernel` value is the cokernel-coordinate block in
subspace-major order. -/
theorem eval_vtrans_canonicalU
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {v env0 env1 : ValExpr} {sa sb : ValSpace}
    {d0 d1 : Nat} {M : Matrix (Fin d1) (Fin d0) ℝ}
    {MW : Matrix (Fin d0) (Fin d0) ℝ}
    {MV : Matrix (Fin d1) (Fin d1) ℝ}
    {ae a0 a1 : FlatArray}
    (he : denotValB_semS orc rho [] [] v = .ok (.array ae))
    (he0 : denotValB_semS orc rho [] [] env0 = .ok (.array a0))
    (he1 : denotValB_semS orc rho [] [] env1 = .ok (.array a1))
    (haelen : ae.length = d0 * d1)
    (ha0len : a0.length = d0 * d0)
    (ha1len : a1.length = d1 * d1)
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hd0 : ValSpace.dof (orc rho [] []) sa = d0)
    (hd1 : ValSpace.dof (orc rho [] []) sb = d1)
    (hM : (denotAsMatrix d0 d1 ae.get).transpose = M)
    (hMW : denotAsMatrix d0 d0 a0.get = MW)
    (hMV : denotAsMatrix d1 d1 a1.get = MV)
    (hG : MW.PosDef) (hH : MV.PosDef)
    (hcoker : orc rho [] [] .cokernel (.tprod sa sb) v =
      M.rank) :
    exists out : FlatArray,
      denotValB_semS orc rho [] [] (.vtrans (.gsvdU v env0 env1)) =
        .ok (.array out) ∧
      out.length = M.rank * d0 ∧
      forall (j : Fin M.rank) (i : Fin d0),
        out.get (j.val * d0 + i.val) = (BasisSpectral.canonicalBlocks M MW MV hG hH).U i j := by
  have hleaf : ValueCanonicalFSV.eval .cokernel d0 d1 ae a0 a1 =
      .ok ⟨d0, M.rank, (BasisSpectral.canonicalBlocks M MW MV hG hH).U⟩ := by
    rw [ValueCanonicalFSV.eval_ok _ _ _ _ _ _ ⟨haelen, ha0len, ha1len⟩
      (hMW.symm ▸ hG) (hMV.symm ▸ hH)]
    simp only [hM, hMW, hMV]
    congr 1
  have heval := denotValB_semS_gsvdU_ok orc rho [] []
    v env0 env1 ae a0 a1 sa sb _ he he0 he1 hinfer (by simpa only [hd0, hd1] using hleaf)
    (by simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient,
      ValSpace.dof_tprod, ValSpace.dof_ffs, hcoker, hd0, hd1])
  rw [denotValB_semS.eq_11, heval]
  simp only [ValValSem.bindArray]
  rw [if_pos (by simp [ValueShape.tensor, ValExpr.inferSpaceCtx, hinfer,
    ValFFSProp.ambient, ValSpace.dof_ffs, hcoker, hd0, hd1,
    ValueCanonicalFSV.ResultMatrix.flatten])]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [FlatArray.length_ofFn, ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient,
      ValSpace.dof_tprod, ValSpace.dof_ffs, hcoker, hd0]
  · intro j i
    simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient, ValSpace.dof_tprod,
      ValSpace.dof_ffs, hcoker, hd0, hd1]
    have hout : j.val * d0 + i.val <
        M.rank * d0 := rowMajor_lt j.isLt i.isLt
    obtain ⟨hdiv, hmod⟩ := rowMajor_div_mod (i := j.val) i.isLt
    have hin : i.val * M.rank + j.val <
        d0 * M.rank := rowMajor_lt i.isLt j.isLt
    simp only [FlatArray.get_ofFn, hout, Nat.not_le.mpr hout, if_true,
      if_false, hdiv, hmod]
    simp only [ValueCanonicalFSV.ResultMatrix.flatten, FlatArray.get_ofFn, matrixAsDenot]
    by_cases hz : M.rank = 0
    · exact Fin.elim0 (hz ▸ j)
    · obtain ⟨hdiv', hmod'⟩ :=
        rowMajor_div_mod (i := i.val) j.isLt
      have hswap : M.rank * i.val + j.val =
          i.val * M.rank + j.val := by
        rw [Nat.mul_comm]
      simp only [hz, if_false, hswap, hin, hdiv', hmod', i.isLt,
        j.isLt, if_true]
      simp

/-- The transposed `canonicalFSV .image` value is the image-coordinate block in
subspace-major order. -/
theorem eval_vtrans_canonicalV
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {v env0 env1 : ValExpr} {sa sb : ValSpace}
    {d0 d1 : Nat} {M : Matrix (Fin d1) (Fin d0) ℝ}
    {MW : Matrix (Fin d0) (Fin d0) ℝ}
    {MV : Matrix (Fin d1) (Fin d1) ℝ}
    {ae a0 a1 : FlatArray}
    (he : denotValB_semS orc rho [] [] v = .ok (.array ae))
    (he0 : denotValB_semS orc rho [] [] env0 = .ok (.array a0))
    (he1 : denotValB_semS orc rho [] [] env1 = .ok (.array a1))
    (haelen : ae.length = d0 * d1)
    (ha0len : a0.length = d0 * d0)
    (ha1len : a1.length = d1 * d1)
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hd0 : ValSpace.dof (orc rho [] []) sa = d0)
    (hd1 : ValSpace.dof (orc rho [] []) sb = d1)
    (hM : (denotAsMatrix d0 d1 ae.get).transpose = M)
    (hMW : denotAsMatrix d0 d0 a0.get = MW)
    (hMV : denotAsMatrix d1 d1 a1.get = MV)
    (hG : MW.PosDef) (hH : MV.PosDef)
    (himage : orc rho [] [] .image (.tprod sa sb) v =
      M.rank) :
    exists out : FlatArray,
      denotValB_semS orc rho [] [] (.vtrans (.gsvdV v env0 env1)) =
        .ok (.array out) ∧
      out.length = M.rank * d1 ∧
      forall (j : Fin M.rank) (i : Fin d1),
        out.get (j.val * d1 + i.val) = (BasisSpectral.canonicalBlocks M MW MV hG hH).V i j := by
  have hleaf : ValueCanonicalFSV.eval .image d0 d1 ae a0 a1 =
      .ok ⟨d1, M.rank, (BasisSpectral.canonicalBlocks M MW MV hG hH).V⟩ := by
    rw [ValueCanonicalFSV.eval_ok _ _ _ _ _ _ ⟨haelen, ha0len, ha1len⟩
      (hMW.symm ▸ hG) (hMV.symm ▸ hH)]
    simp only [hM, hMW, hMV]
    congr 1
  have heval := denotValB_semS_gsvdV_ok orc rho [] []
    v env0 env1 ae a0 a1 sa sb _ he he0 he1 hinfer (by simpa only [hd0, hd1] using hleaf)
    (by simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient,
      ValSpace.dof_tprod, ValSpace.dof_ffs, himage, hd0, hd1])
  rw [denotValB_semS.eq_11, heval]
  simp only [ValValSem.bindArray]
  rw [if_pos (by simp [ValueShape.tensor, ValExpr.inferSpaceCtx, hinfer,
    ValFFSProp.ambient, ValSpace.dof_ffs, himage, hd0, hd1,
    ValueCanonicalFSV.ResultMatrix.flatten])]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [FlatArray.length_ofFn, ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient,
      ValSpace.dof_tprod, ValSpace.dof_ffs, himage, hd1]
  · intro j i
    simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient, ValSpace.dof_tprod,
      ValSpace.dof_ffs, himage, hd0, hd1]
    have hout : j.val * d1 + i.val <
        M.rank * d1 := rowMajor_lt j.isLt i.isLt
    obtain ⟨hdiv, hmod⟩ := rowMajor_div_mod (i := j.val) i.isLt
    have hin : i.val * M.rank + j.val <
        d1 * M.rank := rowMajor_lt i.isLt j.isLt
    simp only [FlatArray.get_ofFn, hout, Nat.not_le.mpr hout, if_true,
      if_false, hdiv, hmod]
    simp only [ValueCanonicalFSV.ResultMatrix.flatten, FlatArray.get_ofFn, matrixAsDenot]
    by_cases hz : M.rank = 0
    · exact Fin.elim0 (hz ▸ j)
    · obtain ⟨hdiv', hmod'⟩ :=
        rowMajor_div_mod (i := i.val) j.isLt
      have hswap : M.rank * i.val + j.val =
          i.val * M.rank + j.val := by
        rw [Nat.mul_comm]
      simp only [hz, if_false, hswap, hin, hdiv', hmod', i.isLt,
        j.isLt, if_true]
      simp

/-- The transposed `canonicalFSV .coimage` value is the coimage-coordinate block in
subspace-major order. -/
theorem eval_vtrans_canonicalVI
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {v env0 env1 : ValExpr} {sa sb : ValSpace}
    {d0 d1 : Nat} {M : Matrix (Fin d1) (Fin d0) ℝ}
    {MW : Matrix (Fin d0) (Fin d0) ℝ}
    {MV : Matrix (Fin d1) (Fin d1) ℝ}
    {ae a0 a1 : FlatArray}
    (he : denotValB_semS orc rho [] [] v = .ok (.array ae))
    (he0 : denotValB_semS orc rho [] [] env0 = .ok (.array a0))
    (he1 : denotValB_semS orc rho [] [] env1 = .ok (.array a1))
    (haelen : ae.length = d0 * d1)
    (ha0len : a0.length = d0 * d0)
    (ha1len : a1.length = d1 * d1)
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hd0 : ValSpace.dof (orc rho [] []) sa = d0)
    (hd1 : ValSpace.dof (orc rho [] []) sb = d1)
    (hM : (denotAsMatrix d0 d1 ae.get).transpose = M)
    (hMW : denotAsMatrix d0 d0 a0.get = MW)
    (hMV : denotAsMatrix d1 d1 a1.get = MV)
    (hG : MW.PosDef) (hH : MV.PosDef)
    (hcoimage : orc rho [] [] .coimage (.tprod sa sb) v =
      d1 - M.rank) :
    exists out : FlatArray,
      denotValB_semS orc rho [] [] (.vtrans (.gsvdVI v env0 env1)) =
        .ok (.array out) ∧
      out.length = (d1 - M.rank) * d1 ∧
      forall (j : Fin (d1 - M.rank)) (i : Fin d1),
        out.get (j.val * d1 + i.val) = (BasisSpectral.canonicalBlocks M MW MV hG hH).VI i j := by
  have hleaf : ValueCanonicalFSV.eval .coimage d0 d1 ae a0 a1 =
      .ok ⟨d1, d1 - M.rank, (BasisSpectral.canonicalBlocks M MW MV hG hH).VI⟩ := by
    rw [ValueCanonicalFSV.eval_ok _ _ _ _ _ _ ⟨haelen, ha0len, ha1len⟩
      (hMW.symm ▸ hG) (hMV.symm ▸ hH)]
    simp only [hM, hMW, hMV]
    congr 1
  have heval := denotValB_semS_gsvdVI_ok orc rho [] []
    v env0 env1 ae a0 a1 sa sb _ he he0 he1 hinfer (by simpa only [hd0, hd1] using hleaf)
    (by simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient,
      ValSpace.dof_tprod, ValSpace.dof_ffs, hcoimage, hd0, hd1])
  rw [denotValB_semS.eq_11, heval]
  simp only [ValValSem.bindArray]
  rw [if_pos (by simp [ValueShape.tensor, ValExpr.inferSpaceCtx, hinfer,
    ValFFSProp.ambient, ValSpace.dof_ffs, hcoimage, hd0, hd1,
    ValueCanonicalFSV.ResultMatrix.flatten])]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [FlatArray.length_ofFn, ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient,
      ValSpace.dof_tprod, ValSpace.dof_ffs, hcoimage, hd1]
  · intro j i
    simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient, ValSpace.dof_tprod,
      ValSpace.dof_ffs, hcoimage, hd0, hd1]
    have hout : j.val * d1 + i.val <
        (d1 - M.rank) * d1 :=
      rowMajor_lt j.isLt i.isLt
    obtain ⟨hdiv, hmod⟩ := rowMajor_div_mod (i := j.val) i.isLt
    have hin : i.val * (d1 - M.rank) + j.val <
        d1 * (d1 - M.rank) :=
      rowMajor_lt i.isLt j.isLt
    simp only [FlatArray.get_ofFn, hout, Nat.not_le.mpr hout, if_true,
      if_false, hdiv, hmod]
    simp only [ValueCanonicalFSV.ResultMatrix.flatten, FlatArray.get_ofFn, matrixAsDenot]
    by_cases hz : d1 - M.rank = 0
    · exact Fin.elim0 (hz ▸ j)
    · obtain ⟨hdiv', hmod'⟩ :=
        rowMajor_div_mod (i := i.val) j.isLt
      have hswap :
          (d1 - M.rank) * i.val + j.val =
            i.val * (d1 - M.rank) + j.val := by
        rw [Nat.mul_comm]
      simp only [hz, if_false, hswap, hin, hdiv', hmod', i.isLt,
        j.isLt, if_true]
      simp

/-! ## Strengthened term arms -/

/-! The long embedding proofs use the oracle in only two numerical places:
the four canonical block dimensions and the equality between the inferred output
shape and the compiled result shape.  Package precisely those two facts at a
raw world so the algebraic proof can be reused by a locally certified oracle.
-/

noncomputable abbrev embedBasisSpace (sigma : DEnv) (b : Basis) : HSpace :=
  denotSpace sigma (Basis.sof b)

noncomputable abbrev embedBasisList (sigma : DEnv) (b : Basis) :
    List (embedBasisSpace sigma b).carrier :=
  (denotBasis sigma b).atSpace (embedBasisSpace sigma b)

noncomputable abbrev embedWitnessLin (sigma : DEnv) (b0 b1 : Basis)
    (e : Term) :
    (embedBasisSpace sigma b0).carrier →ₗ[ℝ]
      (embedBasisSpace sigma b1).carrier :=
  (denotTerm sigma e).asLinMap
    (embedBasisSpace sigma b0) (embedBasisSpace sigma b1)

/-- The complete numerical interface used by an embedding proof at one raw
world.  It intentionally says nothing about arbitrary worlds: callers may
derive it either from a global `OracleSpec` or from a local eventual-oracle
certificate supplied by strict child induction hypotheses. -/
def RawEmbedNumericalFactsAt (orc : FFSOracleSem)
    (rho : ValEnvSem) (sigma : DEnv) (b0 b1 : Basis) (e : Term)
    (v output : ValExpr) (target : ValSpace) : Prop :=
  forall {sa sb : ValSpace} {ae : FlatArray},
    ValExpr.inferSpaceCtx [] v = .tprod sa sb ->
    forall (hb0 : IsListBasis (embedBasisSpace sigma b0)
        (embedBasisList sigma b0))
      (hb1 : IsListBasis (embedBasisSpace sigma b1)
        (embedBasisList sigma b1)),
      ValSpace.dof (orc rho [] []) sa = (embedBasisList sigma b0).length ->
      ValSpace.dof (orc rho [] []) sb = (embedBasisList sigma b1).length ->
      denotValB_semS orc rho [] [] v = .ok (.array ae) ->
      (denotAsMatrix (embedBasisList sigma b0).length
          (embedBasisList sigma b1).length ae.get).transpose =
        hb0.coordMatrix hb1 (embedWitnessLin sigma b0 b1 e) ->
      (orc rho [] [] .kernel (.tprod sa sb) v =
          (embedBasisList sigma b0).length -
            (hb0.canonical hb1 (embedWitnessLin sigma b0 b1 e)).r ∧
        orc rho [] [] .cokernel (.tprod sa sb) v =
          (hb0.canonical hb1 (embedWitnessLin sigma b0 b1 e)).r ∧
        orc rho [] [] .image (.tprod sa sb) v =
          (hb0.canonical hb1 (embedWitnessLin sigma b0 b1 e)).r ∧
        orc rho [] [] .coimage (.tprod sa sb) v =
          (embedBasisList sigma b1).length -
            (hb0.canonical hb1 (embedWitnessLin sigma b0 b1 e)).r) ∧
      ValSpace.shpOf (orc rho [] []) (ValExpr.inferSpaceCtx [] output) =
        ValSpace.shpOf (orc rho [] []) target

/-- Subcontext-closed form of `RawEmbedNumericalFactsAt`. -/
def RawMEmbedNumericalFactsSubctx (orc : FFSOracleSem)
    (Gamma : NLCtx) (Psi : EvalCtx) (b0 b1 : Basis) (e : Term)
    (v output : ValExpr) (target : ValSpace) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
      (sigma : DEnv) (GammaV : ValCtx),
      NLCtxIncl Gamma Gamma' ->
      RawTypedConsistent orc Delta' Gamma' Psi' GammaV sigma rho ->
      RawEmbedNumericalFactsAt orc rho sigma b0 b1 e v output target

theorem rawMEmbedNumericalFacts_of_spec
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {e : Term}
    {v output : ValExpr} {target : ValSpace}
    {tv : ValTy} (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v tv)
    (hout : RawMDofTraceSubctx orc Gamma Psi output (.space target)) :
    RawMEmbedNumericalFactsSubctx orc Gamma Psi b0 b1 e v output target := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  intro sa sb ae hinfer hb0 hb1 hd0 hd1 heval hmatrix
  refine ⟨?_, hout rfl hsub rho Delta' Gamma' sigma GammaV hle hc⟩
  exact ffs_oracle_block_dims hspec hb0 hb1
    (embedWitnessLin sigma b0 b1 e) heval hinfer (hc.exprFinite (he.mono hsub).toOpStep) hd0 hd1 hmatrix

/-- Ordinary exact-basis trace for the kernel inclusion. -/
theorem raw_arm_term_embed_kernel_of_numerical
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (_ht : Nonempty (HasType ∅ Gamma (.embed (.ker s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0))
    (_hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (_hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (_hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : RawMTyAtSubctx orc Gamma Psi
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1)))
    (hnum : RawMEmbedNumericalFactsSubctx orc Gamma Psi b0 b1 e v
      (.vtrans (.gsvdUI v env0 env1))
      (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) :
    RawMTermTraceSubctx orc ∅ Gamma Psi (.embed (.ker s0 s1 e))
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.vtrans (.gsvdUI v env0 env1))
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) := by
  subst s0
  subst s1
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma b0).atSpace V0
  let S1 := (denotBasis sigma b1).atSpace V1
  let f := (denotTerm sigma e).asLinMap V0 V1
  have hb0v : BasisValid Gamma b0 :=
    (S.Term.basisValid he).tprod_inv.1.dual_inv
  have hb1v : BasisValid Gamma b1 :=
    (S.Term.basisValid he).tprod_inv.2
  have hlb0 : IsListBasis V0 S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb1 : IsListBasis V1 S1 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb0d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b0)
    (raw_basisValid_mono (S.Term.basisValid he).tprod_inv.1 hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb1d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b1)
    (raw_basisValid_mono
      (.dual hb1v (tprod_right_tof_eq (S.Term.basisValid he))) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have trE := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI0 := ihI0.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI1 := ihI1.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have hshapeE := trE.dims
  simp only [Basis.tof, Basis.sof, RawAgreeDimsAt] at hshapeE
  change ValSpace.shpOf (orc rho [] []) (.tprod sv0 sv1) =
    srcShp sigma [] (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)) at hshapeE
  rw [RawSpaceFFS.srcShp_tprod_dual] at hshapeE
  simp only [ValSpace.shpOf_tprod] at hshapeE
  have hdsv0 : ValSpace.dof (orc rho [] []) sv0 =
      Module.finrank ℝ V0.carrier := by
    injection hshapeE
  have hdsv1 : ValSpace.dof (orc rho [] []) sv1 =
      Module.finrank ℝ V1.carrier := by
    injection hshapeE with _ htail
    injection htail
  have hdshape := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨sa, sb, hinfer⟩ := eq_tprod_of_shpOf_eq hdshape
  rw [hinfer] at hdshape
  have hfac := tprod_factor_dof_eq_of_shpOf_eq hdshape
  have hd0 : ValSpace.dof (orc rho [] []) sa = S0.length :=
    hfac.1.trans (hdsv0.trans hlb0.finrank_eq)
  have hd1 : ValSpace.dof (orc rho [] []) sb = S1.length :=
    hfac.2.trans (hdsv1.trans hlb1.finrank_eq)
  obtain ⟨ae, heval, haelen, hM⟩ :=
    trace_witness_matrix hlb0 hlb1 trE
  have trI0' : RawTermTraceAt orc sigma rho env0
      (Basis.tof (.tprod (.dual b0) (.dual b0)))
      (.space (.tprod sv0 sv0))
      (denotBasis sigma (.tprod (.dual b0) (.dual b0)))
      (denotTerm sigma (.inner (Basis.sof b0))) := by
    exact trI0
  have trI1' : RawTermTraceAt orc sigma rho env1
      (Basis.tof (.tprod (.dual b1) (.dual b1)))
      (.space (.tprod sv1 sv1))
      (denotBasis sigma (.tprod (.dual b1) (.dual b1)))
      (denotTerm sigma (.inner (Basis.sof b1))) := by
    exact trI1
  obtain ⟨a0, h0eval, ha0len, hMW⟩ :=
    trace_inner_matrix hlb0 hlb0d trI0'
  obtain ⟨a1, h1eval, ha1len, hMV⟩ :=
    trace_inner_matrix hlb1 hlb1d trI1'
  have ha0shape : a0.length = S0.length * S0.length := by
    simpa only [pow_two] using ha0len
  have ha1shape : a1.length = S1.length * S1.length := by
    simpa only [pow_two] using ha1len
  have hnumerical := hnum hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    hinfer hlb0 hlb1 hd0 hd1 heval hM
  have hblocks := hnumerical.1
  obtain ⟨out, hout, houtLen, houtGet⟩ :=
    eval_vtrans_canonicalUI heval h0eval h1eval haelen ha0shape ha1shape hinfer hd0 hd1
      hM hMW hMV hlb0.gram_posDef hlb1.gram_posDef hblocks.1
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have targetShape :
      ValSpace.shpOf (orc rho [] [])
          (.tprod
            (.ffs .kernel (.tprod sv0 sv1)
              (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) =
        srcShp sigma []
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)) := by
    simpa only [Basis.tof, RawAgreeDimsAt] using targetDims
  have targetDof := ValSpace.raw_dof_eq_finrank_of_shpOf targetShape
  have hlbTarget := denotBasis_atSpace_isListBasis sigma Gamma'
    (.tprod
      (.dual (.proj (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)
    (raw_basisValid_mono hbv hle.2) hc.ctxWF_nl hc.envWF_nl
  have targetBasisLen :
      ((denotBasis sigma
        (.tprod
          (.dual (.proj
            (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)).atSpace
        (denotSpace sigma
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)))).length =
        ValSpace.dof (orc rho [] [])
          (.tprod
            (.ffs .kernel (.tprod sv0 sv1)
              (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) :=
    hlbTarget.finrank_eq.symm.trans targetDof.symm
  have inferOut : ValExpr.inferSpaceCtx []
      (.vtrans (.gsvdUI v env0 env1)) =
      .tprod (.ffs .kernel (.tprod sa sb) v) sa := by
    simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient]
  have inferOutDof : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.vtrans (.gsvdUI v env0 env1))) =
      (S0.length - (hlb0.canonical hlb1 f).r) * S0.length := by
    rw [inferOut, ValSpace.dof_tprod, ValSpace.dof_ffs, hblocks.1, hd0]
  have outputShape := hnumerical.2
  have outputDof : out.length = ValSpace.dof (orc rho [] [])
      (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) :=
    (houtLen.trans inferOutDof.symm).trans (dof_eq_of_shpOf_eq outputShape)
  let K : Submodule ℝ V0.carrier := LinearMap.ker f
  let raw : List V0.carrier := BasisFSV.fsvLeft V0 V1 f
    (fun mu => decide (mu = 0)) S0 S1
  have rawEq : raw = List.ofCoords S0 (hlb0.canonical hlb1 f).UI := by
    exact BasisFSV.fsvLeft_eq_canonicalUI hlb0 hlb1 f
  have rawSub : ∀ x ∈ raw, x ∈ K := by
    exact BasisFSV.fsvLeft_subset_ker V0 V1 f S0 S1
  have hlbProj := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1)
    (raw_basisValid_mono hbv.tprod_inv.1.dual_inv hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlbProj' : IsListBasis (HSpace.ofSubmodule V0 K)
      (HSpace.liftToSubmodule K raw) := by
    simpa [V0, V1, S0, S1, f, K, raw, Basis.sof,
      denotSpace, denotSpaceAux, denotTerm, denotBasis,
      BasisDenot.atSpace_vecs_self] using hlbProj
  have projListEq :
      (denotBasis sigma
        (.proj (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1)).atSpace
          (HSpace.ofSubmodule V0 K) =
        HSpace.liftToSubmodule K raw := by
    simp [V0, V1, S0, S1, f, K, raw, denotSpace, denotTerm,
      denotBasis, BasisDenot.atSpace_vecs_self]
  have tensorEq := subtype_tensor_ofCoords V0 K S0
    (hlb0.canonical hlb1 f).UI raw rawEq rawSub hlbProj' out houtGet
  refine ⟨?_, targetDims⟩
  refine ⟨.array out, hout, ?_⟩
  simp only [Basis.tof, Basis.sof, RawAgree]
  rw [LegacyAgree.space_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact targetBasisLen
  · exact outputDof
  · have targetBasisEq := RawSpaceFFS.denotBasis_tprod_dual_atSpace
      sigma (.proj (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1) b0
    simp only [Basis.sof, denotSpace, denotSpaceAux] at targetBasisEq
    rw [projListEq] at targetBasisEq
    let BT :=
      (denotBasis sigma
        (.tprod
          (.dual (.proj
            (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)).atSpace
        (denotSpace sigma
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)))
    let PB := HSpace.tprodOfLists
      (HSpace.dual (HSpace.ofSubmodule V0 K)) V0
      ((HSpace.ofSubmodule V0 K).dualOfList
        (HSpace.liftToSubmodule K raw)) S0
    let N := ValSpace.dof (orc rho [] [])
      (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)
    have BTEq : BT = PB := by
      simpa [BT, PB, V0, K] using targetBasisEq
    have BTLen : BT.length = N := by
      simpa [BT, N] using targetBasisLen
    have tensorFin :
        (dualTensorHomEquiv ℝ (HSpace.ofSubmodule V0 K).carrier
          V0.carrier).symm K.subtype =
        ∑ i : Fin N, out.get i.val • BT.getD i.val 0 := by
      calc
        _ = ∑ q ∈ Finset.range PB.length,
            out.get q • PB.getD q 0 := by
              exact tensorEq
        _ = ∑ q ∈ Finset.range BT.length,
            out.get q • BT.getD q 0 := by rw [BTEq]; rfl
        _ = ∑ q ∈ Finset.range N,
            out.get q • BT.getD q 0 := by rw [BTLen]
        _ = ∑ i : Fin N, out.get i.val • BT.getD i.val 0 :=
          (Fin.sum_univ_eq_sum_range
            (fun i => out.get i • BT.getD i 0) N).symm
    change (embedDVal (HSpace.ofSubmodule V0 K) V0 K.subtype).atSpace
        (HSpace.tprod (HSpace.dual (HSpace.ofSubmodule V0 K)) V0) = _
    unfold embedDVal
    rw [DVal.atSpace_hil_self]
    simpa [BT, N] using tensorFin

/-- Ordinary exact-basis trace for the coimage inclusion. -/
theorem raw_arm_term_embed_coimage_of_numerical
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (_ht : Nonempty (HasType ∅ Gamma (.embed (.coimg s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1))
    (_hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (_hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (_hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : RawMTyAtSubctx orc Gamma Psi
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1)))
    (hnum : RawMEmbedNumericalFactsSubctx orc Gamma Psi b0 b1 e v
      (.vtrans (.gsvdVI v env0 env1))
      (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) :
    RawMTermTraceSubctx orc ∅ Gamma Psi (.embed (.coimg s0 s1 e))
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.vtrans (.gsvdVI v env0 env1))
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) := by
  subst s0
  subst s1
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma b0).atSpace V0
  let S1 := (denotBasis sigma b1).atSpace V1
  let f := (denotTerm sigma e).asLinMap V0 V1
  have hb0v : BasisValid Gamma b0 :=
    (S.Term.basisValid he).tprod_inv.1.dual_inv
  have hb1v : BasisValid Gamma b1 :=
    (S.Term.basisValid he).tprod_inv.2
  have hlb0 : IsListBasis V0 S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb1 : IsListBasis V1 S1 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb0d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b0)
    (raw_basisValid_mono (S.Term.basisValid he).tprod_inv.1 hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb1d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b1)
    (raw_basisValid_mono
      (.dual hb1v (tprod_right_tof_eq (S.Term.basisValid he))) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have trE := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI0 := ihI0.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI1 := ihI1.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have hshapeE := trE.dims
  simp only [Basis.tof, Basis.sof, RawAgreeDimsAt] at hshapeE
  change ValSpace.shpOf (orc rho [] []) (.tprod sv0 sv1) =
    srcShp sigma [] (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)) at hshapeE
  rw [RawSpaceFFS.srcShp_tprod_dual] at hshapeE
  simp only [ValSpace.shpOf_tprod] at hshapeE
  have hdsv0 : ValSpace.dof (orc rho [] []) sv0 =
      Module.finrank ℝ V0.carrier := by
    injection hshapeE
  have hdsv1 : ValSpace.dof (orc rho [] []) sv1 =
      Module.finrank ℝ V1.carrier := by
    injection hshapeE with _ htail
    injection htail
  have hdshape := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨sa, sb, hinfer⟩ := eq_tprod_of_shpOf_eq hdshape
  rw [hinfer] at hdshape
  have hfac := tprod_factor_dof_eq_of_shpOf_eq hdshape
  have hd0 : ValSpace.dof (orc rho [] []) sa = S0.length :=
    hfac.1.trans (hdsv0.trans hlb0.finrank_eq)
  have hd1 : ValSpace.dof (orc rho [] []) sb = S1.length :=
    hfac.2.trans (hdsv1.trans hlb1.finrank_eq)
  obtain ⟨ae, heval, haelen, hM⟩ :=
    trace_witness_matrix hlb0 hlb1 trE
  have trI0' : RawTermTraceAt orc sigma rho env0
      (Basis.tof (.tprod (.dual b0) (.dual b0)))
      (.space (.tprod sv0 sv0))
      (denotBasis sigma (.tprod (.dual b0) (.dual b0)))
      (denotTerm sigma (.inner (Basis.sof b0))) := trI0
  have trI1' : RawTermTraceAt orc sigma rho env1
      (Basis.tof (.tprod (.dual b1) (.dual b1)))
      (.space (.tprod sv1 sv1))
      (denotBasis sigma (.tprod (.dual b1) (.dual b1)))
      (denotTerm sigma (.inner (Basis.sof b1))) := trI1
  obtain ⟨a0, h0eval, ha0len, hMW⟩ :=
    trace_inner_matrix hlb0 hlb0d trI0'
  obtain ⟨a1, h1eval, ha1len, hMV⟩ :=
    trace_inner_matrix hlb1 hlb1d trI1'
  have ha0shape : a0.length = S0.length * S0.length := by
    simpa only [pow_two] using ha0len
  have ha1shape : a1.length = S1.length * S1.length := by
    simpa only [pow_two] using ha1len
  have hnumerical := hnum hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    hinfer hlb0 hlb1 hd0 hd1 heval hM
  have hblocks := hnumerical.1
  obtain ⟨out, hout, houtLen, houtGet⟩ :=
    eval_vtrans_canonicalVI heval h0eval h1eval haelen ha0shape ha1shape hinfer hd0 hd1
      hM hMW hMV hlb0.gram_posDef hlb1.gram_posDef hblocks.2.2.2
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have targetShape :
      ValSpace.shpOf (orc rho [] [])
          (.tprod
            (.ffs .coimage (.tprod sv0 sv1)
              (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) =
        srcShp sigma []
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)) := by
    simpa only [Basis.tof, RawAgreeDimsAt] using targetDims
  have targetDof := ValSpace.raw_dof_eq_finrank_of_shpOf targetShape
  have hlbTarget := denotBasis_atSpace_isListBasis sigma Gamma'
    (.tprod
      (.dual (.proj (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)
    (raw_basisValid_mono hbv hle.2) hc.ctxWF_nl hc.envWF_nl
  have targetBasisLen :
      ((denotBasis sigma
        (.tprod
          (.dual (.proj
            (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)).atSpace
        (denotSpace sigma
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)))).length =
        ValSpace.dof (orc rho [] [])
          (.tprod
            (.ffs .coimage (.tprod sv0 sv1)
              (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) :=
    hlbTarget.finrank_eq.symm.trans targetDof.symm
  have inferOut : ValExpr.inferSpaceCtx []
      (.vtrans (.gsvdVI v env0 env1)) =
      .tprod (.ffs .coimage (.tprod sa sb) v) sb := by
    simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient]
  have inferOutDof : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.vtrans (.gsvdVI v env0 env1))) =
      (S1.length - (hlb0.canonical hlb1 f).r) * S1.length := by
    rw [inferOut, ValSpace.dof_tprod, ValSpace.dof_ffs,
      hblocks.2.2.2, hd1]
  have outputShape := hnumerical.2
  have outputDof : out.length = ValSpace.dof (orc rho [] [])
      (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) :=
    (houtLen.trans inferOutDof.symm).trans (dof_eq_of_shpOf_eq outputShape)
  let K : Submodule ℝ V1.carrier :=
    Submodule.orthRel V1.innerProduct (LinearMap.range f)
  let raw : List V1.carrier := BasisFSV.fsvRight V0 V1 f
    (fun mu => decide (mu = 0)) S0 S1
  have rawEq : raw = List.ofCoords S1 (hlb0.canonical hlb1 f).VI := by
    exact BasisFSV.fsvRight_eq_canonicalVI hlb0 hlb1 f
  have rawSub : ∀ x ∈ raw, x ∈ K := by
    exact BasisFSV.fsvRight_subset_coimg V0 V1 f S0 S1
  have hlbProj := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1)
    (raw_basisValid_mono hbv.tprod_inv.1.dual_inv hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlbProj' : IsListBasis (HSpace.ofSubmodule V1 K)
      (HSpace.liftToSubmodule K raw) := by
    simpa [V0, V1, S0, S1, f, K, raw, Basis.sof,
      denotSpace, denotSpaceAux, denotTerm, denotBasis,
      BasisDenot.atSpace_vecs_self] using hlbProj
  have projListEq :
      (denotBasis sigma
        (.proj (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1)).atSpace
          (HSpace.ofSubmodule V1 K) =
        HSpace.liftToSubmodule K raw := by
    simp [V0, V1, S0, S1, f, K, raw, denotSpace, denotTerm,
      denotBasis, BasisDenot.atSpace_vecs_self]
  have tensorEq := subtype_tensor_ofCoords V1 K S1
    (hlb0.canonical hlb1 f).VI raw rawEq rawSub hlbProj' out houtGet
  refine ⟨?_, targetDims⟩
  refine ⟨.array out, hout, ?_⟩
  simp only [Basis.tof, Basis.sof, RawAgree]
  rw [LegacyAgree.space_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact targetBasisLen
  · exact outputDof
  · have targetBasisEq := RawSpaceFFS.denotBasis_tprod_dual_atSpace
      sigma (.proj (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1) b1
    simp only [Basis.sof, denotSpace, denotSpaceAux] at targetBasisEq
    rw [projListEq] at targetBasisEq
    let BT :=
      (denotBasis sigma
        (.tprod
          (.dual (.proj
            (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)).atSpace
        (denotSpace sigma
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)))
    let PB := HSpace.tprodOfLists
      (HSpace.dual (HSpace.ofSubmodule V1 K)) V1
      ((HSpace.ofSubmodule V1 K).dualOfList
        (HSpace.liftToSubmodule K raw)) S1
    let N := ValSpace.dof (orc rho [] [])
      (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)
    have BTEq : BT = PB := by
      simpa [BT, PB, V1, K] using targetBasisEq
    have BTLen : BT.length = N := by
      simpa [BT, N] using targetBasisLen
    have tensorFin :
        (dualTensorHomEquiv ℝ (HSpace.ofSubmodule V1 K).carrier
          V1.carrier).symm K.subtype =
        ∑ i : Fin N, out.get i.val • BT.getD i.val 0 := by
      calc
        _ = ∑ q ∈ Finset.range PB.length,
            out.get q • PB.getD q 0 := by exact tensorEq
        _ = ∑ q ∈ Finset.range BT.length,
            out.get q • BT.getD q 0 := by rw [BTEq]; rfl
        _ = ∑ q ∈ Finset.range N,
            out.get q • BT.getD q 0 := by rw [BTLen]
        _ = ∑ i : Fin N, out.get i.val • BT.getD i.val 0 :=
          (Fin.sum_univ_eq_sum_range
            (fun i => out.get i • BT.getD i 0) N).symm
    change (embedDVal (HSpace.ofSubmodule V1 K) V1 K.subtype).atSpace
        (HSpace.tprod (HSpace.dual (HSpace.ofSubmodule V1 K)) V1) = _
    unfold embedDVal
    rw [DVal.atSpace_hil_self]
    simpa [BT, N] using tensorFin

/-- Ordinary exact-basis trace for the image inclusion. -/
theorem raw_arm_term_embed_image_of_numerical
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (_ht : Nonempty (HasType ∅ Gamma (.embed (.img s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1))
    (_hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (_hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (_hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : RawMTyAtSubctx orc Gamma Psi
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1)))
    (hnum : RawMEmbedNumericalFactsSubctx orc Gamma Psi b0 b1 e v
      (.vtrans (.gsvdV v env0 env1))
      (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) :
    RawMTermTraceSubctx orc ∅ Gamma Psi (.embed (.img s0 s1 e))
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.vtrans (.gsvdV v env0 env1))
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) := by
  subst s0
  subst s1
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma b0).atSpace V0
  let S1 := (denotBasis sigma b1).atSpace V1
  let f := (denotTerm sigma e).asLinMap V0 V1
  have hb0v : BasisValid Gamma b0 :=
    (S.Term.basisValid he).tprod_inv.1.dual_inv
  have hb1v : BasisValid Gamma b1 :=
    (S.Term.basisValid he).tprod_inv.2
  have hlb0 : IsListBasis V0 S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb1 : IsListBasis V1 S1 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb0d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b0)
    (raw_basisValid_mono (S.Term.basisValid he).tprod_inv.1 hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb1d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b1)
    (raw_basisValid_mono
      (.dual hb1v (tprod_right_tof_eq (S.Term.basisValid he))) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have trE := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI0 := ihI0.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI1 := ihI1.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have hshapeE := trE.dims
  simp only [Basis.tof, Basis.sof, RawAgreeDimsAt] at hshapeE
  change ValSpace.shpOf (orc rho [] []) (.tprod sv0 sv1) =
    srcShp sigma [] (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)) at hshapeE
  rw [RawSpaceFFS.srcShp_tprod_dual] at hshapeE
  simp only [ValSpace.shpOf_tprod] at hshapeE
  have hdsv0 : ValSpace.dof (orc rho [] []) sv0 =
      Module.finrank ℝ V0.carrier := by
    injection hshapeE
  have hdsv1 : ValSpace.dof (orc rho [] []) sv1 =
      Module.finrank ℝ V1.carrier := by
    injection hshapeE with _ htail
    injection htail
  have hdshape := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨sa, sb, hinfer⟩ := eq_tprod_of_shpOf_eq hdshape
  rw [hinfer] at hdshape
  have hfac := tprod_factor_dof_eq_of_shpOf_eq hdshape
  have hd0 : ValSpace.dof (orc rho [] []) sa = S0.length :=
    hfac.1.trans (hdsv0.trans hlb0.finrank_eq)
  have hd1 : ValSpace.dof (orc rho [] []) sb = S1.length :=
    hfac.2.trans (hdsv1.trans hlb1.finrank_eq)
  obtain ⟨ae, heval, haelen, hM⟩ :=
    trace_witness_matrix hlb0 hlb1 trE
  have trI0' : RawTermTraceAt orc sigma rho env0
      (Basis.tof (.tprod (.dual b0) (.dual b0)))
      (.space (.tprod sv0 sv0))
      (denotBasis sigma (.tprod (.dual b0) (.dual b0)))
      (denotTerm sigma (.inner (Basis.sof b0))) := trI0
  have trI1' : RawTermTraceAt orc sigma rho env1
      (Basis.tof (.tprod (.dual b1) (.dual b1)))
      (.space (.tprod sv1 sv1))
      (denotBasis sigma (.tprod (.dual b1) (.dual b1)))
      (denotTerm sigma (.inner (Basis.sof b1))) := trI1
  obtain ⟨a0, h0eval, ha0len, hMW⟩ :=
    trace_inner_matrix hlb0 hlb0d trI0'
  obtain ⟨a1, h1eval, ha1len, hMV⟩ :=
    trace_inner_matrix hlb1 hlb1d trI1'
  have ha0shape : a0.length = S0.length * S0.length := by
    simpa only [pow_two] using ha0len
  have ha1shape : a1.length = S1.length * S1.length := by
    simpa only [pow_two] using ha1len
  have hnumerical := hnum hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    hinfer hlb0 hlb1 hd0 hd1 heval hM
  have hblocks := hnumerical.1
  obtain ⟨out, hout, houtLen, houtGet⟩ :=
    eval_vtrans_canonicalV heval h0eval h1eval haelen ha0shape ha1shape hinfer hd0 hd1
      hM hMW hMV hlb0.gram_posDef hlb1.gram_posDef hblocks.2.2.1
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have targetShape :
      ValSpace.shpOf (orc rho [] [])
          (.tprod
            (.ffs .image (.tprod sv0 sv1)
              (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) =
        srcShp sigma []
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)) := by
    simpa only [Basis.tof, RawAgreeDimsAt] using targetDims
  have targetDof := ValSpace.raw_dof_eq_finrank_of_shpOf targetShape
  have hlbTarget := denotBasis_atSpace_isListBasis sigma Gamma'
    (.tprod
      (.dual (.proj (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)
    (raw_basisValid_mono hbv hle.2) hc.ctxWF_nl hc.envWF_nl
  have targetBasisLen :
      ((denotBasis sigma
        (.tprod
          (.dual (.proj
            (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)).atSpace
        (denotSpace sigma
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)))).length =
        ValSpace.dof (orc rho [] [])
          (.tprod
            (.ffs .image (.tprod sv0 sv1)
              (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) :=
    hlbTarget.finrank_eq.symm.trans targetDof.symm
  have inferOut : ValExpr.inferSpaceCtx []
      (.vtrans (.gsvdV v env0 env1)) =
      .tprod (.ffs .image (.tprod sa sb) v) sb := by
    simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient]
  have inferOutDof : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.vtrans (.gsvdV v env0 env1))) =
      (hlb0.canonical hlb1 f).r * S1.length := by
    rw [inferOut, ValSpace.dof_tprod, ValSpace.dof_ffs,
      hblocks.2.2.1, hd1]
  have outputShape := hnumerical.2
  have outputDof : out.length = ValSpace.dof (orc rho [] [])
      (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) :=
    (houtLen.trans inferOutDof.symm).trans (dof_eq_of_shpOf_eq outputShape)
  let K : Submodule ℝ V1.carrier := LinearMap.range f
  let raw : List V1.carrier := BasisFSV.fsvRight V0 V1 f
    (fun mu => decide (mu ≠ 0)) S0 S1
  have rawEq : raw = List.ofCoords S1 (hlb0.canonical hlb1 f).V := by
    exact BasisFSV.fsvRight_eq_canonicalV hlb0 hlb1 f
  have rawSub : ∀ x ∈ raw, x ∈ K := by
    exact BasisFSV.fsvRight_subset_range V0 V1 f S0 S1
  have hlbProj := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)
    (raw_basisValid_mono hbv.tprod_inv.1.dual_inv hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlbProj' : IsListBasis (HSpace.ofSubmodule V1 K)
      (HSpace.liftToSubmodule K raw) := by
    simpa [V0, V1, S0, S1, f, K, raw, Basis.sof,
      denotSpace, denotSpaceAux, denotTerm, denotBasis,
      BasisDenot.atSpace_vecs_self] using hlbProj
  have projListEq :
      (denotBasis sigma
        (.proj (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)).atSpace
          (HSpace.ofSubmodule V1 K) =
        HSpace.liftToSubmodule K raw := by
    simp [V0, V1, S0, S1, f, K, raw, denotSpace, denotTerm,
      denotBasis, BasisDenot.atSpace_vecs_self]
  have tensorEq := subtype_tensor_ofCoords V1 K S1
    (hlb0.canonical hlb1 f).V raw rawEq rawSub hlbProj' out houtGet
  refine ⟨?_, targetDims⟩
  refine ⟨.array out, hout, ?_⟩
  simp only [Basis.tof, Basis.sof, RawAgree]
  rw [LegacyAgree.space_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact targetBasisLen
  · exact outputDof
  · have targetBasisEq := RawSpaceFFS.denotBasis_tprod_dual_atSpace
      sigma (.proj (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1) b1
    simp only [Basis.sof, denotSpace, denotSpaceAux] at targetBasisEq
    rw [projListEq] at targetBasisEq
    let BT :=
      (denotBasis sigma
        (.tprod
          (.dual (.proj
            (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)).atSpace
        (denotSpace sigma
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b1)))
    let PB := HSpace.tprodOfLists
      (HSpace.dual (HSpace.ofSubmodule V1 K)) V1
      ((HSpace.ofSubmodule V1 K).dualOfList
        (HSpace.liftToSubmodule K raw)) S1
    let N := ValSpace.dof (orc rho [] [])
      (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)
    have BTEq : BT = PB := by
      simpa [BT, PB, V1, K] using targetBasisEq
    have BTLen : BT.length = N := by
      simpa [BT, N] using targetBasisLen
    have tensorFin :
        (dualTensorHomEquiv ℝ (HSpace.ofSubmodule V1 K).carrier
          V1.carrier).symm K.subtype =
        ∑ i : Fin N, out.get i.val • BT.getD i.val 0 := by
      calc
        _ = ∑ q ∈ Finset.range PB.length,
            out.get q • PB.getD q 0 := by exact tensorEq
        _ = ∑ q ∈ Finset.range BT.length,
            out.get q • BT.getD q 0 := by rw [BTEq]; rfl
        _ = ∑ q ∈ Finset.range N,
            out.get q • BT.getD q 0 := by rw [BTLen]
        _ = ∑ i : Fin N, out.get i.val • BT.getD i.val 0 :=
          (Fin.sum_univ_eq_sum_range
            (fun i => out.get i • BT.getD i 0) N).symm
    change (embedDVal (HSpace.ofSubmodule V1 K) V1 K.subtype).atSpace
        (HSpace.tprod (HSpace.dual (HSpace.ofSubmodule V1 K)) V1) = _
    unfold embedDVal
    rw [DVal.atSpace_hil_self]
    simpa [BT, N] using tensorFin

/-- Ordinary exact-basis trace for the cokernel inclusion. -/
theorem raw_arm_term_embed_cokernel_of_numerical
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (_ht : Nonempty (HasType ∅ Gamma (.embed (.coker s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0))
    (_hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (_hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (_hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : RawMTyAtSubctx orc Gamma Psi
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1)))
    (hnum : RawMEmbedNumericalFactsSubctx orc Gamma Psi b0 b1 e v
      (.vtrans (.gsvdU v env0 env1))
      (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) :
    RawMTermTraceSubctx orc ∅ Gamma Psi (.embed (.coker s0 s1 e))
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.vtrans (.gsvdU v env0 env1))
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) := by
  subst s0
  subst s1
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma b0).atSpace V0
  let S1 := (denotBasis sigma b1).atSpace V1
  let f := (denotTerm sigma e).asLinMap V0 V1
  have hb0v : BasisValid Gamma b0 :=
    (S.Term.basisValid he).tprod_inv.1.dual_inv
  have hb1v : BasisValid Gamma b1 :=
    (S.Term.basisValid he).tprod_inv.2
  have hlb0 : IsListBasis V0 S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb1 : IsListBasis V1 S1 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb0d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b0)
    (raw_basisValid_mono (S.Term.basisValid he).tprod_inv.1 hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb1d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b1)
    (raw_basisValid_mono
      (.dual hb1v (tprod_right_tof_eq (S.Term.basisValid he))) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have trE := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI0 := ihI0.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI1 := ihI1.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have hshapeE := trE.dims
  simp only [Basis.tof, Basis.sof, RawAgreeDimsAt] at hshapeE
  change ValSpace.shpOf (orc rho [] []) (.tprod sv0 sv1) =
    srcShp sigma [] (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)) at hshapeE
  rw [RawSpaceFFS.srcShp_tprod_dual] at hshapeE
  simp only [ValSpace.shpOf_tprod] at hshapeE
  have hdsv0 : ValSpace.dof (orc rho [] []) sv0 =
      Module.finrank ℝ V0.carrier := by
    injection hshapeE
  have hdsv1 : ValSpace.dof (orc rho [] []) sv1 =
      Module.finrank ℝ V1.carrier := by
    injection hshapeE with _ htail
    injection htail
  have hdshape := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨sa, sb, hinfer⟩ := eq_tprod_of_shpOf_eq hdshape
  rw [hinfer] at hdshape
  have hfac := tprod_factor_dof_eq_of_shpOf_eq hdshape
  have hd0 : ValSpace.dof (orc rho [] []) sa = S0.length :=
    hfac.1.trans (hdsv0.trans hlb0.finrank_eq)
  have hd1 : ValSpace.dof (orc rho [] []) sb = S1.length :=
    hfac.2.trans (hdsv1.trans hlb1.finrank_eq)
  obtain ⟨ae, heval, haelen, hM⟩ :=
    trace_witness_matrix hlb0 hlb1 trE
  have trI0' : RawTermTraceAt orc sigma rho env0
      (Basis.tof (.tprod (.dual b0) (.dual b0)))
      (.space (.tprod sv0 sv0))
      (denotBasis sigma (.tprod (.dual b0) (.dual b0)))
      (denotTerm sigma (.inner (Basis.sof b0))) := trI0
  have trI1' : RawTermTraceAt orc sigma rho env1
      (Basis.tof (.tprod (.dual b1) (.dual b1)))
      (.space (.tprod sv1 sv1))
      (denotBasis sigma (.tprod (.dual b1) (.dual b1)))
      (denotTerm sigma (.inner (Basis.sof b1))) := trI1
  obtain ⟨a0, h0eval, ha0len, hMW⟩ :=
    trace_inner_matrix hlb0 hlb0d trI0'
  obtain ⟨a1, h1eval, ha1len, hMV⟩ :=
    trace_inner_matrix hlb1 hlb1d trI1'
  have ha0shape : a0.length = S0.length * S0.length := by
    simpa only [pow_two] using ha0len
  have ha1shape : a1.length = S1.length * S1.length := by
    simpa only [pow_two] using ha1len
  have hnumerical := hnum hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    hinfer hlb0 hlb1 hd0 hd1 heval hM
  have hblocks := hnumerical.1
  obtain ⟨out, hout, houtLen, houtGet⟩ :=
    eval_vtrans_canonicalU heval h0eval h1eval haelen ha0shape ha1shape hinfer hd0 hd1
      hM hMW hMV hlb0.gram_posDef hlb1.gram_posDef hblocks.2.1
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have targetShape :
      ValSpace.shpOf (orc rho [] [])
          (.tprod
            (.ffs .cokernel (.tprod sv0 sv1)
              (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) =
        srcShp sigma []
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)) := by
    simpa only [Basis.tof, RawAgreeDimsAt] using targetDims
  have targetDof := ValSpace.raw_dof_eq_finrank_of_shpOf targetShape
  have hlbTarget := denotBasis_atSpace_isListBasis sigma Gamma'
    (.tprod
      (.dual (.proj (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)
    (raw_basisValid_mono hbv hle.2) hc.ctxWF_nl hc.envWF_nl
  have targetBasisLen :
      ((denotBasis sigma
        (.tprod
          (.dual (.proj
            (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)).atSpace
        (denotSpace sigma
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)))).length =
        ValSpace.dof (orc rho [] [])
          (.tprod
            (.ffs .cokernel (.tprod sv0 sv1)
              (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) :=
    hlbTarget.finrank_eq.symm.trans targetDof.symm
  have inferOut : ValExpr.inferSpaceCtx []
      (.vtrans (.gsvdU v env0 env1)) =
      .tprod (.ffs .cokernel (.tprod sa sb) v) sa := by
    simp only [ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient]
  have inferOutDof : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.vtrans (.gsvdU v env0 env1))) =
      (hlb0.canonical hlb1 f).r * S0.length := by
    rw [inferOut, ValSpace.dof_tprod, ValSpace.dof_ffs, hblocks.2.1, hd0]
  have outputShape := hnumerical.2
  have outputDof : out.length = ValSpace.dof (orc rho [] [])
      (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) :=
    (houtLen.trans inferOutDof.symm).trans (dof_eq_of_shpOf_eq outputShape)
  let K : Submodule ℝ V0.carrier :=
    Submodule.orthRel V0.innerProduct (LinearMap.ker f)
  let raw : List V0.carrier := BasisFSV.fsvLeft V0 V1 f
    (fun mu => decide (mu ≠ 0)) S0 S1
  have rawEq : raw = List.ofCoords S0 (hlb0.canonical hlb1 f).U := by
    exact BasisFSV.fsvLeft_eq_canonicalU hlb0 hlb1 f
  have rawSub : ∀ x ∈ raw, x ∈ K := by
    exact BasisFSV.fsvLeft_subset_coker V0 V1 f S0 S1
  have hlbProj := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)
    (raw_basisValid_mono hbv.tprod_inv.1.dual_inv hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlbProj' : IsListBasis (HSpace.ofSubmodule V0 K)
      (HSpace.liftToSubmodule K raw) := by
    simpa [V0, V1, S0, S1, f, K, raw, Basis.sof,
      denotSpace, denotSpaceAux, denotTerm, denotBasis,
      BasisDenot.atSpace_vecs_self] using hlbProj
  have projListEq :
      (denotBasis sigma
        (.proj (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)).atSpace
          (HSpace.ofSubmodule V0 K) =
        HSpace.liftToSubmodule K raw := by
    simp [V0, V1, S0, S1, f, K, raw, denotSpace, denotTerm,
      denotBasis, BasisDenot.atSpace_vecs_self]
  have tensorEq := subtype_tensor_ofCoords V0 K S0
    (hlb0.canonical hlb1 f).U raw rawEq rawSub hlbProj' out houtGet
  refine ⟨?_, targetDims⟩
  refine ⟨.array out, hout, ?_⟩
  simp only [Basis.tof, Basis.sof, RawAgree]
  rw [LegacyAgree.space_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact targetBasisLen
  · exact outputDof
  · have targetBasisEq := RawSpaceFFS.denotBasis_tprod_dual_atSpace
      sigma (.proj (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1) b0
    simp only [Basis.sof, denotSpace, denotSpaceAux] at targetBasisEq
    rw [projListEq] at targetBasisEq
    let BT :=
      (denotBasis sigma
        (.tprod
          (.dual (.proj
            (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)).atSpace
        (denotSpace sigma
          (Basis.sof
            (.tprod
              (.dual (.proj
                (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)) b0)))
    let PB := HSpace.tprodOfLists
      (HSpace.dual (HSpace.ofSubmodule V0 K)) V0
      ((HSpace.ofSubmodule V0 K).dualOfList
        (HSpace.liftToSubmodule K raw)) S0
    let N := ValSpace.dof (orc rho [] [])
      (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)
    have BTEq : BT = PB := by
      simpa [BT, PB, V0, K] using targetBasisEq
    have BTLen : BT.length = N := by
      simpa [BT, N] using targetBasisLen
    have tensorFin :
        (dualTensorHomEquiv ℝ (HSpace.ofSubmodule V0 K).carrier
          V0.carrier).symm K.subtype =
        ∑ i : Fin N, out.get i.val • BT.getD i.val 0 := by
      calc
        _ = ∑ q ∈ Finset.range PB.length,
            out.get q • PB.getD q 0 := by exact tensorEq
        _ = ∑ q ∈ Finset.range BT.length,
            out.get q • BT.getD q 0 := by rw [BTEq]; rfl
        _ = ∑ q ∈ Finset.range N,
            out.get q • BT.getD q 0 := by rw [BTLen]
        _ = ∑ i : Fin N, out.get i.val • BT.getD i.val 0 :=
          (Fin.sum_univ_eq_sum_range
            (fun i => out.get i • BT.getD i 0) N).symm
    change (embedDVal (HSpace.ofSubmodule V0 K) V0 K.subtype).atSpace
        (HSpace.tprod (HSpace.dual (HSpace.ofSubmodule V0 K)) V0) = _
    unfold embedDVal
    rw [DVal.atSpace_hil_self]
    simpa [BT, N] using tensorFin

/-! ## Paired trace/inferred-space wrappers -/

theorem raw_arm_term_embed_kernel_facts
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (ht : Nonempty (HasType ∅ Gamma (.embed (.ker s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0))
    (hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : RawMTyAtSubctx orc Gamma Psi
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    RawTermDofFactsSubctx orc ∅ Gamma Psi (.embed (.ker s0 s1 e))
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.vtrans (.gsvdUI v env0 env1))
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) :=
  ⟨raw_arm_term_embed_kernel_of_numerical hs0 hs1 ht hbv hTy hi0 hi1 he
      ihTy ihI0 ihI1 ihE
      (rawMEmbedNumericalFacts_of_spec hspec he
        (arm_embed_kernel_dof (env0 := env0) (env1 := env1) hspec he ihE)),
    arm_embed_kernel_dof (env0 := env0) (env1 := env1) hspec he ihE⟩

theorem raw_arm_term_embed_cokernel_facts
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (ht : Nonempty (HasType ∅ Gamma (.embed (.coker s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0))
    (hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : RawMTyAtSubctx orc Gamma Psi
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    RawTermDofFactsSubctx orc ∅ Gamma Psi (.embed (.coker s0 s1 e))
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.vtrans (.gsvdU v env0 env1))
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) :=
  ⟨raw_arm_term_embed_cokernel_of_numerical hs0 hs1 ht hbv hTy hi0 hi1 he
      ihTy ihI0 ihI1 ihE
      (rawMEmbedNumericalFacts_of_spec hspec he
        (arm_embed_cokernel_dof (env0 := env0) (env1 := env1) hspec he ihE)),
    arm_embed_cokernel_dof (env0 := env0) (env1 := env1) hspec he ihE⟩

theorem raw_arm_term_embed_image_facts
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (ht : Nonempty (HasType ∅ Gamma (.embed (.img s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1))
    (hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : RawMTyAtSubctx orc Gamma Psi
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    RawTermDofFactsSubctx orc ∅ Gamma Psi (.embed (.img s0 s1 e))
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.vtrans (.gsvdV v env0 env1))
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) :=
  ⟨raw_arm_term_embed_image_of_numerical hs0 hs1 ht hbv hTy hi0 hi1 he
      ihTy ihI0 ihI1 ihE
      (rawMEmbedNumericalFacts_of_spec hspec he
        (arm_embed_image_dof (env0 := env0) (env1 := env1) hspec he ihE)),
    arm_embed_image_dof (env0 := env0) (env1 := env1) hspec he ihE⟩

theorem raw_arm_term_embed_coimage_facts
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (ht : Nonempty (HasType ∅ Gamma (.embed (.coimg s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1))
    (hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : RawMTyAtSubctx orc Gamma Psi
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (ihI0 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : RawTermDofFactsSubctx orc ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    RawTermDofFactsSubctx orc ∅ Gamma Psi (.embed (.coimg s0 s1 e))
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.vtrans (.gsvdVI v env0 env1))
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) :=
  ⟨raw_arm_term_embed_coimage_of_numerical hs0 hs1 ht hbv hTy hi0 hi1 he
      ihTy ihI0 ihI1 ihE
      (rawMEmbedNumericalFacts_of_spec hspec he
        (arm_embed_coimage_dof (env0 := env0) (env1 := env1) hspec he ihE)),
    arm_embed_coimage_dof (env0 := env0) (env1 := env1) hspec he ihE⟩

end RawTermEmbed

end GLang
