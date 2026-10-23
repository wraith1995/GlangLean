import GLang.Numerics.SVD.ValueImageCoords
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobProjections

/-! The two ordinary tensor contractions implementing canonical image
coordinate conversion, factored from their spectral operand proofs. -/

namespace GLang
open scoped BigOperators

namespace RawImageCoords

theorem eval_idelta_matrix (orc : FFSOracleSem) (rho : ValEnvSem)
    (s : ValSpace) (n : Nat) (hd : ValSpace.dof (orc rho [] []) s = n) :
    ∃ a : FlatArray, denotValB_semS orc rho [] [] (.idelta s) = .ok (.array a) ∧
      a.length = n * n ∧ denotAsMatrix n n a.get = 1 := by
  rw [denotValB_semS.eq_8]
  simp only [ValExpr.inferSpaceCtx, ValSpace.dof_tprod, hd]
  refine ⟨_, rfl, rfl, ?_⟩
  ext i j
  have hn : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt)
  have hlt : n * i.val + j.val < n * n := by nlinarith [i.isLt, j.isLt]
  simp [denotAsMatrix, ValValSem.arrayOf, FlatArray.get_ofFn, hlt, hn,
    Nat.mul_add_div (Nat.pos_of_ne_zero hn), Nat.div_eq_of_lt j.isLt,
    Nat.mod_eq_of_lt j.isLt, i.isLt, Matrix.one_apply, Fin.ext_iff]

private theorem pack_castColumns {m k l : ℕ} (h : k = l)
    (M : Matrix (Fin m) (Fin k) ℝ) :
    ValueCanonicalFSV.ResultMatrix.mk m l (BasisSpectral.castColumns h M) =
      ⟨m, k, M⟩ := by
  subst l
  rfl

theorem eval_canonicalV
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {v env0 env1 : ValExpr} {sa sb : ValSpace}
    {d0 d1 : Nat} {M : Matrix (Fin d1) (Fin d0) ℝ}
    {MW : Matrix (Fin d0) (Fin d0) ℝ} {MV : Matrix (Fin d1) (Fin d1) ℝ}
    {ae a0 a1 : FlatArray}
    (he : denotValB_semS orc rho [] [] v = .ok (.array ae))
    (he0 : denotValB_semS orc rho [] [] env0 = .ok (.array a0))
    (he1 : denotValB_semS orc rho [] [] env1 = .ok (.array a1))
    (haelen : ae.length = d0 * d1) (ha0len : a0.length = d0 * d0)
    (ha1len : a1.length = d1 * d1)
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hd0 : ValSpace.dof (orc rho [] []) sa = d0)
    (hd1 : ValSpace.dof (orc rho [] []) sb = d1)
    (hM : (denotAsMatrix d0 d1 ae.get).transpose = M)
    (hMW : denotAsMatrix d0 d0 a0.get = MW)
    (hMV : denotAsMatrix d1 d1 a1.get = MV)
    (hG : MW.PosDef) (hH : MV.PosDef)
    (himage : orc rho [] [] .image (.tprod sa sb) v = M.rank) :
    ∃ out : FlatArray,
      denotValB_semS orc rho [] [] (.gsvdV v env0 env1) = .ok (.array out) ∧
      out.length = d1 * M.rank ∧ ∀ (i : Fin d1) (j : Fin M.rank),
        out.get (i.val * M.rank + j.val) =
          (BasisSpectral.canonicalBlocks M MW MV hG hH).V i j := by
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
  refine ⟨_, heval, rfl, ?_⟩
  intro i j
  simpa only [Nat.mul_comm] using
    ValueCanonicalFSV.ResultMatrix.flatten_get
      ⟨d1, M.rank, (BasisSpectral.canonicalBlocks M MW MV hG hH).V⟩ i j

theorem eval_of_operands (orc : FFSOracleSem) (rho : ValEnvSem)
    (s0 s1 : ValSpace) (e : ValExpr) (m n r : Nat)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin r) (Fin m) ℝ)
    (V : Matrix (Fin n) (Fin r) ℝ)
    (a u v : FlatArray)
    (h0 : ValSpace.dof (orc rho [] []) s0 = m)
    (h1 : ValSpace.dof (orc rho [] []) s1 = n)
    (hc : orc rho [] [] .cokernel (.tprod s0 s1)
      (ValExpr.reshapBase e (.tprod s0 s1)) = r)
    (hi : orc rho [] [] .image (.tprod s0 s1)
      (ValExpr.reshapBase e (.tprod s0 s1)) = r)
    (ha : denotValB_semS orc rho [] [] (ValExpr.reshapBase e (.tprod s0 s1)) =
      .ok (.array a))
    (hu : denotValB_semS orc rho [] []
      (.vtrans (.gsvdU (ValExpr.reshapBase e (.tprod s0 s1))
        (.idelta s0) (.idelta s1))) = .ok (.array u))
    (hv : denotValB_semS orc rho [] []
      (.gsvdV (ValExpr.reshapBase e (.tprod s0 s1))
        (.idelta s0) (.idelta s1)) = .ok (.array v))
    (haLen : a.length = m * n)
    (huLen : u.length = r * m)
    (hvLen : v.length = n * r)
    (hA : ∀ i j, a.get (i.val * n + j.val) = A i j)
    (hU : ∀ i j, u.get (i.val * m + j.val) = U i j)
    (hV : ∀ i j, v.get (i.val * r + j.val) = V i j) :
    ∃ out : FlatArray,
      denotValB_semS orc rho [] [] (ValExpr.imageCoords (.tprod s0 s1) e) =
        .ok (.array out) ∧ out.length = r * r ∧
      ∀ i j : Fin r, out.get (i.val * r + j.val) = (U * A * V) i j := by
  let w := ValExpr.reshapBase e (.tprod s0 s1)
  let ue := ValExpr.vtrans (.gsvdU w (.idelta s0) (.idelta s1))
  let ve := ValExpr.gsvdV w (.idelta s0) (.idelta s1)
  let sc := ValSpace.ffs .cokernel (.tprod s0 s1) w
  let si := ValSpace.ffs .image (.tprod s0 s1) w
  have hsc : ValSpace.dof (orc rho [] []) sc = r := by simpa [sc, w, ValSpace.dof_ffs] using hc
  have hsi : ValSpace.dof (orc rho [] []) si = r := by simpa [si, w, ValSpace.dof_ffs] using hi
  have hwInfer : ValExpr.inferSpaceCtx [] w = .tprod s0 s1 := rfl
  have huInfer : ValExpr.inferSpaceCtx [] ue = .tprod sc s0 := rfl
  have hvInfer : ValExpr.inferSpaceCtx [] ve = .tprod s1 si := rfl
  obtain ⟨au, hau, hlau, hgetau⟩ := raw_mtm_rectangular orc rho
    (sAux := s0) hwInfer huInfer ha hu hsc h0 h1 haLen huLen
  have hauInfer : ValExpr.inferSpaceCtx [] (.mtm 0 0 s0 s0 w ue) =
      .tprod sc s1 := rfl
  obtain ⟨out, hout, hlen, hget⟩ := raw_mtm_rectangular orc rho
    (sAux := s1) hvInfer hauInfer hv hau hsc h1 hsi hvLen hlau
  refine ⟨out, hout, hlen, ?_⟩
  intro i j
  rw [hget _ _ i.isLt j.isLt]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [hV k j, hgetau _ _ i.isLt k.isLt]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [hA l k, hU i l, mul_comm]

end RawImageCoords
end GLang
