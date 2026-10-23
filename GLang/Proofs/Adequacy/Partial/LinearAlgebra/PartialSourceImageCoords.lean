import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCanonicalBlocks
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceProjectionCore
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceLinearSums
import GLang.Numerics.SVD.ValueImageCoords
import GLang.Numerics.Spectral.BasisCanonicalImage
namespace GLang.PartialAdequacy.ImageCoords
open scoped BigOperators
open PartialValueEval
theorem eval_idelta_matrix (orc : PartialFFSOracleSem) (rho : ValEnvSem)
    (s : ValSpace) (n : Nat) (hd : ValSpace.dofPartial (orc rho [] []) s = .ok n) :
    ∃ a : FlatArray, denotValB_partial orc rho [] [] (.idelta s) = .ok (.array a) ∧
      a.length = n * n ∧ denotAsMatrix n n a.get = 1 := by
  rw [denotValB_partial]
  have hg : dimensions (orc rho [] []) [s] = .ok () := by
    simp [dimensions, hd, bind, Except.bind]
  rw [withDimensions, hg]
  dsimp only
  simp only [ValExpr.inferSpaceCtx, ValSpace.dof_tprod, dof_numbers _ _ _ hd]
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
    {rho : ValEnvSem}
    {v env0 env1 : ValExpr} {sa sb : ValSpace}
    {d0 d1 : Nat} {M : Matrix (Fin d1) (Fin d0) ℝ}
    {MW : Matrix (Fin d0) (Fin d0) ℝ} {MV : Matrix (Fin d1) (Fin d1) ℝ}
    {ae a0 a1 : FlatArray}
    (he : denotValB_partial PartialDirectOracle.oracle rho [] [] v = .ok (.array ae))
    (he0 : denotValB_partial PartialDirectOracle.oracle rho [] [] env0 = .ok (.array a0))
    (he1 : denotValB_partial PartialDirectOracle.oracle rho [] [] env1 = .ok (.array a1))
    (haelen : ae.length = d0 * d1) (ha0len : a0.length = d0 * d0)
    (ha1len : a1.length = d1 * d1)
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hd0 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) sa = .ok d0)
    (hd1 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) sb = .ok d1)
    (hM : (denotAsMatrix d0 d1 ae.get).transpose = M)
    (hMW : denotAsMatrix d0 d0 a0.get = MW)
    (hMV : denotAsMatrix d1 d1 a1.get = MV)
    (hG : MW.PosDef) (hH : MV.PosDef)
    (hgd : ∃ k, (ValExpr.inferSpaceCtx [] env0).dofPartial (PartialDirectOracle.oracle rho [] []) = .ok k)
    (hhd : ∃ k, (ValExpr.inferSpaceCtx [] env1).dofPartial (PartialDirectOracle.oracle rho [] []) = .ok k)
    (hf : ValueQueryDependencies.Finite (.expr [] v)) :
    ∃ out : FlatArray,
      denotValB_partial PartialDirectOracle.oracle rho [] [] (.gsvdV v env0 env1) = .ok (.array out) ∧
      out.length = d1 * M.rank ∧ ∀ (i : Fin d1) (j : Fin M.rank),
        out.get (i.val * M.rank + j.val) =
          (BasisSpectral.canonicalBlocks M MW MV hG hH).V i j := by
  have hleaf : ValueCanonicalFSV.eval .image d0 d1 ae a0 a1 =
      .ok ⟨d1, M.rank, (BasisSpectral.canonicalBlocks M MW MV hG hH).V⟩ := by
    rw [ValueCanonicalFSV.eval_ok _ _ _ _ _ _ ⟨haelen, ha0len, ha1len⟩
      (hMW.symm ▸ hG) (hMV.symm ▸ hH)]
    simp only [hM, hMW, hMV]
    congr 1
  obtain ⟨hdrow,hdcol⟩ := canonical_dimensions he hd0 hd1 hleaf ((hinfer ▸ hf.inferSpace).ffs hf)
  have hout : (ValExpr.inferSpaceCtx [] (.gsvdV v env0 env1)).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok (d1*M.rank) := by
    simp only [ValExpr.inferSpaceCtx, hinfer]
    exact dof_tprod_ok hdrow hdcol
  have heval := eval_canonicalFSV (p := .image)
    (r := ⟨d1, M.rank, (BasisSpectral.canonicalBlocks M MW MV hG hH).V⟩) he he0 he1 hinfer hd0 hd1 hgd hhd hout hleaf
  refine ⟨_, heval, rfl, ?_⟩
  intro i j
  simpa only [Nat.mul_comm] using
    ValueCanonicalFSV.ResultMatrix.flatten_get
      ⟨d1, M.rank, (BasisSpectral.canonicalBlocks M MW MV hG hH).V⟩ i j

theorem eval_of_operands (orc : PartialFFSOracleSem) (rho : ValEnvSem)
    (s0 s1 : ValSpace) (e : ValExpr) (m n r : Nat)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin r) (Fin m) ℝ)
    (V : Matrix (Fin n) (Fin r) ℝ)
    (a u v : FlatArray)
    (h0 : ValSpace.dofPartial (orc rho [] []) s0 = .ok m)
    (h1 : ValSpace.dofPartial (orc rho [] []) s1 = .ok n)
    (hc : orc rho [] [] .cokernel (.tprod s0 s1)
      (ValExpr.reshapBase e (.tprod s0 s1)) = .ok r)
    (hi : orc rho [] [] .image (.tprod s0 s1)
      (ValExpr.reshapBase e (.tprod s0 s1)) = .ok r)
    (ha : denotValB_partial orc rho [] [] (ValExpr.reshapBase e (.tprod s0 s1)) =
      .ok (.array a))
    (hu : denotValB_partial orc rho [] []
      (.vtrans (.gsvdU (ValExpr.reshapBase e (.tprod s0 s1))
        (.idelta s0) (.idelta s1))) = .ok (.array u))
    (hv : denotValB_partial orc rho [] []
      (.gsvdV (ValExpr.reshapBase e (.tprod s0 s1))
        (.idelta s0) (.idelta s1)) = .ok (.array v))
    (haLen : a.length = m * n)
    (huLen : u.length = r * m)
    (hvLen : v.length = n * r)
    (hA : ∀ i j, a.get (i.val * n + j.val) = A i j)
    (hU : ∀ i j, u.get (i.val * m + j.val) = U i j)
    (hV : ∀ i j, v.get (i.val * r + j.val) = V i j) :
    ∃ out : FlatArray,
      denotValB_partial orc rho [] [] (ValExpr.imageCoords (.tprod s0 s1) e) =
        .ok (.array out) ∧ out.length = r * r ∧
      ∀ i j : Fin r, out.get (i.val * r + j.val) = (U * A * V) i j := by
  let w := ValExpr.reshapBase e (.tprod s0 s1)
  let ue := ValExpr.vtrans (.gsvdU w (.idelta s0) (.idelta s1))
  let ve := ValExpr.gsvdV w (.idelta s0) (.idelta s1)
  let sc := ValSpace.ffs .cokernel (.tprod s0 s1) w
  let si := ValSpace.ffs .image (.tprod s0 s1) w
  have hsc : ValSpace.dofPartial (orc rho [] []) sc = .ok r := by simp [sc, w, ValSpace.dofPartial, ValSpace.shpOfPartial, hc, bind, Except.bind, pure, Except.pure]
  have hsi : ValSpace.dofPartial (orc rho [] []) si = .ok r := by simp [si, w, ValSpace.dofPartial, ValSpace.shpOfPartial, hi, bind, Except.bind, pure, Except.pure]
  have hwInfer : ValExpr.inferSpaceCtx [] w = .tprod s0 s1 := rfl
  have huInfer : ValExpr.inferSpaceCtx [] ue = .tprod sc s0 := rfl
  have hvInfer : ValExpr.inferSpaceCtx [] ve = .tprod s1 si := rfl
  obtain ⟨au, hau, hlau, hgetau⟩ := mtm_rectangular orc rho
    (sAux := s0) hwInfer huInfer ha hu hsc h0 h1 haLen huLen
  have hauInfer : ValExpr.inferSpaceCtx [] (.mtm 0 0 s0 s0 w ue) =
      .tprod sc s1 := rfl
  obtain ⟨out, hout, hlen, hget⟩ := mtm_rectangular orc rho
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
theorem eval (rho : ValEnvSem)
    (s0 s1 : ValSpace) (e : ValExpr) (m n : Nat)
    (M : Matrix (Fin n) (Fin m) ℝ) (a : FlatArray)
    (h0 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) s0 = .ok m)
    (h1 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) s1 = .ok n)
    (ha : denotValB_partial PartialDirectOracle.oracle rho [] [] e = .ok (.array a))
    (hlen : a.length = m * n)
    (hM : (denotAsMatrix m n a.get).transpose = M)
    (hc : PartialDirectOracle.oracle rho [] [] .cokernel (.tprod s0 s1)
      (ValExpr.reshapBase e (.tprod s0 s1)) = .ok M.rank)
    (hi : PartialDirectOracle.oracle rho [] [] .image (.tprod s0 s1)
      (ValExpr.reshapBase e (.tprod s0 s1)) = .ok M.rank) :
    ∃ out : FlatArray,
      denotValB_partial PartialDirectOracle.oracle rho [] [] (ValExpr.imageCoords (.tprod s0 s1) e) =
        .ok (.array out) ∧ out.length = M.rank * M.rank ∧
      ∀ i j : Fin M.rank, out.get (i.val * M.rank + j.val) =
        BasisSpectral.standardImageRows M i j := by
  have hf : ValueQueryDependencies.Finite (.expr [] (ValExpr.reshapBase e (.tprod s0 s1))) :=
    (PartialDirectLocality.finite_of_success hc).child (by simp [ValueQueryDependencies.children])
  have hw := reshapeBase_ok ha (by rw [hlen]; exact dof_tprod_ok h0 h1)
  obtain ⟨a0, he0, hl0, hm0⟩ := eval_idelta_matrix PartialDirectOracle.oracle rho s0 m h0
  obtain ⟨a1, he1, hl1, hm1⟩ := eval_idelta_matrix PartialDirectOracle.oracle rho s1 n h1
  obtain ⟨u, hu, hlu, hgu⟩ := eval_vtrans_canonicalU
    hw he0 he1 hlen hl0 hl1 rfl h0 h1 hM hm0 hm1
    Matrix.PosDef.one Matrix.PosDef.one
      ⟨_,dof_tprod_ok h0 h0⟩ ⟨_,dof_tprod_ok h1 h1⟩ hf
  obtain ⟨v, hv, hlv, hgv⟩ := eval_canonicalV
    hw he0 he1 hlen hl0 hl1 rfl h0 h1 hM hm0 hm1
    Matrix.PosDef.one Matrix.PosDef.one
      ⟨_,dof_tprod_ok h0 h0⟩ ⟨_,dof_tprod_ok h1 h1⟩ hf
  apply eval_of_operands PartialDirectOracle.oracle rho s0 s1 e m n M.rank M.transpose
    (BasisSpectral.canonicalBlocks M 1 1 Matrix.PosDef.one Matrix.PosDef.one).U.transpose
    (BasisSpectral.canonicalBlocks M 1 1 Matrix.PosDef.one Matrix.PosDef.one).V
    a u v h0 h1 hc hi hw hu hv hlen hlu hlv ?_ hgu hgv
  intro i j
  have h := congrArg (fun B : Matrix (Fin n) (Fin m) ℝ => B j i) hM
  simpa only [Matrix.transpose_apply, denotAsMatrix, Nat.mul_comm] using h

end GLang.PartialAdequacy.ImageCoords
