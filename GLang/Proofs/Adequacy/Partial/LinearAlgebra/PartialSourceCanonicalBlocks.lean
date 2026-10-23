import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCanonical

namespace GLang.PartialAdequacy

private theorem pack_castColumns {m k l : ℕ} (h : k = l)
    (M : Matrix (Fin m) (Fin k) ℝ) :
    (ValueCanonicalFSV.ResultMatrix.mk m l (BasisSpectral.castColumns h M)) =
      ⟨m, k, M⟩ := by
  subst l
  rfl

theorem eval_vtrans_canonicalUI
    {rho : ValEnvSem}
    {v env0 env1 : ValExpr} {sa sb : ValSpace}
    {d0 d1 : Nat} {M : Matrix (Fin d1) (Fin d0) ℝ}
    {MW : Matrix (Fin d0) (Fin d0) ℝ}
    {MV : Matrix (Fin d1) (Fin d1) ℝ}
    {ae a0 a1 : FlatArray}
    (he : denotValB_partial PartialDirectOracle.oracle rho [] [] v = .ok (.array ae))
    (he0 : denotValB_partial PartialDirectOracle.oracle rho [] [] env0 = .ok (.array a0))
    (he1 : denotValB_partial PartialDirectOracle.oracle rho [] [] env1 = .ok (.array a1))
    (haelen : ae.length = d0 * d1)
    (ha0len : a0.length = d0 * d0)
    (ha1len : a1.length = d1 * d1)
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hd0 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) sa = .ok d0)
    (hd1 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) sb = .ok d1)
    (hM : (denotAsMatrix d0 d1 ae.get).transpose = M)
    (hMW : denotAsMatrix d0 d0 a0.get = MW)
    (hMV : denotAsMatrix d1 d1 a1.get = MV)
    (hG : MW.PosDef) (hH : MV.PosDef)
    (hgd : ∃ d, (ValExpr.inferSpaceCtx [] env0).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d)
    (hhd : ∃ d, (ValExpr.inferSpaceCtx [] env1).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d)
    (hf : ValueQueryDependencies.Finite (.expr [] v)) :
    exists out : FlatArray,
      denotValB_partial PartialDirectOracle.oracle rho [] [] (.vtrans (.gsvdUI v env0 env1)) =
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
  exact canonical_transpose_direct he he0 he1 hinfer hd0 hd1 hgd hhd hleaf hf

theorem eval_vtrans_canonicalU
    {rho : ValEnvSem}
    {v env0 env1 : ValExpr} {sa sb : ValSpace}
    {d0 d1 : Nat} {M : Matrix (Fin d1) (Fin d0) ℝ}
    {MW : Matrix (Fin d0) (Fin d0) ℝ}
    {MV : Matrix (Fin d1) (Fin d1) ℝ}
    {ae a0 a1 : FlatArray}
    (he : denotValB_partial PartialDirectOracle.oracle rho [] [] v = .ok (.array ae))
    (he0 : denotValB_partial PartialDirectOracle.oracle rho [] [] env0 = .ok (.array a0))
    (he1 : denotValB_partial PartialDirectOracle.oracle rho [] [] env1 = .ok (.array a1))
    (haelen : ae.length = d0 * d1)
    (ha0len : a0.length = d0 * d0)
    (ha1len : a1.length = d1 * d1)
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hd0 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) sa = .ok d0)
    (hd1 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) sb = .ok d1)
    (hM : (denotAsMatrix d0 d1 ae.get).transpose = M)
    (hMW : denotAsMatrix d0 d0 a0.get = MW)
    (hMV : denotAsMatrix d1 d1 a1.get = MV)
    (hG : MW.PosDef) (hH : MV.PosDef)
    (hgd : ∃ d, (ValExpr.inferSpaceCtx [] env0).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d)
    (hhd : ∃ d, (ValExpr.inferSpaceCtx [] env1).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d)
    (hf : ValueQueryDependencies.Finite (.expr [] v)) :
    exists out : FlatArray,
      denotValB_partial PartialDirectOracle.oracle rho [] [] (.vtrans (.gsvdU v env0 env1)) =
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
  exact canonical_transpose_direct he he0 he1 hinfer hd0 hd1 hgd hhd hleaf hf

theorem eval_vtrans_canonicalV
    {rho : ValEnvSem}
    {v env0 env1 : ValExpr} {sa sb : ValSpace}
    {d0 d1 : Nat} {M : Matrix (Fin d1) (Fin d0) ℝ}
    {MW : Matrix (Fin d0) (Fin d0) ℝ}
    {MV : Matrix (Fin d1) (Fin d1) ℝ}
    {ae a0 a1 : FlatArray}
    (he : denotValB_partial PartialDirectOracle.oracle rho [] [] v = .ok (.array ae))
    (he0 : denotValB_partial PartialDirectOracle.oracle rho [] [] env0 = .ok (.array a0))
    (he1 : denotValB_partial PartialDirectOracle.oracle rho [] [] env1 = .ok (.array a1))
    (haelen : ae.length = d0 * d1)
    (ha0len : a0.length = d0 * d0)
    (ha1len : a1.length = d1 * d1)
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hd0 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) sa = .ok d0)
    (hd1 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) sb = .ok d1)
    (hM : (denotAsMatrix d0 d1 ae.get).transpose = M)
    (hMW : denotAsMatrix d0 d0 a0.get = MW)
    (hMV : denotAsMatrix d1 d1 a1.get = MV)
    (hG : MW.PosDef) (hH : MV.PosDef)
    (hgd : ∃ d, (ValExpr.inferSpaceCtx [] env0).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d)
    (hhd : ∃ d, (ValExpr.inferSpaceCtx [] env1).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d)
    (hf : ValueQueryDependencies.Finite (.expr [] v)) :
    exists out : FlatArray,
      denotValB_partial PartialDirectOracle.oracle rho [] [] (.vtrans (.gsvdV v env0 env1)) =
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
  exact canonical_transpose_direct he he0 he1 hinfer hd0 hd1 hgd hhd hleaf hf

theorem eval_vtrans_canonicalVI
    {rho : ValEnvSem}
    {v env0 env1 : ValExpr} {sa sb : ValSpace}
    {d0 d1 : Nat} {M : Matrix (Fin d1) (Fin d0) ℝ}
    {MW : Matrix (Fin d0) (Fin d0) ℝ}
    {MV : Matrix (Fin d1) (Fin d1) ℝ}
    {ae a0 a1 : FlatArray}
    (he : denotValB_partial PartialDirectOracle.oracle rho [] [] v = .ok (.array ae))
    (he0 : denotValB_partial PartialDirectOracle.oracle rho [] [] env0 = .ok (.array a0))
    (he1 : denotValB_partial PartialDirectOracle.oracle rho [] [] env1 = .ok (.array a1))
    (haelen : ae.length = d0 * d1)
    (ha0len : a0.length = d0 * d0)
    (ha1len : a1.length = d1 * d1)
    (hinfer : ValExpr.inferSpaceCtx [] v = .tprod sa sb)
    (hd0 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) sa = .ok d0)
    (hd1 : ValSpace.dofPartial (PartialDirectOracle.oracle rho [] []) sb = .ok d1)
    (hM : (denotAsMatrix d0 d1 ae.get).transpose = M)
    (hMW : denotAsMatrix d0 d0 a0.get = MW)
    (hMV : denotAsMatrix d1 d1 a1.get = MV)
    (hG : MW.PosDef) (hH : MV.PosDef)
    (hgd : ∃ d, (ValExpr.inferSpaceCtx [] env0).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d)
    (hhd : ∃ d, (ValExpr.inferSpaceCtx [] env1).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d)
    (hf : ValueQueryDependencies.Finite (.expr [] v)) :
    exists out : FlatArray,
      denotValB_partial PartialDirectOracle.oracle rho [] [] (.vtrans (.gsvdVI v env0 env1)) =
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
  exact canonical_transpose_direct he he0 he1 hinfer hd0 hd1 hgd hhd hleaf hf

end GLang.PartialAdequacy
