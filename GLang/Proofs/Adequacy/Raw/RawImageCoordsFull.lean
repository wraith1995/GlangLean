import GLang.Proofs.Adequacy.Raw.RawImageCoords
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyEmbed
import GLang.Numerics.Spectral.BasisCanonicalImage

namespace GLang.RawImageCoords

theorem eval (orc : FFSOracleSem) (rho : ValEnvSem)
    (s0 s1 : ValSpace) (e : ValExpr) (m n : Nat)
    (M : Matrix (Fin n) (Fin m) ℝ) (a : FlatArray)
    (h0 : ValSpace.dof (orc rho [] []) s0 = m)
    (h1 : ValSpace.dof (orc rho [] []) s1 = n)
    (ha : denotValB_semS orc rho [] [] e = .ok (.array a))
    (hlen : a.length = m * n)
    (hM : (denotAsMatrix m n a.get).transpose = M)
    (hc : orc rho [] [] .cokernel (.tprod s0 s1)
      (ValExpr.reshapBase e (.tprod s0 s1)) = M.rank)
    (hi : orc rho [] [] .image (.tprod s0 s1)
      (ValExpr.reshapBase e (.tprod s0 s1)) = M.rank) :
    ∃ out : FlatArray,
      denotValB_semS orc rho [] [] (ValExpr.imageCoords (.tprod s0 s1) e) =
        .ok (.array out) ∧ out.length = M.rank * M.rank ∧
      ∀ i j : Fin M.rank, out.get (i.val * M.rank + j.val) =
        BasisSpectral.standardImageRows M i j := by
  have hw := denotValB_semS_reshap_spaces_ok orc rho [] [] e
    (.tprod s0 s1) (.tprod s0 s1) a ha
    (by simpa only [ValSpace.dof_tprod, h0, h1] using hlen) rfl
  obtain ⟨a0, he0, hl0, hm0⟩ := eval_idelta_matrix orc rho s0 m h0
  obtain ⟨a1, he1, hl1, hm1⟩ := eval_idelta_matrix orc rho s1 n h1
  obtain ⟨u, hu, hlu, hgu⟩ := RawTermEmbed.eval_vtrans_canonicalU
    hw he0 he1 hlen hl0 hl1 rfl h0 h1 hM hm0 hm1
    Matrix.PosDef.one Matrix.PosDef.one hc
  obtain ⟨v, hv, hlv, hgv⟩ := eval_canonicalV
    hw he0 he1 hlen hl0 hl1 rfl h0 h1 hM hm0 hm1
    Matrix.PosDef.one Matrix.PosDef.one hi
  apply eval_of_operands orc rho s0 s1 e m n M.rank M.transpose
    (BasisSpectral.canonicalBlocks M 1 1 Matrix.PosDef.one Matrix.PosDef.one).U.transpose
    (BasisSpectral.canonicalBlocks M 1 1 Matrix.PosDef.one Matrix.PosDef.one).V
    a u v h0 h1 hc hi hw hu hv hlen hlu hlv ?_ hgu hgv
  intro i j
  have h := congrArg (fun B : Matrix (Fin n) (Fin m) ℝ => B j i) hM
  simpa only [Matrix.transpose_apply, denotAsMatrix, Nat.mul_comm] using h

end GLang.RawImageCoords
