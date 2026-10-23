import GLang.Numerics.Spectral.BasisCanonicalCoordinates
import GLang.Numerics.SVD.PairedSVDCoordinates
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Canonical selection matrices indexed by rank and nullity for operational use.
These are the four blocks of the paired canonical singular decomposition. -/
noncomputable section
namespace GLang.BasisSpectral

structure CanonicalBlocks (m n : ℕ) where
  r : ℕ
  UI : Matrix (Fin m) (Fin (m - r)) ℝ
  U : Matrix (Fin m) (Fin r) ℝ
  V : Matrix (Fin n) (Fin r) ℝ
  VI : Matrix (Fin n) (Fin (n - r)) ℝ

theorem kerMatrix_columns_rank {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    (leftVectors A G H hG hH (fun μ => decide (μ = 0))).length = m - A.rank := by
  rw [kerMatrix_columns]
  have hrank := (Matrix.toLin' A).finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ (Fin m → ℝ) = m := by simp
  change A.rank + Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A)) = _ at hrank
  omega

/-- Retype a column index using a proved dimension equality; column order is unchanged. -/
def castColumns {m k l : ℕ} (h : k = l) (M : Matrix (Fin m) (Fin k) ℝ) :
    Matrix (Fin m) (Fin l) ℝ := fun i j => M i (Fin.cast h.symm j)

theorem ofCoords_castColumns {V : HSpace} (xs : List V.carrier)
    {k l : ℕ} (h : k = l) (M : Matrix (Fin xs.length) (Fin k) ℝ) :
    List.ofCoords xs (castColumns h M) = List.ofCoords xs M := by
  subst l
  rfl

/-- Four rank-indexed canonical matrices for the exact input metric pair. -/
def canonicalBlocks {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) : CanonicalBlocks m n where
  r := A.rank
  UI := (ValuePairedSVD.decomposition A G H hG hH).UI
  U := (ValuePairedSVD.decomposition A G H hG hH).U
  V := (ValuePairedSVD.decomposition A G H hG hH).V
  VI := (ValuePairedSVD.decomposition A G H hG hH).VI

/-- Retyping the two column sets preserves the image reconstruction identity. -/
theorem castColumns_image_reconstruct {m n k l r : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin l) ℝ)
    (hk : k = r) (hl : l = r)
    (h : V * (V.transpose * H * A * U) = A * U) :
    castColumns hl V * ((castColumns hl V).transpose * H * A * castColumns hk U) =
      A * castColumns hk U := by
  subst k
  subst l
  exact h

/-- Exact coordinate conversion between the independently canonical blocks. -/
theorem canonicalBlocks_image_reconstruct {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    let g := canonicalBlocks A G H hG hH
    g.V * (g.V.transpose * H * A * g.U) = A * g.U := by
  change (ValuePairedSVD.decomposition A G H hG hH).V *
    ((ValuePairedSVD.decomposition A G H hG hH).V.transpose * H * A *
      (ValuePairedSVD.decomposition A G H hG hH).U) =
      A * (ValuePairedSVD.decomposition A G H hG hH).U
  rw [ValuePairedSVD.image_coordinates]
  exact (ValuePairedSVD.positive_pairing_matrix A G H hG hH).symm

end GLang.BasisSpectral
namespace GLang
/-- Canonical blocks in a pair of ordered input bases and their Gram metrics. -/
def IsListBasis.canonical {V W : HSpace} {xs : List V.carrier} {ys : List W.carrier}
    (hb : IsListBasis V xs) (hc : IsListBasis W ys) (f : V.carrier →ₗ[ℝ] W.carrier) :=
  BasisSpectral.canonicalBlocks (hb.coordMatrix hc f) (IsListBasis.gram V xs)
    (IsListBasis.gram W ys) hb.gram_posDef hc.gram_posDef
end GLang
