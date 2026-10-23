

import GLang.Numerics.SVD.GSVDConstruction
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

namespace GLang

open Matrix

/-! ## Singular value decomposition

`A : Matrix (Fin m) (Fin n) ℝ` admits a factorization
`A = U · diag(σ) · Vᵀ` with `U : m × r`, `V : n × r`,
`Uᵀ U = I_r`, `Vᵀ V = I_r`, `σ : Fin r → ℝ` strictly positive and
weakly decreasing. -/

structure SVDecomposition (m n : Nat) where
  /-- Number of nonzero singular values (rank). -/
  r : Nat
  r_le_m : r ≤ m
  r_le_n : r ≤ n
  /-- Left singular vectors, `U : m × r`. -/
  U : Matrix (Fin m) (Fin r) ℝ
  /-- Right singular vectors, `V : n × r`. -/
  V : Matrix (Fin n) (Fin r) ℝ
  /-- Singular values, strictly positive, weakly decreasing. -/
  σ : Fin r → ℝ
  σ_pos  : ∀ i, 0 < σ i
  σ_decr : ∀ i j : Fin r, i ≤ j → σ j ≤ σ i
  /-- `U` has orthonormal columns. -/
  U_orthonormal : Uᵀ * U = Matrix.diagonal (fun _ : Fin r => (1 : ℝ))
  /-- `V` has orthonormal columns. -/
  V_orthonormal : Vᵀ * V = Matrix.diagonal (fun _ : Fin r => (1 : ℝ))

namespace SVDecomposition

variable {m n : Nat} (svd : SVDecomposition m n)

/-- The diagonal singular-value matrix, `Sigma : r × r`. -/
noncomputable def sigmaMat : Matrix (Fin svd.r) (Fin svd.r) ℝ :=
  Matrix.diagonal svd.σ

/-- The diagonal matrix of *reciprocals* of singular values (used by the
    pseudo-inverse: `Σ⁺ = diag(1/σᵢ)`). -/
noncomputable def sigmaInvMat : Matrix (Fin svd.r) (Fin svd.r) ℝ :=
  Matrix.diagonal (fun i => (svd.σ i)⁻¹)

end SVDecomposition

/-- Generalized SVD of an `n × m` real matrix `A` (the coordinate matrix
    of `L : W → V`, rows indexed by the codomain `V`), with respect to the
    inner-product Gram matrices `M_W : m×m` on the domain (`W`) and
    `M_V : n×n` on the codomain (`V`). -/
structure GSVDecomposition (m n : Nat) where
  /-- Number of nonzero singular values (rank). -/
  r : Nat
  r_le_m : r ≤ m
  r_le_n : r ≤ n
  /-- `U : m × r` (left singular basis for the cokernel / image of `Aᵀ`). -/
  U  : Matrix (Fin m) (Fin r) ℝ
  /-- `UI : m × (m − r)` (left singular basis for the kernel direction). -/
  UI : Matrix (Fin m) (Fin (m - r)) ℝ
  /-- `V : n × r` (right singular basis for the image of `A`). -/
  V  : Matrix (Fin n) (Fin r) ℝ
  /-- `VI : n × (n − r)` (right singular basis for the coimage direction). -/
  VI : Matrix (Fin n) (Fin (n - r)) ℝ
  /-- Singular values, strictly positive, weakly decreasing. -/
  σ  : Fin r → ℝ
  σ_pos  : ∀ i, 0 < σ i
  σ_decr : ∀ i j : Fin r, i ≤ j → σ j ≤ σ i
  /-- The domain (`W`) inner-product Gram matrix the GSVD is taken
      with respect to. -/
  M_W : Matrix (Fin m) (Fin m) ℝ
  /-- The codomain (`V`) inner-product Gram matrix the GSVD is taken
      with respect to. -/
  M_V : Matrix (Fin n) (Fin n) ℝ
  /-- `U` columns orthonormal in `M_W`. -/
  U_orth_MW  : Uᵀ * M_W * U =
                 Matrix.diagonal (fun _ : Fin r => (1 : ℝ))
  /-- `V` columns orthonormal in `M_V`. -/
  V_orth_MV  : Vᵀ * M_V * V =
                 Matrix.diagonal (fun _ : Fin r => (1 : ℝ))

  UI_orth_MW : UIᵀ * M_W * UI = 1

  U_UI_orth_MW : Uᵀ * M_W * UI = 0

  VI_orth_MV : VIᵀ * M_V * VI = 1

  V_VI_orth_MV : Vᵀ * M_V * VI = 0

namespace GSVDecomposition

variable {m n : Nat} (gsvd : GSVDecomposition m n)

/-- The diagonal singular-value matrix, `S : r × r`. -/
noncomputable def sMat : Matrix (Fin gsvd.r) (Fin gsvd.r) ℝ :=
  Matrix.diagonal gsvd.σ

/-- The diagonal matrix of reciprocals of singular values (used by
    `gpinv`). -/
noncomputable def sInvMat : Matrix (Fin gsvd.r) (Fin gsvd.r) ℝ :=
  Matrix.diagonal (fun i => (gsvd.σ i)⁻¹)

end GSVDecomposition

theorem Matrix.exists_gsvd (m n : Nat)
    (A : Matrix (Fin n) (Fin m) ℝ)
    (M_W : Matrix (Fin m) (Fin m) ℝ)
    (M_V : Matrix (Fin n) (Fin n) ℝ)
    (_hW : M_W.PosDef) (_hV : M_V.PosDef) :
    ∃ gsvd : GSVDecomposition m n,
      gsvd.M_W = M_W ∧ gsvd.M_V = M_V ∧
      A = gsvd.V * Matrix.diagonal gsvd.σ * gsvd.Uᵀ * M_W := by
  obtain ⟨r, U, UI, V, VI, σ, hm, hn, hσ, hsort, hU, hV, hUI, hUUI, hVI, hVVI, hA⟩ :=
    GSVDConstruction.matrix_exists m n A M_W M_V _hW _hV
  refine ⟨{
    r := r, r_le_m := hm, r_le_n := hn,
    U := U, UI := UI, V := V, VI := VI, σ := σ,
    σ_pos := hσ, σ_decr := fun i j hij => hsort hij,
    M_W := M_W, M_V := M_V,
    U_orth_MW := ?_, V_orth_MV := ?_,
    UI_orth_MW := hUI, U_UI_orth_MW := hUUI,
    VI_orth_MV := hVI, V_VI_orth_MV := hVVI
  }, rfl, rfl, hA⟩
  · simpa only [Matrix.diagonal_one] using hU
  · simpa only [Matrix.diagonal_one] using hV

/-! ### Ordinary SVD as a specialization of GSVD

The two identity Gram matrices give the ordinary Euclidean factorization.
This removes a redundant existence axiom while retaining the public SVD API.
-/

/-- Every real matrix admits an SVD, by the identity-metric case of GSVD. -/
theorem Matrix.exists_svd (m n : Nat) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ svd : SVDecomposition m n,
      A = svd.U * Matrix.diagonal svd.σ * svd.V.transpose := by
  obtain ⟨g, hW, hV, hA⟩ := Matrix.exists_gsvd n m A 1 1
    Matrix.PosDef.one Matrix.PosDef.one
  refine ⟨{
    r := g.r
    r_le_m := g.r_le_n
    r_le_n := g.r_le_m
    U := g.V
    V := g.U
    σ := g.σ
    σ_pos := g.σ_pos
    σ_decr := g.σ_decr
    U_orthonormal := ?_
    V_orthonormal := ?_ }, ?_⟩
  · simpa only [hV, Matrix.mul_one] using g.V_orth_MV
  · simpa only [hW, Matrix.mul_one] using g.U_orth_MW
  · simpa only [Matrix.mul_one] using hA

/-- *Some* SVD of `A`. Existence is by `Matrix.exists_svd`. -/
noncomputable def matrixSVD {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    SVDecomposition m n :=
  (Matrix.exists_svd m n A).choose

/-- The SVD factorization, witnessed by `Matrix.exists_svd`. -/
theorem matrixSVD_factor {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    A = (matrixSVD A).U *
        Matrix.diagonal (matrixSVD A).σ *
        (matrixSVD A).Vᵀ :=
  (Matrix.exists_svd m n A).choose_spec

/-- Pseudo-inverse of `A` via SVD: `V · Σ⁻¹ · Uᵀ`. -/
noncomputable def matrixSVDPinv {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  let svd := matrixSVD A
  svd.V * svd.sigmaInvMat * svd.Uᵀ

/-- *Some* GSVD of `A` relative to `M_W`, `M_V`. When the Gram inputs are
    positive definite this is a witness of `Matrix.exists_gsvd`; off the
    PD domain (never reached from a list basis, whose Gram matrix is PD
    by `IsListBasis.gram_posDef`) it falls back to a GSVD relative to
    the identity metrics, so the definition is total. -/
noncomputable def matrixGSVD {m n : Nat}
    (A : Matrix (Fin n) (Fin m) ℝ)
    (M_W : Matrix (Fin m) (Fin m) ℝ)
    (M_V : Matrix (Fin n) (Fin n) ℝ) : GSVDecomposition m n :=
  haveI := Classical.propDecidable (M_W.PosDef ∧ M_V.PosDef)
  if h : M_W.PosDef ∧ M_V.PosDef then
    (Matrix.exists_gsvd m n A M_W M_V h.1 h.2).choose
  else
    (Matrix.exists_gsvd m n A 1 1 Matrix.PosDef.one Matrix.PosDef.one).choose

section GSVDSpec

variable {m n : Nat}
  (A : Matrix (Fin n) (Fin m) ℝ)
  (M_W : Matrix (Fin m) (Fin m) ℝ)
  (M_V : Matrix (Fin n) (Fin n) ℝ)

/-- The witnessing conjunction of `Matrix.exists_gsvd` for `matrixGSVD`. -/
theorem matrixGSVD_spec (hW : M_W.PosDef) (hV : M_V.PosDef) :
    (matrixGSVD A M_W M_V).M_W = M_W ∧ (matrixGSVD A M_W M_V).M_V = M_V ∧
    A = (matrixGSVD A M_W M_V).V *
        Matrix.diagonal (matrixGSVD A M_W M_V).σ *
        (matrixGSVD A M_W M_V).Uᵀ * M_W := by
  unfold matrixGSVD
  rw [dif_pos ⟨hW, hV⟩]
  exact (Matrix.exists_gsvd m n A M_W M_V hW hV).choose_spec

/-- The GSVD is taken relative to the input domain Gram matrix. -/
theorem matrixGSVD_M_W (hW : M_W.PosDef) (hV : M_V.PosDef) :
    (matrixGSVD A M_W M_V).M_W = M_W :=
  (matrixGSVD_spec A M_W M_V hW hV).1

/-- The GSVD is taken relative to the input codomain Gram matrix. -/
theorem matrixGSVD_M_V (hW : M_W.PosDef) (hV : M_V.PosDef) :
    (matrixGSVD A M_W M_V).M_V = M_V :=
  (matrixGSVD_spec A M_W M_V hW hV).2.1

theorem matrixGSVD_factor (hW : M_W.PosDef) (hV : M_V.PosDef) :
    A = (matrixGSVD A M_W M_V).V *
        Matrix.diagonal (matrixGSVD A M_W M_V).σ *
        (matrixGSVD A M_W M_V).Uᵀ * M_W :=
  (matrixGSVD_spec A M_W M_V hW hV).2.2

/-- `U` columns orthonormal in the *input* `M_W`. -/
theorem matrixGSVD_U_orth (hW : M_W.PosDef) (hV : M_V.PosDef) :
    (matrixGSVD A M_W M_V).Uᵀ * M_W * (matrixGSVD A M_W M_V).U = 1 := by
  have h := (matrixGSVD A M_W M_V).U_orth_MW
  rw [matrixGSVD_M_W A M_W M_V hW hV, Matrix.diagonal_one] at h
  exact h

/-- `UI` columns orthonormal in the *input* `M_W`. -/
theorem matrixGSVD_UI_orth (hW : M_W.PosDef) (hV : M_V.PosDef) :
    (matrixGSVD A M_W M_V).UIᵀ * M_W * (matrixGSVD A M_W M_V).UI = 1 := by
  have h := (matrixGSVD A M_W M_V).UI_orth_MW
  rw [matrixGSVD_M_W A M_W M_V hW hV] at h
  exact h

/-- `U ⊥ UI` in the *input* `M_W`. -/
theorem matrixGSVD_U_UI_orth (hW : M_W.PosDef) (hV : M_V.PosDef) :
    (matrixGSVD A M_W M_V).Uᵀ * M_W * (matrixGSVD A M_W M_V).UI = 0 := by
  have h := (matrixGSVD A M_W M_V).U_UI_orth_MW
  rw [matrixGSVD_M_W A M_W M_V hW hV] at h
  exact h

/-- `V` columns orthonormal in the *input* `M_V`. -/
theorem matrixGSVD_V_orth (hW : M_W.PosDef) (hV : M_V.PosDef) :
    (matrixGSVD A M_W M_V).Vᵀ * M_V * (matrixGSVD A M_W M_V).V = 1 := by
  have h := (matrixGSVD A M_W M_V).V_orth_MV
  rw [matrixGSVD_M_V A M_W M_V hW hV, Matrix.diagonal_one] at h
  exact h

/-- `VI` columns orthonormal in the *input* `M_V`. -/
theorem matrixGSVD_VI_orth (hW : M_W.PosDef) (hV : M_V.PosDef) :
    (matrixGSVD A M_W M_V).VIᵀ * M_V * (matrixGSVD A M_W M_V).VI = 1 := by
  have h := (matrixGSVD A M_W M_V).VI_orth_MV
  rw [matrixGSVD_M_V A M_W M_V hW hV] at h
  exact h

/-- `V ⊥ VI` in the *input* `M_V`. -/
theorem matrixGSVD_V_VI_orth (hW : M_W.PosDef) (hV : M_V.PosDef) :
    (matrixGSVD A M_W M_V).Vᵀ * M_V * (matrixGSVD A M_W M_V).VI = 0 := by
  have h := (matrixGSVD A M_W M_V).V_VI_orth_MV
  rw [matrixGSVD_M_V A M_W M_V hW hV] at h
  exact h

theorem matrixGSVD_mul_UI (hW : M_W.PosDef) (hV : M_V.PosDef) :
    A * (matrixGSVD A M_W M_V).UI = 0 := by
  have hfac := matrixGSVD_factor A M_W M_V hW hV
  have horth := matrixGSVD_U_UI_orth A M_W M_V hW hV
  set g := matrixGSVD A M_W M_V with hg
  calc A * g.UI = g.V * Matrix.diagonal g.σ * (g.Uᵀ * M_W * g.UI) := by
        rw [hfac]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [horth, Matrix.mul_zero]

theorem matrixGSVD_mul_U (hW : M_W.PosDef) (hV : M_V.PosDef) :
    A * (matrixGSVD A M_W M_V).U =
      (matrixGSVD A M_W M_V).V * Matrix.diagonal (matrixGSVD A M_W M_V).σ := by
  have hfac := matrixGSVD_factor A M_W M_V hW hV
  have horth := matrixGSVD_U_orth A M_W M_V hW hV
  set g := matrixGSVD A M_W M_V with hg
  calc A * g.U = g.V * Matrix.diagonal g.σ * (g.Uᵀ * M_W * g.U) := by
        rw [hfac]; simp only [Matrix.mul_assoc]
    _ = g.V * Matrix.diagonal g.σ := by rw [horth, Matrix.mul_one]

theorem matrixGSVD_Ut_MW_mulVec_eq_zero (hW : M_W.PosDef) (hV : M_V.PosDef)
    (c : Fin m → ℝ) (hc : A *ᵥ c = 0) :
    ((matrixGSVD A M_W M_V).Uᵀ * M_W) *ᵥ c = 0 := by
  have hfac := matrixGSVD_factor A M_W M_V hW hV
  have horth := matrixGSVD_V_orth A M_W M_V hW hV
  set g := matrixGSVD A M_W M_V with hg
  set y : Fin g.r → ℝ := (g.Uᵀ * M_W) *ᵥ c with hy
  -- `(Vᵀ M_V) (A c) = (Vᵀ M_V V) (S y) = S y`.
  have h1 : (g.Vᵀ * M_V) *ᵥ (A *ᵥ c) = Matrix.diagonal g.σ *ᵥ y := by
    rw [hfac, Matrix.mulVec_mulVec, hy, Matrix.mulVec_mulVec]
    congr 1
    calc g.Vᵀ * M_V * (g.V * Matrix.diagonal g.σ * g.Uᵀ * M_W)
        = (g.Vᵀ * M_V * g.V) * Matrix.diagonal g.σ * (g.Uᵀ * M_W) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal g.σ * (g.Uᵀ * M_W) := by rw [horth, Matrix.one_mul]
  rw [hc, Matrix.mulVec_zero] at h1
  funext i
  have hi : (Matrix.diagonal g.σ *ᵥ y) i = 0 := by rw [← h1]; rfl
  rw [Matrix.mulVec_diagonal] at hi
  have hσ : g.σ i ≠ 0 := ne_of_gt (g.σ_pos i)
  exact (mul_eq_zero.mp hi).resolve_left hσ

theorem matrixGSVD_VIt_MV_mul (hW : M_W.PosDef) (hV : M_V.PosDef) :
    (matrixGSVD A M_W M_V).VIᵀ * M_V * A = 0 := by
  have hfac := matrixGSVD_factor A M_W M_V hW hV
  have horth := matrixGSVD_V_VI_orth A M_W M_V hW hV
  set g := matrixGSVD A M_W M_V with hg
  have hsymm : M_Vᵀ = M_V := by
    have h := hV.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have horth' : g.VIᵀ * M_V * g.V = 0 := by
    have h := congrArg Matrix.transpose horth
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsymm,
      Matrix.transpose_zero, Matrix.mul_assoc] at h
    rw [Matrix.mul_assoc]
    exact h
  calc g.VIᵀ * M_V * A
      = (g.VIᵀ * M_V * g.V) * Matrix.diagonal g.σ * g.Uᵀ * M_W := by
        rw [hfac]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [horth']; simp

end GSVDSpec

noncomputable def matrixGSVDPinv {m n : Nat}
    (A : Matrix (Fin n) (Fin m) ℝ)
    (M_W : Matrix (Fin m) (Fin m) ℝ)
    (M_V : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  let g := matrixGSVD A M_W M_V
  g.U * g.sInvMat * g.Vᵀ * M_V

/-! ## Bridges between `Nat → ℝ` and `Matrix (Fin m) (Fin n) ℝ`

The value language stores everything as `Nat → ℝ` (flat C-order
arrays, with `ValIdx ≜ Nat`). For SVD computations we need to view a
value as a matrix; for returning a value we need to flatten back. -/

/-- View a flat `Nat → ℝ` as an `m × n` matrix using C-order layout:
    `M i j = f (n * i + j)`. The shape `(m, n)` is supplied explicitly
    (callers recover it from `ValExpr.inferSpace`). -/
def denotAsMatrix (m n : Nat) (f : Nat → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => f (n * i.val + j.val)

def matrixAsDenot {m n : Nat} (M : Matrix (Fin m) (Fin n) ℝ) :
    Nat → ℝ :=
  fun k =>
    if n = 0 then 0
    else
      let i := k / n
      let j := k % n
      if him : i < m then
        if hjn : j < n then
          M ⟨i, him⟩ ⟨j, hjn⟩
        else 0
      else 0

/-! ## Proved Moore–Penrose identities

These identities follow from the existing SVD factorization and orthonormal
columns. They require SVD existence, but no separate pseudoinverse axiom.
-/

namespace SVDecomposition
theorem sigma_mul_inverse {m n} (s : SVDecomposition m n) :
    Matrix.diagonal s.σ * s.sigmaInvMat = 1 := by
  rw [sigmaInvMat, Matrix.diagonal_mul_diagonal]
  simp [mul_inv_cancel₀ (ne_of_gt (s.σ_pos _))]
theorem inverse_mul_sigma {m n} (s : SVDecomposition m n) :
    s.sigmaInvMat * Matrix.diagonal s.σ = 1 := by
  rw [sigmaInvMat, Matrix.diagonal_mul_diagonal]
  simp [inv_mul_cancel₀ (ne_of_gt (s.σ_pos _))]
end SVDecomposition
theorem matrixSVD_mul_pinv {m n} (A : Matrix (Fin m) (Fin n) ℝ) :
    A * matrixSVDPinv A = (matrixSVD A).U * (matrixSVD A).Uᵀ := by
  let s := matrixSVD A
  calc
    A * matrixSVDPinv A = s.U * Matrix.diagonal s.σ * (s.Vᵀ * s.V) * s.sigmaInvMat * s.Uᵀ := by
      conv_lhs => lhs; rw [matrixSVD_factor A]
      simp only [matrixSVDPinv, s, Matrix.mul_assoc]
    _ = s.U * (Matrix.diagonal s.σ * s.sigmaInvMat) * s.Uᵀ := by
      rw [s.V_orthonormal]
      simp [Matrix.mul_assoc]
    _ = s.U * s.Uᵀ := by rw [s.sigma_mul_inverse, Matrix.mul_one]
theorem matrixSVD_pinv_mul {m n} (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixSVDPinv A * A = (matrixSVD A).V * (matrixSVD A).Vᵀ := by
  let s := matrixSVD A
  calc
    matrixSVDPinv A * A = s.V * s.sigmaInvMat * (s.Uᵀ * s.U) * Matrix.diagonal s.σ * s.Vᵀ := by
      conv_lhs => rhs; rw [matrixSVD_factor A]
      simp only [matrixSVDPinv, s, Matrix.mul_assoc]
    _ = s.V * (s.sigmaInvMat * Matrix.diagonal s.σ) * s.Vᵀ := by
      rw [s.U_orthonormal]
      simp [Matrix.mul_assoc]
    _ = s.V * s.Vᵀ := by rw [s.inverse_mul_sigma, Matrix.mul_one]

theorem matrixSVDPinv_mul_self {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    A * matrixSVDPinv A * A = A := by
  rw [matrixSVD_mul_pinv]
  conv_lhs => rhs; rw [matrixSVD_factor A]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (matrixSVD A).Uᵀ,
    ← Matrix.mul_assoc (matrixSVD A).Uᵀ, (matrixSVD A).U_orthonormal]
  simpa [Matrix.mul_assoc] using (matrixSVD_factor A).symm

theorem matrixSVDPinv_mul_self_mul_svdPinv {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixSVDPinv A * A * matrixSVDPinv A = matrixSVDPinv A := by
  rw [matrixSVD_pinv_mul]
  simp only [matrixSVDPinv]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (matrixSVD A).Vᵀ,
    ← Matrix.mul_assoc (matrixSVD A).Vᵀ, (matrixSVD A).V_orthonormal]
  simp [Matrix.mul_assoc]

end GLang
