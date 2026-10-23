import GLang.Numerics.Spectral.BasisSpectralCoordinates
import GLang.Numerics.Spectral.BasisSpectralTransport
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # Canonical filtered singular vectors in metric coordinates

Matrix rows are ambient coordinates, columns are ordered canonical vectors.
Metrics are required positive definite; runtime handling of malformed metrics
is deliberately left to the later checked value-language interface.
-/
noncomputable section
open scoped Matrix BigOperators
namespace GLang.BasisSpectral

/-- A positive-definite real matrix defines the coordinate Hilbert space. -/
@[reducible] def metricSpace {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) : HSpace where
  carrier := Fin n → ℝ
  innerProduct := Matrix.toBilin' G
  innerIsIP := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      simp only [Matrix.toBilin'_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hg : G j i = G i j := by simpa using hG.isHermitian.apply i j
      rw [hg]
      ring
    · intro x
      simpa only [Matrix.toBilin'_apply', star_trivial] using hG.posSemidef.dotProduct_mulVec_nonneg x
    · intro x hx
      by_contra hn
      have hp := hG.dotProduct_mulVec_pos hn
      simp only [star_trivial] at hp
      exact (ne_of_gt hp) ((Matrix.toBilin'_apply' G x x).symm.trans hx)

/-- Increasing coordinate order, independent of either spectral decomposition. -/
def coordinateBasis (n : ℕ) : List (Fin n → ℝ) :=
  List.ofFn (fun i => Pi.single i (1 : ℝ))

theorem coordinateBasis_span (n : ℕ) :
    Submodule.span ℝ {v | v ∈ coordinateBasis n} = ⊤ := by
  have hs : {v | v ∈ coordinateBasis n} = Set.range (Pi.basisFun ℝ (Fin n)) := by
    ext v
    simp [coordinateBasis, Pi.basisFun_apply]
  rw [hs]
  exact (Pi.basisFun ℝ (Fin n)).span_eq

/-- Reify a list of coordinate vectors as a matrix, without choosing or
reordering any column. -/
def columns {n : ℕ} (xs : List (Fin n → ℝ)) : Matrix (Fin n) (Fin xs.length) ℝ :=
  fun i j => xs.get j i

/-- The exact coordinate reconstruction convention, including zero dimensions. -/
theorem columns_mulVec {n : ℕ} (xs : List (Fin n → ℝ)) (a : Fin xs.length → ℝ) :
    columns xs *ᵥ a = ∑ j, a j • xs.get j := by
  funext i
  simp [columns, Matrix.mulVec, dotProduct, mul_comm]

/-- The metric Gram matrix of the output columns is the identity. -/
theorem columns_metric_orthonormal {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (xs : List (Fin n → ℝ))
    (hon : ∀ i j : Fin xs.length,
      (metricSpace G hG).innerProduct (xs.get i) (xs.get j) = if i = j then 1 else 0) :
    (columns xs)ᵀ * G * columns xs = 1 := by
  ext j k
  have h := hon j k
  change Matrix.toBilin' G (xs.get j) (xs.get k) = _ at h
  rw [Matrix.toBilin'_apply] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, columns, Finset.sum_mul]
  rw [Finset.sum_comm, h]
  exact (Matrix.one_apply (i := j) (j := k)).symm

/-- Numeric domain-side canonical vectors, using actual spectral values. -/
def leftVectors {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) (pred : ℝ → Bool) : List (Fin m → ℝ) :=
  filteredLeft (metricSpace G hG) (metricSpace H hH) (Matrix.toLin' A) pred (coordinateBasis m)

def rightVectors {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) (pred : ℝ → Bool) : List (Fin n → ℝ) :=
  filteredRight (metricSpace G hG) (metricSpace H hH) (Matrix.toLin' A) pred (coordinateBasis n)

def leftMatrix {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) (pred : ℝ → Bool) :=
  columns (leftVectors A G H hG hH pred)

def rightMatrix {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) (pred : ℝ → Bool) :=
  columns (rightVectors A G H hG hH pred)

theorem leftMatrix_orthonormal {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) (pred : ℝ → Bool) :
    (leftMatrix A G H hG hH pred)ᵀ * G * leftMatrix A G H hG hH pred = 1 :=
  columns_metric_orthonormal G hG _ (filteredLeft_inner _ _ _ _ _)

theorem rightMatrix_orthonormal {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) (pred : ℝ → Bool) :
    (rightMatrix A G H hG hH pred)ᵀ * H * rightMatrix A G H hG hH pred = 1 :=
  columns_metric_orthonormal H hH _ (filteredRight_inner _ _ _ _ _)

/-- The four matrix selections consumed by projected-basis embeddings. -/
def kerMatrix {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) := leftMatrix A G H hG hH (fun μ => decide (μ = 0))
def cokerMatrix {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) := leftMatrix A G H hG hH (fun μ => decide (μ ≠ 0))
def imgMatrix {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) := rightMatrix A G H hG hH (fun μ => decide (μ ≠ 0))
def coimgMatrix {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) := rightMatrix A G H hG hH (fun μ => decide (μ = 0))

/-- Full signed/rotated conversion from the image of the canonical domain
basis to the independently canonical image basis. -/
def imageConversion {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :=
  (imgMatrix A G H hG hH)ᵀ * H * A * cokerMatrix A G H hG hH

/-- Matrix cross-Gram entries are the coordinate metric inner products. -/
theorem crossGram_apply {n k l : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin k) ℝ) (B : Matrix (Fin n) (Fin l) ℝ) (i : Fin k) (j : Fin l) :
    (Rᵀ * H * B) i j = Matrix.toBilin' H (fun a => R a i) (fun a => B a j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.toBilin'_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The image conversion is exactly the source-to-target inner-product
matrix, not a diagonal positive singular-value approximation. -/
theorem imageConversion_apply {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef)
    (i : Fin (rightVectors A G H hG hH (fun μ => decide (μ ≠ 0))).length)
    (j : Fin (leftVectors A G H hG hH (fun μ => decide (μ ≠ 0))).length) :
    imageConversion A G H hG hH i j = (metricSpace H hH).innerProduct
      ((rightVectors A G H hG hH (fun μ => decide (μ ≠ 0))).get i)
      (A *ᵥ ((leftVectors A G H hG hH (fun μ => decide (μ ≠ 0))).get j)) := by
  unfold imageConversion
  rw [Matrix.mul_assoc]
  rw [crossGram_apply]
  rfl

set_option maxHeartbeats 800000 in
/-- The conversion reconstructs every image column exactly. -/
theorem imageConversion_reconstruct {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    imgMatrix A G H hG hH * imageConversion A G H hG hH = A * cokerMatrix A G H hG hH := by
  let W := metricSpace H hH
  letI := W.innerIsIP.toIPSCore
  letI : NormedAddCommGroup (Fin n → ℝ) := W.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : SeminormedAddCommGroup (Fin n → ℝ) := W.innerIsIP.toIPSCore.toNormedAddCommGroup.toSeminormedAddCommGroup
  letI : InnerProductSpace ℝ (Fin n → ℝ) := InnerProductSpace.ofCore inferInstance
  let rs := rightVectors A G H hG hH (fun μ => decide (μ ≠ 0))
  let ls := leftVectors A G H hG hH (fun μ => decide (μ ≠ 0))
  have hon : Orthonormal ℝ rs.get :=
    (W.orthonormal_iff_innerProduct rs.get).mpr (filteredRight_inner _ _ _ _ _)
  have hspan : Submodule.span ℝ (Set.range rs.get) = LinearMap.range (Matrix.toLin' A) := by
    exact (HSpace.span_setOf_mem_eq_span_range_get (V := W) rs).symm.trans
      (filteredRight_nonzero_span _ _ _ _ (coordinateBasis_span n))
  ext a j
  have hv : A *ᵥ ls.get j ∈ Submodule.span ℝ (Set.range rs.get) := by
    rw [hspan]
    exact ⟨ls.get j, rfl⟩
  have hx := orthonormal_reconstruct rs.get hon hv
  have hx' := congrArg (fun x : W.carrier => x a) hx
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx'
  change (∑ i, rs.get i a * imageConversion A G H hG hH i j) = _
  simp only [imageConversion_apply]
  change (∑ i, W.innerProduct (rs.get i) (A *ᵥ ls.get j) * rs.get i a) = _ at hx'
  calc
    _ = ∑ i, W.innerProduct (rs.get i) (A *ᵥ ls.get j) * rs.get i a :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    _ = _ := hx'

/-- The exact runtime matrix-vector equation needed by the operational
image-to-canonical-image conversion. No reshaping or padding is implicit. -/
theorem imageConversion_mulVec {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef)
    (a : Fin (leftVectors A G H hG hH (fun μ => decide (μ ≠ 0))).length → ℝ) :
    imgMatrix A G H hG hH *ᵥ (imageConversion A G H hG hH *ᵥ a) =
      A *ᵥ (cokerMatrix A G H hG hH *ᵥ a) := by
  rw [Matrix.mulVec_mulVec, imageConversion_reconstruct, Matrix.mulVec_mulVec]

/-- Kernel-selection column count: exact nullity, including degenerate sizes. -/
theorem kerMatrix_columns {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    (leftVectors A G H hG hH (fun μ => decide (μ = 0))).length =
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A)) :=
  filteredLeft_zero_length _ _ _ _ (coordinateBasis_span m)

/-- Image-selection column count: exact rank. -/
theorem imgMatrix_columns {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    (rightVectors A G H hG hH (fun μ => decide (μ ≠ 0))).length =
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) :=
  filteredRight_nonzero_length _ _ _ _ (coordinateBasis_span n)

/-- Cokernel-selection column count: exact rank. -/
theorem cokerMatrix_columns {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    (leftVectors A G H hG hH (fun μ => decide (μ ≠ 0))).length =
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) :=
  filteredLeft_nonzero_length_eq_range _ _ _ _ (coordinateBasis_span m)

/-- Coimage-selection column count: exact target nullity. -/
theorem coimgMatrix_columns {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    (rightVectors A G H hG hH (fun μ => decide (μ = 0))).length =
      n - Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) := by
  simpa using filteredRight_zero_length_eq_sub_range
    (metricSpace G hG) (metricSpace H hH) (Matrix.toLin' A)
    (coordinateBasis n) (coordinateBasis_span n)

end GLang.BasisSpectral
