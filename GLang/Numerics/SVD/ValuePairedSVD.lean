import GLang.Numerics.Spectral.BasisPairedDecomposition
import GLang.Numerics.Spectral.BasisSpectralMatrices
import GLang.Numerics.SVD.ValueSVD
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section
open scoped Matrix BigOperators
namespace GLang.ValuePairedSVD
open BasisSpectral

variable {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
  (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
  (hG : G.PosDef) (hH : H.PosDef)

abbrev domain := metricSpace G hG
abbrev codomain := metricSpace H hH

def domainPositive : List (Fin m → ℝ) :=
  BasisPairedSpectral.left (domain G hG) (codomain H hH) (Matrix.toLin' A)
    (fun μ => decide (μ ≠ 0)) (coordinateBasis m)
def domainZero : List (Fin m → ℝ) :=
  BasisPairedSpectral.left (domain G hG) (codomain H hH) (Matrix.toLin' A)
    (fun μ => decide (μ = 0)) (coordinateBasis m)
def codomainPositive : List (Fin n → ℝ) :=
  BasisPairedSpectral.right (domain G hG) (codomain H hH) (Matrix.toLin' A)
    (fun μ => decide (μ ≠ 0)) (coordinateBasis m) (coordinateBasis n)
def codomainZero : List (Fin n → ℝ) :=
  BasisPairedSpectral.right (domain G hG) (codomain H hH) (Matrix.toLin' A)
    (fun μ => decide (μ = 0)) (coordinateBasis m) (coordinateBasis n)

theorem domainPositive_length : (domainPositive A G H hG hH).length = A.rank :=
  BasisPairedSpectral.positive_length (domain G hG) (codomain H hH)
    (Matrix.toLin' A) (coordinateBasis m) (coordinateBasis_span m)

theorem domainZero_length : (domainZero A G H hG hH).length = m - A.rank := by
  simpa using BasisPairedSpectral.kernel_length
    (domain G hG) (codomain H hH) (Matrix.toLin' A) _ (coordinateBasis_span m)

theorem codomainPositive_length : (codomainPositive A G H hG hH).length = A.rank := by
  unfold codomainPositive
  rw [BasisPairedSpectral.right_nonzero_eq_map, List.length_map]
  exact domainPositive_length A G H hG hH

theorem codomainZero_length : (codomainZero A G H hG hH).length = n - A.rank := by
  simpa using BasisPairedSpectral.cokernel_length
    (domain G hG) (codomain H hH) (Matrix.toLin' A) _ _
    (coordinateBasis_span m) (coordinateBasis_span n)

/-- Reindex a literal ordered list by its proved length. -/
def getAs {α : Type} (xs : List α) {k : ℕ} (hk : xs.length = k) (i : Fin k) : α :=
  xs.get (Fin.cast hk.symm i)

def u (i : Fin A.rank) : Fin m → ℝ :=
  getAs (domainPositive A G H hG hH) (domainPositive_length A G H hG hH) i
def v (i : Fin A.rank) : Fin n → ℝ :=
  BasisPairedSpectral.normalizedImage (domain G hG) (codomain H hH) (Matrix.toLin' A)
    (u A G H hG hH i)
def ui (i : Fin (m - A.rank)) : Fin m → ℝ :=
  getAs (domainZero A G H hG hH) (domainZero_length A G H hG hH) i
def vi (i : Fin (n - A.rank)) : Fin n → ℝ :=
  getAs (codomainZero A G H hG hH) (codomainZero_length A G H hG hH) i
def sigma (i : Fin A.rank) : ℝ :=
  BasisPairedSpectral.singularValue (domain G hG) (codomain H hH) (Matrix.toLin' A)
    (u A G H hG hH i)

theorem sigma_pos (i : Fin A.rank) : 0 < sigma A G H hG hH i := by
  apply BasisPairedSpectral.singularValue_pos _ _ _ (coordinateBasis m)
  exact List.get_mem _ _

theorem sigma_antitone : Antitone (sigma A G H hG hH) := by
  intro i j hij
  exact BasisPairedSpectral.singularValues_antitone (domain G hG) (codomain H hH)
    (Matrix.toLin' A) (coordinateBasis m) hij

theorem pairing (i : Fin A.rank) :
    A *ᵥ u A G H hG hH i = sigma A G H hG hH i • v A G H hG hH i := by
  exact BasisPairedSpectral.positive_pairing (domain G hG) (codomain H hH) (Matrix.toLin' A) (coordinateBasis m) _ (List.get_mem _ _)

theorem u_inner (i j : Fin A.rank) :
    (domain G hG).innerProduct (u A G H hG hH i) (u A G H hG hH j) =
      if i = j then 1 else 0 := by
  have h := BasisPairedSpectral.left_inner (domain G hG) (codomain H hH)
    (Matrix.toLin' A) (fun μ => decide (μ ≠ 0)) (coordinateBasis m)
    (Fin.cast (domainPositive_length A G H hG hH).symm i)
    (Fin.cast (domainPositive_length A G H hG hH).symm j)
  simpa only [u, getAs, Fin.cast_inj] using h

theorem v_inner (i j : Fin A.rank) :
    (codomain H hH).innerProduct (v A G H hG hH i) (v A G H hG hH j) =
      if i = j then 1 else 0 := by
  have h := BasisPairedSpectral.right_inner (domain G hG) (codomain H hH)
    (Matrix.toLin' A) (fun μ => decide (μ ≠ 0)) (coordinateBasis m) (coordinateBasis n)
  rw [BasisPairedSpectral.right_nonzero_eq_map] at h
  let i' : Fin ((domainPositive A G H hG hH).map
      (BasisPairedSpectral.normalizedImage (domain G hG) (codomain H hH) (Matrix.toLin' A))).length :=
    ⟨i.val, by simp [domainPositive_length]⟩
  let j' : Fin ((domainPositive A G H hG hH).map
      (BasisPairedSpectral.normalizedImage (domain G hG) (codomain H hH) (Matrix.toLin' A))).length :=
    ⟨j.val, by simp [domainPositive_length]⟩
  simpa only [v, u, getAs, List.get_eq_getElem, List.getElem_map, i', j',
    Fin.ext_iff, Fin.val_cast, Fin.mk.injEq, domainPositive] using h i' j'

theorem ui_inner (i j : Fin (m - A.rank)) :
    (domain G hG).innerProduct (ui A G H hG hH i) (ui A G H hG hH j) =
      if i = j then 1 else 0 := by
  have h := BasisPairedSpectral.left_inner (domain G hG) (codomain H hH)
    (Matrix.toLin' A) (fun μ => decide (μ = 0)) (coordinateBasis m)
    (Fin.cast (domainZero_length A G H hG hH).symm i)
    (Fin.cast (domainZero_length A G H hG hH).symm j)
  simpa only [ui, getAs, Fin.cast_inj] using h

theorem vi_inner (i j : Fin (n - A.rank)) :
    (codomain H hH).innerProduct (vi A G H hG hH i) (vi A G H hG hH j) =
      if i = j then 1 else 0 := by
  have h := BasisPairedSpectral.right_inner (domain G hG) (codomain H hH)
    (Matrix.toLin' A) (fun μ => decide (μ = 0)) (coordinateBasis m) (coordinateBasis n)
    (Fin.cast (codomainZero_length A G H hG hH).symm i)
    (Fin.cast (codomainZero_length A G H hG hH).symm j)
  simpa only [vi, getAs, Fin.cast_inj] using h

theorem u_ui_inner (i : Fin A.rank) (j : Fin (m - A.rank)) :
    (domain G hG).innerProduct (u A G H hG hH i) (ui A G H hG hH j) = 0 := by
  exact BasisPairedSpectral.domain_positive_zero_inner
    (domain G hG) (codomain H hH) (Matrix.toLin' A) (coordinateBasis m)
    (coordinateBasis_span m) _ _ (List.get_mem _ _) (List.get_mem _ _)

theorem v_vi_inner (i : Fin A.rank) (j : Fin (n - A.rank)) :
    (codomain H hH).innerProduct (v A G H hG hH i) (vi A G H hG hH j) = 0 := by
  exact BasisPairedSpectral.image_zero_inner
    (domain G hG) (codomain H hH) (Matrix.toLin' A) (coordinateBasis m)
    (coordinateBasis n) (coordinateBasis_span m) (coordinateBasis_span n)
    _ _ (List.get_mem _ _)

/-- The SVD package uses only the canonical paired choices. -/
def decomposition : GSVDecomposition m n where
  r := A.rank
  r_le_m := Matrix.rank_le_card_width A |>.trans_eq (Fintype.card_fin m)
  r_le_n := Matrix.rank_le_card_height A |>.trans_eq (Fintype.card_fin n)
  U := fun a b => u A G H hG hH b a
  UI := fun a b => ui A G H hG hH b a
  V := fun a b => v A G H hG hH b a
  VI := fun a b => vi A G H hG hH b a
  σ := sigma A G H hG hH
  σ_pos := sigma_pos A G H hG hH
  σ_decr := sigma_antitone A G H hG hH
  M_W := G
  M_V := H
  U_orth_MW := by
    ext i j
    exact (GSVDConstruction.gram_columns G _ _ i j).trans
      ((u_inner A G H hG hH i j).trans (Matrix.diagonal_apply (fun _ => (1 : ℝ)) i j).symm)
  V_orth_MV := by
    ext i j
    exact (GSVDConstruction.gram_columns H _ _ i j).trans
      ((v_inner A G H hG hH i j).trans (Matrix.diagonal_apply (fun _ => (1 : ℝ)) i j).symm)
  UI_orth_MW := by
    ext i j
    exact (GSVDConstruction.gram_columns G _ _ i j).trans
      ((ui_inner A G H hG hH i j).trans (Matrix.one_apply (i := i) (j := j)).symm)
  VI_orth_MV := by
    ext i j
    exact (GSVDConstruction.gram_columns H _ _ i j).trans
      ((vi_inner A G H hG hH i j).trans (Matrix.one_apply (i := i) (j := j)).symm)
  U_UI_orth_MW := by
    ext i j
    exact (GSVDConstruction.gram_columns G _ _ i j).trans (u_ui_inner A G H hG hH i j)
  V_VI_orth_MV := by
    ext i j
    exact (GSVDConstruction.gram_columns H _ _ i j).trans (v_vi_inner A G H hG hH i j)

/-- Exact vector reconstruction from the packaged singular families. -/
theorem reconstruction (x : Fin m → ℝ) :
    A *ᵥ x = ∑ i : Fin A.rank,
      ((domain G hG).innerProduct (u A G H hG hH i) x * sigma A G H hG hH i) •
        v A G H hG hH i := by
  have hh := BasisPairedSpectral.reconstruction (domain G hG) (codomain H hH)
    (Matrix.toLin' A) (coordinateBasis m) (coordinateBasis_span m) x
  rw [Matrix.toLin'_apply] at hh
  rw [hh]
  exact (Equiv.sum_comp (finCongr (domainPositive_length A G H hG hH).symm) _).symm

/-- Full metric factorization, with a positive decreasing diagonal. -/
theorem factorization :
    let g := decomposition A G H hG hH
    A = g.V * g.sMat * g.U.transpose * G := by
  ext i j
  have hx := congrFun (reconstruction A G H hG hH (Pi.single j 1)) i
  simp [Matrix.mulVec_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
  rw [hx]
  change _ = ((Matrix.of (fun a b => v A G H hG hH b a)) *
    Matrix.diagonal (sigma A G H hG hH) *
    (Matrix.of (fun a b => u A G H hG hH b a)).transpose * G) i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  change (Matrix.toBilin' G (u A G H hG hH k) (Pi.single j 1) * sigma A G H hG hH k) *
    v A G H hG hH k i = _
  simp only [Matrix.toBilin'_apply', Matrix.mulVec_single, dotProduct]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  simp [Matrix.diagonal_apply]
  ring

theorem positive_pairing_matrix :
    let g := decomposition A G H hG hH
    A * g.U = g.V * g.sMat := by
  let g := decomposition A G H hG hH
  change A * g.U = g.V * g.sMat
  calc
    A * g.U = g.V * g.sMat * (g.U.transpose * G * g.U) := by
      rw [factorization A G H hG hH]
      simp only [g, Matrix.mul_assoc]
    _ = g.V * g.sMat := by
      have ho := g.U_orth_MW
      change g.U.transpose * G * g.U = Matrix.diagonal (fun _ => (1 : ℝ)) at ho
      rw [ho, Matrix.diagonal_one, Matrix.mul_one]

theorem image_coordinates :
    let g := decomposition A G H hG hH
    g.V.transpose * H * A * g.U = g.sMat := by
  let g := decomposition A G H hG hH
  change g.V.transpose * H * A * g.U = g.sMat
  calc
    g.V.transpose * H * A * g.U = g.V.transpose * H * (A * g.U) := by
      simp only [Matrix.mul_assoc]
    _ = (g.V.transpose * H * g.V) * g.sMat := by
      rw [positive_pairing_matrix A G H hG hH]
      simp only [g, Matrix.mul_assoc]
    _ = g.sMat := by
      have ho := g.V_orth_MV
      change g.V.transpose * H * g.V = Matrix.diagonal (fun _ => (1 : ℝ)) at ho
      rw [ho, Matrix.diagonal_one, Matrix.one_mul]

@[simp] theorem ofFn_getAs {α : Type} (xs : List α) {k : ℕ} (hk : xs.length = k) :
    List.ofFn (getAs xs hk) = xs := by
  subst k
  change List.ofFn xs.get = xs
  exact List.ofFn_get xs

theorem ofFn_u : List.ofFn (u A G H hG hH) = domainPositive A G H hG hH :=
  ofFn_getAs _ (domainPositive_length A G H hG hH)
theorem ofFn_ui : List.ofFn (ui A G H hG hH) = domainZero A G H hG hH :=
  ofFn_getAs _ (domainZero_length A G H hG hH)
theorem ofFn_vi : List.ofFn (vi A G H hG hH) = codomainZero A G H hG hH :=
  ofFn_getAs _ (codomainZero_length A G H hG hH)
theorem ofFn_v : List.ofFn (v A G H hG hH) = codomainPositive A G H hG hH := by
  unfold codomainPositive
  rw [BasisPairedSpectral.right_nonzero_eq_map]
  change List.ofFn (v A G H hG hH) = (domainPositive A G H hG hH).map _
  rw [← ofFn_u A G H hG hH, List.map_ofFn]
  rfl

end GLang.ValuePairedSVD
