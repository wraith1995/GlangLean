import GLang.Numerics.SVD.GSVDPairedSpectral
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Spectral construction of finite paired singular blocks, including their
orthogonal complements. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace Matrix
namespace GLang.GSVDConstruction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Complete a finite orthonormal family by its orthogonal complement. -/
theorem complement {r : ℕ} (u : Fin r → E) (hu : Orthonormal ℝ u) :
    ∃ w : Fin (Module.finrank ℝ E - r) → E,
      Orthonormal ℝ w ∧ ∀ i j, ⟪u i, w j⟫ = 0 := by
  let K := Submodule.span ℝ (Set.range u)
  have hk : Module.finrank ℝ K = r := by
    simpa [K] using finrank_span_eq_card hu.linearIndependent
  have hd : Module.finrank ℝ Kᗮ = Module.finrank ℝ E - r := by
    have h := K.finrank_add_finrank_orthogonal
    omega
  let b := (stdOrthonormalBasis ℝ Kᗮ).reindex (finCongr hd)
  refine ⟨fun i => (b i : E), ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    exact orthonormal_iff_ite.mp b.orthonormal i j
  · intro i j
    exact K.inner_right_of_mem_orthogonal (Submodule.subset_span ⟨i, rfl⟩) (b j).property

open GSVDPairedSpectral
/-- Ordered positive singular families and their exact reconstruction. -/
theorem paired (A : E →ₗ[ℝ] F) :
    ∃ (r : ℕ) (u : Fin r → E) (v : Fin r → F) (σ : Fin r → ℝ),
      r ≤ Module.finrank ℝ E ∧ r ≤ Module.finrank ℝ F ∧
      Orthonormal ℝ u ∧ Orthonormal ℝ v ∧
      (∀ i, 0 < σ i) ∧ Antitone σ ∧
      ∀ x, A x = ∑ i, (⟪u i, x⟫ * σ i) • v i := by
  classical
  let s := Finset.univ.filter (fun i => 0 < gramValues A i)
  let e := s.orderIsoOfFin rfl
  let p : Fin s.card → PositiveIndex A := fun i =>
    ⟨(e i).val, (Finset.mem_filter.mp (e i).property).2⟩
  have hp : Function.Injective p := by
    intro i j h
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun k : PositiveIndex A => k.val) h
  let u := fun i => gramBasis A (p i).val
  let v := fun i => pairedImage A (u i) (singularValues A (p i).val)
  let σ := fun i => singularValues A (p i).val
  have hu : Orthonormal ℝ u :=
    (gramBasis A).orthonormal.comp _ (Subtype.val_injective.comp hp)
  have hv : Orthonormal ℝ v := (positive_paired_orthonormal A).comp p hp
  refine ⟨s.card, u, v, σ, ?_, ?_, hu, hv, ?_, ?_, ?_⟩
  · simpa using hu.linearIndependent.fintype_card_le_finrank
  · simpa using hv.linearIndependent.fintype_card_le_finrank
  · intro i
    exact Real.sqrt_pos.mpr (p i).property
  · intro i j hij
    exact singularValues_antitone A (e.monotone hij)
  · intro x
    rw [spectral_reconstruction]
    have hsum : (∑ i, (⟪gramBasis A i, x⟫ * singularValues A i) •
        pairedImage A (gramBasis A i) (singularValues A i)) =
        ∑ i ∈ s, (⟪gramBasis A i, x⟫ * singularValues A i) •
          pairedImage A (gramBasis A i) (singularValues A i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      have hz : gramValues A i = 0 := by
        have : ¬ 0 < gramValues A i := by simpa [s] using hi
        exact le_antisymm (le_of_not_gt this) (gramValues_nonneg A i)
      simp [singularValues, hz]
    rw [hsum]
    rw [← Finset.sum_coe_sort]
    exact (e.toEquiv.sum_comp _).symm

/-- The supplied positive-definite Gram matrix, used as an inner product. -/
@[reducible] def metricCore {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) : InnerProductSpace.Core ℝ (Fin n → ℝ) where
  inner x y := Matrix.toBilin' G x y
  conj_inner_symm x y := by
    simp only [conj_trivial, Matrix.toBilin'_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hg : G j i = G i j := by simpa using hG.isHermitian.apply i j
    rw [hg]
    ring
  re_inner_nonneg x := by
    simpa only [Matrix.toBilin'_apply', star_trivial, RCLike.re_to_real] using
      hG.posSemidef.dotProduct_mulVec_nonneg x
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra hn
    have hp := hG.dotProduct_mulVec_pos hn
    simp only [star_trivial] at hp
    exact (ne_of_gt hp) ((Matrix.toBilin'_apply' G x x).symm.trans hx)

/-- Matrix form of a Gram pairing of two column families. -/
theorem gram_columns {n r k : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin r → Fin n → ℝ) (v : Fin k → Fin n → ℝ) (i : Fin r) (j : Fin k) :
    ((Matrix.of (fun a b => u b a))ᵀ * G *
      Matrix.of (fun a b => v b a)) i j =
      Matrix.toBilin' G (u i) (v j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    Matrix.toBilin'_apply, Matrix.of_apply]
  rw [Finset.sum_comm]

/-- GSVD data with precisely the dimensions, ordering, metric identities and
factorization required by the existing numerical interface. -/
theorem matrix_exists (m n : ℕ) (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    ∃ (r : ℕ) (U : Matrix (Fin m) (Fin r) ℝ)
      (UI : Matrix (Fin m) (Fin (m-r)) ℝ)
      (V : Matrix (Fin n) (Fin r) ℝ)
      (VI : Matrix (Fin n) (Fin (n-r)) ℝ) (σ : Fin r → ℝ),
      r ≤ m ∧ r ≤ n ∧ (∀ i, 0 < σ i) ∧ Antitone σ ∧
      Uᵀ * G * U = 1 ∧ Vᵀ * H * V = 1 ∧
      UIᵀ * G * UI = 1 ∧ Uᵀ * G * UI = 0 ∧
      VIᵀ * H * VI = 1 ∧ Vᵀ * H * VI = 0 ∧
      A = V * Matrix.diagonal σ * Uᵀ * G := by
  letI := metricCore G hG
  letI : NormedAddCommGroup (Fin m → ℝ) := (metricCore G hG).toNormedAddCommGroup
  letI : SeminormedAddCommGroup (Fin m → ℝ) := (metricCore G hG).toNormedAddCommGroup.toSeminormedAddCommGroup
  letI : InnerProductSpace ℝ (Fin m → ℝ) := InnerProductSpace.ofCore inferInstance
  letI := metricCore H hH
  letI : NormedAddCommGroup (Fin n → ℝ) := (metricCore H hH).toNormedAddCommGroup
  letI : SeminormedAddCommGroup (Fin n → ℝ) := (metricCore H hH).toNormedAddCommGroup.toSeminormedAddCommGroup
  letI : InnerProductSpace ℝ (Fin n → ℝ) := InnerProductSpace.ofCore inferInstance
  obtain ⟨r, u, v, σ, hm, hn, hu, hv, hσ, hsort, hrec⟩ := paired (Matrix.toLin' A)
  have dm : Module.finrank ℝ (Fin m → ℝ) = m := by simp
  have dn : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  rw [dm] at hm
  rw [dn] at hn
  have hcU := complement u hu
  have hcV := complement v hv
  rw [dm] at hcU
  rw [dn] at hcV
  obtain ⟨ui, hui, hui0⟩ := hcU
  obtain ⟨vi, hvi, hvi0⟩ := hcV
  let U : Matrix (Fin m) (Fin r) ℝ := fun a b => u b a
  let V : Matrix (Fin n) (Fin r) ℝ := fun a b => v b a
  let UI : Matrix (Fin m) (Fin (m-r)) ℝ := fun a b => ui b a
  let VI : Matrix (Fin n) (Fin (n-r)) ℝ := fun a b => vi b a
  refine ⟨r, U, UI, V, VI, σ, hm, hn, hσ, hsort, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    exact (gram_columns G u u i j).trans
      ((orthonormal_iff_ite.mp hu i j).trans (Matrix.one_apply (i := i) (j := j)).symm)
  · ext i j
    exact (gram_columns H v v i j).trans
      ((orthonormal_iff_ite.mp hv i j).trans (Matrix.one_apply (i := i) (j := j)).symm)
  · ext i j
    exact (gram_columns G ui ui i j).trans
      ((orthonormal_iff_ite.mp hui i j).trans (Matrix.one_apply (i := i) (j := j)).symm)
  · ext i j
    exact (gram_columns G u ui i j).trans (hui0 i j)
  · ext i j
    exact (gram_columns H vi vi i j).trans
      ((orthonormal_iff_ite.mp hvi i j).trans (Matrix.one_apply (i := i) (j := j)).symm)
  · ext i j
    exact (gram_columns H v vi i j).trans (hvi0 i j)
  · apply Matrix.ext
    intro i j
    have hx := congrFun (hrec (Pi.single j 1)) i
    simp [Matrix.toLin'_apply, Matrix.mulVec_single,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
    change A i j = _ at hx
    rw [hx]
    simp only [U, V, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    change (Matrix.toBilin' G (u k) (Pi.single j 1) * σ k) * v k i = _
    simp only [Matrix.toBilin'_apply', Matrix.mulVec_single, dotProduct]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    simp [Matrix.diagonal_apply]
    ring
end GLang.GSVDConstruction

