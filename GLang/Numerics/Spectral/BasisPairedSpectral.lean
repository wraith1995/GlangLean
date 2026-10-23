import GLang.Numerics.Spectral.BasisSpectralFilteredTransport
import GLang.Numerics.SVD.GSVDPairedSpectral

noncomputable section
namespace GLang.BasisPairedSpectral
open BasisSpectral
open scoped RealInnerProductSpace

variable (V W : HSpace)
local instance : InnerProductSpace.Core ℝ V.carrier := V.innerIsIP.toIPSCore
local instance : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ W.carrier := W.innerIsIP.toIPSCore
local instance : NormedAddCommGroup W.carrier := W.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ W.carrier := InnerProductSpace.ofCore inferInstance

/-- Canonical domain block at a squared singular value. -/
def leftBlock (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ)
    (xs : List V.carrier) : List V.carrier :=
  bucket V (LinearMap.adjoint A ∘ₗ A) μ xs

/-- Paired codomain block; at zero use the codomain projected basis. -/
def rightBlock (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ)
    (xs : List V.carrier) (ys : List W.carrier) : List W.carrier :=
  if μ = 0 then bucket W (A ∘ₗ LinearMap.adjoint A) 0 ys
  else (leftBlock V W A μ xs).map (fun u => (Real.sqrt μ)⁻¹ • A u)

def values (A : V.carrier →ₗ[ℝ] W.carrier) : List ℝ :=
  ((eigenvaluesIncreasing A ++ eigenvaluesIncreasing (LinearMap.adjoint A)).toFinset).sort (· ≥ ·)

def left (A : V.carrier →ₗ[ℝ] W.carrier) (pred : ℝ → Bool)
    (xs : List V.carrier) : List V.carrier :=
  ((values V W A).filter pred).flatMap (fun μ => leftBlock V W A μ xs)

def right (A : V.carrier →ₗ[ℝ] W.carrier) (pred : ℝ → Bool)
    (xs : List V.carrier) (ys : List W.carrier) : List W.carrier :=
  ((values V W A).filter pred).flatMap (fun μ => rightBlock V W A μ xs ys)

@[simp] theorem rightBlock_zero (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier) :
    rightBlock V W A 0 xs ys = bucket W (A ∘ₗ LinearMap.adjoint A) 0 ys := by
  simp [rightBlock]

theorem rightBlock_pos (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ) (hμ : 0 < μ)
    (xs : List V.carrier) (ys : List W.carrier) :
    rightBlock V W A μ xs ys =
      (leftBlock V W A μ xs).map (fun u => (Real.sqrt μ)⁻¹ • A u) := by
  simp [rightBlock, ne_of_gt hμ]

theorem rightBlock_length (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ) (hμ : 0 < μ)
    (xs : List V.carrier) (ys : List W.carrier) :
    (rightBlock V W A μ xs ys).length = (leftBlock V W A μ xs).length := by
  simp [rightBlock_pos V W A μ hμ]

theorem leftBlock_eigen (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ)
    (xs : List V.carrier) (u : V.carrier) (hu : u ∈ leftBlock V W A μ xs) :
    (LinearMap.adjoint A) (A u) = μ • u := by
  exact (Module.End.mem_eigenspace_iff.mp (bucket_mem V _ μ xs u hu))

/-- Literal pairing, not merely equality of the spans. -/
theorem apply_eq_sqrt_smul (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ)
    (hμ : 0 < μ) (u : V.carrier) :
    A u = Real.sqrt μ • ((Real.sqrt μ)⁻¹ • A u) := by
  simp [smul_smul, ne_of_gt (Real.sqrt_pos.mpr hμ)]

/-- Each transported positive vector lies in the corresponding codomain eigenspace. -/
theorem paired_eigen (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ)
    (xs : List V.carrier) (u : V.carrier) (hu : u ∈ leftBlock V W A μ xs) :
    (A ∘ₗ LinearMap.adjoint A) ((Real.sqrt μ)⁻¹ • A u) =
      μ • ((Real.sqrt μ)⁻¹ • A u) := by
  simp only [LinearMap.comp_apply, map_smul, leftBlock_eigen V W A μ xs u hu]
  simp [smul_smul, mul_comm]

/-- Paired positive blocks are orthonormal, including repeated eigenvalues. -/
theorem paired_orthonormal (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ)
    (hμ : 0 < μ) (xs : List V.carrier) :
    Orthonormal ℝ (fun i : Fin (leftBlock V W A μ xs).length =>
      (Real.sqrt μ)⁻¹ • A ((leftBlock V W A μ xs).get i)) := by
  apply GSVDPairedSpectral.pairedImage_orthonormal A
    (fun i => (leftBlock V W A μ xs).get i) (fun _ => Real.sqrt μ)
  · rw [orthonormal_iff_ite]
    exact bucket_inner V _ μ xs
  · intro _; exact Real.sqrt_pos.mpr hμ
  · intro i
    rw [Real.sq_sqrt (le_of_lt hμ)]
    exact leftBlock_eigen V W A μ xs _ (List.get_mem _ i)

/-- Normalized transport is onto the codomain eigenspace at each positive value. -/
theorem map_eigenspace (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ) (hμ : 0 < μ) :
    Submodule.map ((Real.sqrt μ)⁻¹ • A)
      (Module.End.eigenspace (LinearMap.adjoint A ∘ₗ A) μ) =
      Module.End.eigenspace (A ∘ₗ LinearMap.adjoint A) μ := by
  have hs : Real.sqrt μ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hμ)
  apply le_antisymm
  · rintro z ⟨u, hu, rfl⟩
    change u ∈ Module.End.eigenspace (LinearMap.adjoint A ∘ₗ A) μ at hu
    rw [Module.End.mem_eigenspace_iff] at hu ⊢
    change (LinearMap.adjoint A) (A u) = μ • u at hu
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, hu]
    simp [smul_smul, mul_comm]
  · intro z hz
    rw [Module.End.mem_eigenspace_iff] at hz
    change A ((LinearMap.adjoint A) z) = μ • z at hz
    refine ⟨(Real.sqrt μ)⁻¹ • (LinearMap.adjoint A) z, ?_, ?_⟩
    · change (Real.sqrt μ)⁻¹ • (LinearMap.adjoint A) z ∈
        Module.End.eigenspace (LinearMap.adjoint A ∘ₗ A) μ
      rw [Module.End.mem_eigenspace_iff]
      simp only [LinearMap.comp_apply, map_smul, hz]
      simp [smul_smul, mul_comm]
    · simp only [LinearMap.smul_apply, map_smul, hz, smul_smul]
      have hscalar : (Real.sqrt μ)⁻¹ * ((Real.sqrt μ)⁻¹ * μ) = 1 := by
        field_simp
        nlinarith [Real.sq_sqrt (le_of_lt hμ)]
      rw [hscalar, one_smul]

theorem rightBlock_span_pos (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ) (hμ : 0 < μ)
    (xs : List V.carrier) (ys : List W.carrier)
    (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤) :
    Submodule.span ℝ {z | z ∈ rightBlock V W A μ xs ys} =
      Module.End.eigenspace (A ∘ₗ LinearMap.adjoint A) μ := by
  rw [rightBlock_pos V W A μ hμ]
  have hm : {z | z ∈ (leftBlock V W A μ xs).map (fun u => (Real.sqrt μ)⁻¹ • A u)} =
      ((Real.sqrt μ)⁻¹ • A) '' {u | u ∈ leftBlock V W A μ xs} := by
    ext z
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image, LinearMap.smul_apply]
  rw [hm, ← Submodule.map_span, leftBlock, bucket_span V _ μ xs hxs]
  exact map_eigenspace V W A μ hμ

/-- Indexed orthonormality in the form consumed by the source basis proofs. -/
theorem rightBlock_inner (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ) (hμ : 0 ≤ μ)
    (xs : List V.carrier) (ys : List W.carrier) :
    ∀ i j : Fin (rightBlock V W A μ xs ys).length,
      W.innerProduct ((rightBlock V W A μ xs ys).get i)
        ((rightBlock V W A μ xs ys).get j) = if i = j then 1 else 0 := by
  by_cases hz : μ = 0
  · subst μ
    rw [rightBlock_zero]
    exact bucket_inner W _ 0 ys
  · have hp : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hz)
    rw [rightBlock_pos V W A μ hp]
    intro i j
    let i' : Fin (leftBlock V W A μ xs).length := ⟨i.val, by simpa using i.isLt⟩
    let j' : Fin (leftBlock V W A μ xs).length := ⟨j.val, by simpa using j.isLt⟩
    have h := orthonormal_iff_ite.mp (paired_orthonormal V W A μ hp xs) i' j'
    simpa only [List.get_eq_getElem, List.getElem_map, i', j', Fin.mk.injEq,
      Fin.ext_iff] using h

/-- Right block vectors satisfy the literal codomain eigenvector equation. -/
theorem rightBlock_mem (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ)
    (xs : List V.carrier) (ys : List W.carrier)
    (z : W.carrier) (hz : z ∈ rightBlock V W A μ xs ys) :
    z ∈ Module.End.eigenspace (A ∘ₗ LinearMap.adjoint A) μ := by
  by_cases h0 : μ = 0
  · subst μ
    exact bucket_mem W _ 0 ys z (by simpa using hz)
  · simp only [rightBlock, if_neg h0, List.mem_map] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [Module.End.mem_eigenspace_iff]
    exact paired_eigen V W A μ xs u hu

/-- The zero blocks remain the independently projected kernel bases. -/
theorem rightBlock_span_zero (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier)
    (hys : Submodule.span ℝ {z | z ∈ ys} = ⊤) :
    Submodule.span ℝ {z | z ∈ rightBlock V W A 0 xs ys} =
      Module.End.eigenspace (A ∘ₗ LinearMap.adjoint A) 0 := by
  rw [rightBlock_zero]
  exact bucket_span W _ 0 ys hys

@[simp] theorem mem_values (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ) :
    μ ∈ values V W A ↔
      Module.End.HasEigenvalue (LinearMap.adjoint A ∘ₗ A) μ ∨
      Module.End.HasEigenvalue (A ∘ₗ LinearMap.adjoint A) μ := by
  simp [values, eigenvaluesIncreasing_mem_iff]

theorem values_nodup (A : V.carrier →ₗ[ℝ] W.carrier) :
    (values V W A).Nodup := Finset.sort_nodup _ _

theorem values_nonneg (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ)
    (hμ : μ ∈ values V W A) : 0 ≤ μ := by
  have h : ∀ {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] (B : E →ₗ[ℝ] F),
      μ ∈ eigenvaluesIncreasing B → 0 ≤ μ := by
    intro E F _ _ _ _ _ _ B hb
    simp only [eigenvaluesIncreasing, Finset.mem_sort, Finset.mem_image,
      Finset.mem_univ, true_and] at hb
    obtain ⟨i, rfl⟩ := hb
    exact GSVDPairedSpectral.gramValues_nonneg B i
  simp only [values, Finset.mem_sort, List.mem_toFinset, List.mem_append] at hμ
  rcases hμ with hl | hr
  · exact h A hl
  · exact h (LinearMap.adjoint A) hr

theorem left_inner (A : V.carrier →ₗ[ℝ] W.carrier)
    (pred : ℝ → Bool) (xs : List V.carrier) :
    ∀ i j : Fin (left V W A pred xs).length,
      V.innerProduct ((left V W A pred xs).get i)
        ((left V W A pred xs).get j) = if i = j then 1 else 0 := by
  exact buckets_inner V _ A.isSymmetric_adjoint_comp_self _
    ((values_nodup V W A).filter pred) xs

theorem right_inner (A : V.carrier →ₗ[ℝ] W.carrier)
    (pred : ℝ → Bool) (xs : List V.carrier) (ys : List W.carrier) :
    ∀ i j : Fin (right V W A pred xs ys).length,
      W.innerProduct ((right V W A pred xs ys).get i)
        ((right V W A pred xs ys).get j) = if i = j then 1 else 0 := by
  have aux : ∀ ms : List ℝ, ms.Nodup → (∀ μ ∈ ms, 0 ≤ μ) →
      ∀ i j : Fin (ms.flatMap (fun μ => rightBlock V W A μ xs ys)).length,
        W.innerProduct ((ms.flatMap (fun μ => rightBlock V W A μ xs ys)).get i)
          ((ms.flatMap (fun μ => rightBlock V W A μ xs ys)).get j) =
          if i = j then 1 else 0 := by
    intro ms hn hp
    induction ms with
    | nil => exact BasisFSV.nil_orthonormal W
    | cons μ ms ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      apply BasisFSV.concat_orthonormal W _ _
        (rightBlock_inner V W A μ (hp μ (by simp)) xs ys)
        (ih hnodup (fun ν hν => hp ν (by simp [hν])))
      intro i j
      have hi := rightBlock_mem V W A μ xs ys _ (List.get_mem _ i)
      obtain ⟨ν, hν, hj⟩ := List.mem_flatMap.mp (List.get_mem _ j)
      have hne : μ ≠ ν := by intro h; subst ν; exact hnot hν
      exact A.isSymmetric_self_comp_adjoint.orthogonalFamily_eigenspaces hne
        ⟨_, hi⟩ ⟨_, rightBlock_mem V W A ν xs ys _ hj⟩
  exact aux _ ((values_nodup V W A).filter pred)
    (fun μ hμ => values_nonneg V W A μ (List.mem_filter.mp hμ).1)

/-- The paired construction preserves every selected spectral subspace. -/
theorem right_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (pred : ℝ → Bool) (xs : List V.carrier) (ys : List W.carrier)
    (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤)
    (hys : Submodule.span ℝ {z | z ∈ ys} = ⊤) :
    Submodule.span ℝ {z | z ∈ right V W A pred xs ys} =
      ⨆ μ, ⨆ (_ : pred μ = true), Module.End.eigenspace (A ∘ₗ LinearMap.adjoint A) μ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨μ, hμ, hz⟩ := List.mem_flatMap.mp hz
    have hle : Module.End.eigenspace (A ∘ₗ LinearMap.adjoint A) μ ≤
        ⨆ ν, ⨆ (_ : pred ν = true), Module.End.eigenspace (A ∘ₗ LinearMap.adjoint A) ν :=
      le_iSup_of_le μ (le_iSup_of_le (List.mem_filter.mp hμ).2 le_rfl)
    exact hle (rightBlock_mem V W A μ xs ys z hz)
  · apply iSup₂_le
    intro μ hp
    by_cases he : Module.End.HasEigenvalue (A ∘ₗ LinearMap.adjoint A) μ
    · have hv := (mem_values V W A μ).mpr (Or.inr he)
      have hs : Submodule.span ℝ {z | z ∈ rightBlock V W A μ xs ys} =
          Module.End.eigenspace (A ∘ₗ LinearMap.adjoint A) μ := by
        by_cases hz : μ = 0
        · subst μ; exact rightBlock_span_zero V W A xs ys hys
        · exact rightBlock_span_pos V W A μ
            (lt_of_le_of_ne (values_nonneg V W A μ hv) (Ne.symm hz)) xs ys hxs
      rw [← hs]
      apply Submodule.span_mono
      intro z hz
      exact List.mem_flatMap.mpr ⟨μ, List.mem_filter.mpr ⟨hv, hp⟩, hz⟩
    · have hbot : Module.End.eigenspace (A ∘ₗ LinearMap.adjoint A) μ = ⊥ := by
        simpa only [Module.End.hasEigenvalue_iff, not_not] using he
      rw [hbot]; exact bot_le

theorem left_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (pred : ℝ → Bool) (xs : List V.carrier)
    (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤) :
    Submodule.span ℝ {u | u ∈ left V W A pred xs} =
      ⨆ μ, ⨆ (_ : pred μ = true), Module.End.eigenspace (LinearMap.adjoint A ∘ₗ A) μ := by
  change Submodule.span ℝ {u | u ∈ ((values V W A).filter pred).flatMap
    (fun μ => bucket V (LinearMap.adjoint A ∘ₗ A) μ xs)} = _
  rw [buckets_span V _ _ xs hxs]
  apply le_antisymm
  · apply iSup₂_le
    intro μ hμ
    exact le_iSup_of_le μ (le_iSup_of_le (List.mem_filter.mp hμ).2 le_rfl)
  · apply iSup₂_le
    intro μ hp
    by_cases he : Module.End.HasEigenvalue (LinearMap.adjoint A ∘ₗ A) μ
    · exact le_iSup_of_le μ (le_iSup_of_le
        (List.mem_filter.mpr ⟨(mem_values V W A μ).mpr (Or.inl he), hp⟩) le_rfl)
    · have hb : Module.End.eigenspace (LinearMap.adjoint A ∘ₗ A) μ = ⊥ := by
        simpa only [Module.End.hasEigenvalue_iff, not_not] using he
      rw [hb]; exact bot_le

theorem left_zero_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤) :
    Submodule.span ℝ {u | u ∈ left V W A (fun μ => decide (μ = 0)) xs} =
      LinearMap.ker A := by
  rw [left_span V W A _ xs hxs]
  simp only [decide_eq_true_eq, iSup_iSup_eq_left, Module.End.eigenspace_zero,
    LinearMap.ker_adjoint_comp_self]

theorem left_nonzero_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤) :
    Submodule.span ℝ {u | u ∈ left V W A (fun μ => decide (μ ≠ 0)) xs} =
      (LinearMap.ker A)ᗮ := by
  rw [left_span V W A _ xs hxs]
  simp only [decide_eq_true_eq]
  rw [nonzero_eigenspaces_eq V _ A.isSymmetric_adjoint_comp_self,
    LinearMap.ker_adjoint_comp_self]

theorem right_zero_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier)
    (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤)
    (hys : Submodule.span ℝ {z | z ∈ ys} = ⊤) :
    Submodule.span ℝ {z | z ∈ right V W A (fun μ => decide (μ = 0)) xs ys} =
      (LinearMap.range A)ᗮ := by
  rw [right_span V W A _ xs ys hxs hys]
  simp only [decide_eq_true_eq, iSup_iSup_eq_left, Module.End.eigenspace_zero,
    LinearMap.ker_self_comp_adjoint, LinearMap.orthogonal_range]

theorem right_nonzero_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier)
    (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤)
    (hys : Submodule.span ℝ {z | z ∈ ys} = ⊤) :
    Submodule.span ℝ {z | z ∈ right V W A (fun μ => decide (μ ≠ 0)) xs ys} =
      LinearMap.range A := by
  rw [right_span V W A _ xs ys hxs hys]
  simp only [decide_eq_true_eq]
  rw [nonzero_eigenspaces_eq W _ A.isSymmetric_self_comp_adjoint,
    LinearMap.ker_self_comp_adjoint, LinearMap.orthogonal_ker, LinearMap.adjoint_adjoint]

/-- Recover a squared singular value from a normalized domain vector. -/
theorem image_inner_self (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ)
    (xs : List V.carrier) (u : V.carrier) (hu : u ∈ leftBlock V W A μ xs) :
    W.innerProduct (A u) (A u) = μ := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
  have hon := bucket_inner V (LinearMap.adjoint A ∘ₗ A) μ xs i i
  have huu : inner ℝ u u = 1 := by
    change V.innerProduct u u = 1
    change V.innerProduct ((leftBlock V W A μ xs).get i)
      ((leftBlock V W A μ xs).get i) = _ at hon
    simpa only [hi, if_pos rfl] using hon
  change inner ℝ (A u) (A u) = μ
  rw [← A.adjoint_inner_right, leftBlock_eigen V W A μ xs u hu,
    real_inner_smul_right, huu, mul_one]

/-- Positive singular value attached to a canonical domain vector. -/
def singularValue (A : V.carrier →ₗ[ℝ] W.carrier) (u : V.carrier) : ℝ :=
  Real.sqrt (W.innerProduct (A u) (A u))

def normalizedImage (A : V.carrier →ₗ[ℝ] W.carrier) (u : V.carrier) : W.carrier :=
  (singularValue V W A u)⁻¹ • A u

theorem singularValue_pos (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (u : V.carrier)
    (hu : u ∈ left V W A (fun μ => decide (μ ≠ 0)) xs) :
    0 < singularValue V W A u := by
  obtain ⟨μ, hμ, hu⟩ := List.mem_flatMap.mp hu
  have hn := values_nonneg V W A μ (List.mem_filter.mp hμ).1
  have hz : μ ≠ 0 := by simpa using (List.mem_filter.mp hμ).2
  unfold singularValue
  rw [image_inner_self V W A μ xs u hu]
  exact Real.sqrt_pos.mpr (lt_of_le_of_ne hn (Ne.symm hz))

/-- The positive codomain list is literally the normalized image list in the
same order, so one shared SVD supplies both sides. -/
theorem right_nonzero_eq_map (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier) :
    right V W A (fun μ => decide (μ ≠ 0)) xs ys =
      (left V W A (fun μ => decide (μ ≠ 0)) xs).map (normalizedImage V W A) := by
  unfold right left
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro μ hμ
  have hn := values_nonneg V W A μ (List.mem_filter.mp hμ).1
  have hz : μ ≠ 0 := by simpa using (List.mem_filter.mp hμ).2
  rw [rightBlock_pos V W A μ (lt_of_le_of_ne hn (Ne.symm hz))]
  apply List.map_congr_left
  intro u hu
  simp only [normalizedImage, singularValue, image_inner_self V W A μ xs u hu]

/-- Exact pairing for every positive source vector. -/
theorem positive_pairing (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (u : V.carrier)
    (hu : u ∈ left V W A (fun μ => decide (μ ≠ 0)) xs) :
    A u = singularValue V W A u • normalizedImage V W A u := by
  simp [normalizedImage, smul_smul, ne_of_gt (singularValue_pos V W A xs u hu)]

end GLang.BasisPairedSpectral

namespace GLang.BasisPairedSpectral
section Transport
variable {V W V' W' : HSpace}
local instance : InnerProductSpace.Core ℝ V.carrier := V.innerIsIP.toIPSCore
local instance : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ W.carrier := W.innerIsIP.toIPSCore
local instance : NormedAddCommGroup W.carrier := W.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ W.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ V'.carrier := V'.innerIsIP.toIPSCore
local instance : NormedAddCommGroup V'.carrier := V'.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ V'.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ W'.carrier := W'.innerIsIP.toIPSCore
local instance : NormedAddCommGroup W'.carrier := W'.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ W'.carrier := InnerProductSpace.ofCore inferInstance

/-- Canonical domain selection commutes with an isometric coordinate change. -/
theorem leftBlock_map (e : V.carrier ≃ₗᵢ[ℝ] V'.carrier)
    (f : W.carrier ≃ₗᵢ[ℝ] W'.carrier)
    (A : V.carrier →ₗ[ℝ] W.carrier) (B : V'.carrier →ₗ[ℝ] W'.carrier)
    (h : ∀ x, B (e x) = f (A x)) (μ : ℝ) (xs : List V.carrier) :
    leftBlock V' W' B μ (xs.map e) = (leftBlock V W A μ xs).map e := by
  exact BasisSpectral.bucket_map e _ _ (BasisSpectral.gram_intertwines e f A B h) μ xs

/-- Pairing preserves exact ordered coordinate correspondence, not just spans. -/
theorem rightBlock_map (e : V.carrier ≃ₗᵢ[ℝ] V'.carrier)
    (f : W.carrier ≃ₗᵢ[ℝ] W'.carrier)
    (A : V.carrier →ₗ[ℝ] W.carrier) (B : V'.carrier →ₗ[ℝ] W'.carrier)
    (h : ∀ x, B (e x) = f (A x)) (μ : ℝ)
    (xs : List V.carrier) (ys : List W.carrier) :
    rightBlock V' W' B μ (xs.map e) (ys.map f) =
      (rightBlock V W A μ xs ys).map f := by
  unfold rightBlock
  split_ifs with h0
  · subst μ
    apply BasisSpectral.bucket_map f _ _
    intro y
    simp only [LinearMap.comp_apply, BasisSpectral.adjoint_intertwines e f A B h, h]
  · rw [leftBlock_map e f A B h]
    simp only [List.map_map]
    congr 1
    funext u
    simp [h]

theorem values_map (e : V.carrier ≃ₗᵢ[ℝ] V'.carrier)
    (f : W.carrier ≃ₗᵢ[ℝ] W'.carrier)
    (A : V.carrier →ₗ[ℝ] W.carrier) (B : V'.carrier →ₗ[ℝ] W'.carrier)
    (h : ∀ x, B (e x) = f (A x)) : values V' W' B = values V W A := by
  unfold values
  rw [BasisSpectral.eigenvaluesIncreasing_intertwines e f A B h,
    BasisSpectral.eigenvaluesIncreasing_intertwines f e (LinearMap.adjoint A)
      (LinearMap.adjoint B) (BasisSpectral.adjoint_intertwines e f A B h)]

theorem left_map (e : V.carrier ≃ₗᵢ[ℝ] V'.carrier)
    (f : W.carrier ≃ₗᵢ[ℝ] W'.carrier)
    (A : V.carrier →ₗ[ℝ] W.carrier) (B : V'.carrier →ₗ[ℝ] W'.carrier)
    (h : ∀ x, B (e x) = f (A x)) (pred : ℝ → Bool) (xs : List V.carrier) :
    left V' W' B pred (xs.map e) = (left V W A pred xs).map e := by
  unfold left
  rw [values_map e f A B h, List.map_flatMap]
  congr 1
  funext μ
  exact leftBlock_map e f A B h μ xs

theorem right_map (e : V.carrier ≃ₗᵢ[ℝ] V'.carrier)
    (f : W.carrier ≃ₗᵢ[ℝ] W'.carrier)
    (A : V.carrier →ₗ[ℝ] W.carrier) (B : V'.carrier →ₗ[ℝ] W'.carrier)
    (h : ∀ x, B (e x) = f (A x)) (pred : ℝ → Bool)
    (xs : List V.carrier) (ys : List W.carrier) :
    right V' W' B pred (xs.map e) (ys.map f) = (right V W A pred xs ys).map f := by
  unfold right
  rw [values_map e f A B h, List.map_flatMap]
  congr 1
  funext μ
  exact rightBlock_map e f A B h μ xs ys

end Transport
end GLang.BasisPairedSpectral
