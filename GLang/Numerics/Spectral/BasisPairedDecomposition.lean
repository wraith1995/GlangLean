import GLang.Numerics.Spectral.BasisPairedSpectral
import GLang.Numerics.Spectral.BasisSpectralCoordinates

/-! Reconstruction and diagonal image coordinates for the paired convention. -/
noncomputable section
namespace GLang.BasisPairedSpectral
open BasisSpectral
open scoped BigOperators RealInnerProductSpace
variable (V W : HSpace)
local instance : InnerProductSpace.Core ℝ V.carrier := V.innerIsIP.toIPSCore
local instance : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ W.carrier := W.innerIsIP.toIPSCore
local instance : NormedAddCommGroup W.carrier := W.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ W.carrier := InnerProductSpace.ofCore inferInstance

/-- Orthonormality of paired positive columns indexed by the domain list. -/
theorem positive_images_orthonormal (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier) :
    Orthonormal ℝ (fun i : Fin (left V W A (fun μ => decide (μ ≠ 0)) xs).length =>
      normalizedImage V W A ((left V W A (fun μ => decide (μ ≠ 0)) xs).get i)) := by
  have h := right_inner V W A (fun μ => decide (μ ≠ 0)) xs ys
  rw [right_nonzero_eq_map] at h
  rw [orthonormal_iff_ite]
  intro i j
  let i' : Fin ((left V W A (fun μ => decide (μ ≠ 0)) xs).map
      (normalizedImage V W A)).length := ⟨i.val, by simpa using i.isLt⟩
  let j' : Fin ((left V W A (fun μ => decide (μ ≠ 0)) xs).map
      (normalizedImage V W A)).length := ⟨j.val, by simpa using j.isLt⟩
  simpa only [List.get_eq_getElem, List.getElem_map, i', j', Fin.mk.injEq,
    Fin.ext_iff] using h i' j'

/-- Image-coordinate conversion reduces to the positive singular-value diagonal. -/
theorem image_coordinates_diagonal (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier)
    (i j : Fin (left V W A (fun μ => decide (μ ≠ 0)) xs).length) :
    W.innerProduct
      (normalizedImage V W A ((left V W A (fun μ => decide (μ ≠ 0)) xs).get i))
      (A ((left V W A (fun μ => decide (μ ≠ 0)) xs).get j)) =
      if i = j then singularValue V W A
        ((left V W A (fun μ => decide (μ ≠ 0)) xs).get j) else 0 := by
  rw [positive_pairing V W A xs _ (List.get_mem _ j)]
  change inner ℝ
    (normalizedImage V W A ((left V W A (fun μ => decide (μ ≠ 0)) xs).get i))
    (singularValue V W A ((left V W A (fun μ => decide (μ ≠ 0)) xs).get j) •
      normalizedImage V W A ((left V W A (fun μ => decide (μ ≠ 0)) xs).get j)) = _
  rw [real_inner_smul_right,
    orthonormal_iff_ite.mp (positive_images_orthonormal V W A xs ys) i j]
  split_ifs <;> simp

/-- The canonical positive blocks reconstruct the source map exactly. -/
theorem reconstruction (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤)
    (x : V.carrier) :
    A x = ∑ i : Fin (left V W A (fun μ => decide (μ ≠ 0)) xs).length,
      (V.innerProduct ((left V W A (fun μ => decide (μ ≠ 0)) xs).get i) x *
        singularValue V W A ((left V W A (fun μ => decide (μ ≠ 0)) xs).get i)) •
        normalizedImage V W A ((left V W A (fun μ => decide (μ ≠ 0)) xs).get i) := by
  let us := left V W A (fun μ => decide (μ ≠ 0)) xs
  let K := (LinearMap.ker A)ᗮ
  have hon : Orthonormal ℝ us.get := by
    rw [orthonormal_iff_ite]
    exact left_inner V W A _ xs
  have hs : Submodule.span ℝ (Set.range us.get) = K := by
    rw [← HSpace.span_setOf_mem_eq_span_range_get]
    exact left_nonzero_span V W A xs hxs
  have hmem : ∀ i : Fin us.length, us.get i ∈ K := by
    intro i
    rw [← hs]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hp : ∑ i : Fin us.length, inner ℝ (us.get i) x • us.get i =
      K.starProjection x := by
    have hh := orthonormal_reconstruct us.get hon
      (x := K.starProjection x) (by rw [hs]; exact Submodule.starProjection_apply_mem _ _)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hmem i)]
  have hzero : A (x - K.starProjection x) = 0 := by
    apply LinearMap.mem_ker.mp
    have hz := K.sub_starProjection_mem_orthogonal x
    simpa only [K, Submodule.orthogonal_orthogonal] using hz
  have heq : A x = A (K.starProjection x) := by
    simpa only [map_sub, sub_eq_zero] using hzero
  rw [heq, ← hp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, positive_pairing V W A xs _ (List.get_mem us i), smul_smul]
  rfl

/-- Descending spectral blocks give the usual decreasing singular-value order. -/
theorem singularValues_antitone (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) :
    Antitone (fun i : Fin (left V W A (fun μ => decide (μ ≠ 0)) xs).length =>
      singularValue V W A ((left V W A (fun μ => decide (μ ≠ 0)) xs).get i)) := by
  have hp : (left V W A (fun μ => decide (μ ≠ 0)) xs).Pairwise
      (fun u v => singularValue V W A v ≤ singularValue V W A u) := by
    unfold left
    rw [List.pairwise_flatMap]
    constructor
    · intro μ _
      rw [List.pairwise_iff_get]
      intro i j _
      simp only [singularValue,
        image_inner_self V W A μ xs _ (List.get_mem _ i),
        image_inner_self V W A μ xs _ (List.get_mem _ j), le_refl]
    · have hs : ((values V W A).filter (fun μ => decide (μ ≠ 0))).Pairwise (· ≥ ·) :=
        (Finset.pairwise_sort _ _).filter _
      apply hs.imp
      intro μ ν hμν u hu z hz
      simp only [singularValue, image_inner_self V W A μ xs u hu,
        image_inner_self V W A ν xs z hz]
      exact Real.sqrt_le_sqrt hμν
  intro i j hij
  rcases eq_or_lt_of_le hij with heq | hlt
  · subst j; exact le_refl _
  · exact List.pairwise_iff_get.mp hp i j hlt

/-- Exact positive column count, independent of coordinate choices. -/
theorem positive_length (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤) :
    (left V W A (fun μ => decide (μ ≠ 0)) xs).length =
      Module.finrank ℝ (LinearMap.range A) := by
  rw [length_eq_finrank_span V _ (left_inner V W A _ xs), left_nonzero_span V W A xs hxs]
  have ho := (LinearMap.ker A).finrank_add_finrank_orthogonal
  have hr := A.finrank_range_add_finrank_ker
  omega

theorem kernel_length (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤) :
    (left V W A (fun μ => decide (μ = 0)) xs).length =
      Module.finrank ℝ V.carrier - Module.finrank ℝ (LinearMap.range A) := by
  rw [length_eq_finrank_span V _ (left_inner V W A _ xs), left_zero_span V W A xs hxs]
  have hr := A.finrank_range_add_finrank_ker
  omega

theorem cokernel_length (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier)
    (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤)
    (hys : Submodule.span ℝ {z | z ∈ ys} = ⊤) :
    (right V W A (fun μ => decide (μ = 0)) xs ys).length =
      Module.finrank ℝ W.carrier - Module.finrank ℝ (LinearMap.range A) := by
  rw [length_eq_finrank_span W _ (right_inner V W A _ xs ys), right_zero_span V W A xs ys hxs hys]
  have ho := (LinearMap.range A).finrank_add_finrank_orthogonal
  omega

theorem domain_positive_zero_inner (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤)
    (u z : V.carrier)
    (hu : u ∈ left V W A (fun μ => decide (μ ≠ 0)) xs)
    (hz : z ∈ left V W A (fun μ => decide (μ = 0)) xs) :
    V.innerProduct u z = 0 := by
  have hu' : u ∈ (LinearMap.ker A)ᗮ := by
    rw [← left_nonzero_span V W A xs hxs]
    exact Submodule.subset_span hu
  have hz' : z ∈ LinearMap.ker A := by
    rw [← left_zero_span V W A xs hxs]
    exact Submodule.subset_span hz
  change inner ℝ u z = 0
  rw [real_inner_comm]
  rw [Submodule.mem_orthogonal] at hu'
  exact hu' z hz'

theorem image_zero_inner (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier)
    (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤)
    (hys : Submodule.span ℝ {z | z ∈ ys} = ⊤)
    (u : V.carrier) (z : W.carrier)
    (hz : z ∈ right V W A (fun μ => decide (μ = 0)) xs ys) :
    W.innerProduct (normalizedImage V W A u) z = 0 := by
  have hz' : z ∈ (LinearMap.range A)ᗮ := by
    rw [← right_zero_span V W A xs ys hxs hys]
    exact Submodule.subset_span hz
  have hu : normalizedImage V W A u ∈ LinearMap.range A :=
    Submodule.smul_mem _ _ (LinearMap.mem_range_self A u)
  rw [Submodule.mem_orthogonal] at hz'
  exact hz' _ hu

theorem left_zero_length (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤) :
    (left V W A (fun μ => decide (μ = 0)) xs).length = Module.finrank ℝ (LinearMap.ker A) := by
  rw [length_eq_finrank_span V _ (left_inner V W A _ xs), left_zero_span V W A xs hxs]

theorem right_nonzero_length (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier)
    (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤) :
    (right V W A (fun μ => decide (μ ≠ 0)) xs ys).length = Module.finrank ℝ (LinearMap.range A) := by
  rw [right_nonzero_eq_map, List.length_map]
  exact positive_length V W A xs hxs

theorem left_nonzero_span_orthRel (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤) :
    Submodule.span ℝ {u | u ∈ left V W A (fun μ => decide (μ ≠ 0)) xs} =
      Submodule.orthRel V.innerProduct (LinearMap.ker A) := by
  rw [left_nonzero_span V W A xs hxs]
  ext u
  rw [HSpace.mem_orthRel_innerProduct_iff, Submodule.mem_orthogonal]
  rfl

theorem right_zero_span_orthRel (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier)
    (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤)
    (hys : Submodule.span ℝ {z | z ∈ ys} = ⊤) :
    Submodule.span ℝ {z | z ∈ right V W A (fun μ => decide (μ = 0)) xs ys} =
      Submodule.orthRel W.innerProduct (LinearMap.range A) := by
  rw [right_zero_span V W A xs ys hxs hys]
  ext z
  rw [HSpace.mem_orthRel_innerProduct_iff, Submodule.mem_orthogonal]
  rfl

theorem left_nonzero_length_orthRel (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤) :
    (left V W A (fun μ => decide (μ ≠ 0)) xs).length =
      Module.finrank ℝ (Submodule.orthRel V.innerProduct (LinearMap.ker A)) := by
  rw [length_eq_finrank_span V _ (left_inner V W A _ xs), left_nonzero_span_orthRel V W A xs hxs]

theorem right_zero_length_orthRel (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier)
    (hxs : Submodule.span ℝ {u | u ∈ xs} = ⊤)
    (hys : Submodule.span ℝ {z | z ∈ ys} = ⊤) :
    (right V W A (fun μ => decide (μ = 0)) xs ys).length =
      Module.finrank ℝ (Submodule.orthRel W.innerProduct (LinearMap.range A)) := by
  rw [length_eq_finrank_span W _ (right_inner V W A _ xs ys),
    right_zero_span_orthRel V W A xs ys hxs hys]

end GLang.BasisPairedSpectral
