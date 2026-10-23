import GLang.Numerics.Spectral.BasisSpectral
import GLang.Proofs.Basis.BasisListOrthonormal
import GLang.Numerics.Spectral.BasisFSVGSVD

/-! # Soundness of the ordered spectral construction

These results concern the canonical source FSV construction. The live GSVD
canonicalization is proved equal to it in `GSVDCanonicalMatrices`. All proofs
use only standard Lean foundations.
-/
namespace GLang.BasisSpectral
noncomputable section

/-- The normalized greedy subsequence spans exactly the original list. -/
theorem normalizedLexInd_span_list (V : HSpace) (xs : List V.carrier) :
    Submodule.span ℝ {v | v ∈ normalizedLexInd V xs} = Submodule.span ℝ {v | v ∈ xs} := by
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  have hs : {v | v ∈ normalizedLexInd V xs} =
      Set.range (InnerProductSpace.gramSchmidtNormed ℝ (V.lexInd xs).get) := by
    ext v
    simp [normalizedLexInd]
  rw [hs]
  exact normalizedLexInd_span V xs

/-- List-indexed form of normalized Gram–Schmidt orthonormality. -/
theorem normalizedLexInd_inner (V : HSpace) (xs : List V.carrier) :
    ∀ i j : Fin (normalizedLexInd V xs).length,
      V.innerProduct ((normalizedLexInd V xs).get i) ((normalizedLexInd V xs).get j) =
        if i = j then 1 else 0 := by
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  have h := orthonormal_iff_ite.mp (normalizedLexInd_orthonormal V xs)
  intro i j
  have hlen : (normalizedLexInd V xs).length = (V.lexInd xs).length := by
    simp [normalizedLexInd]
  let i' : Fin (V.lexInd xs).length := ⟨i.val, hlen ▸ i.isLt⟩
  let j' : Fin (V.lexInd xs).length := ⟨j.val, hlen ▸ j.isLt⟩
  have heq : i' = j' ↔ i = j := by
    simp only [Fin.ext_iff, i', j']
  simpa only [normalizedLexInd, List.get_eq_getElem, List.getElem_ofFn,
    heq] using h i' j'

/-- An orthonormal output list has exactly the dimension of its span. -/
theorem length_eq_finrank_span (V : HSpace) (xs : List V.carrier)
    (hon : ∀ i j : Fin xs.length,
      V.innerProduct (xs.get i) (xs.get j) = if i = j then 1 else 0) :
    xs.length = Module.finrank ℝ (Submodule.span ℝ {v | v ∈ xs}) := by
  have h := finrank_span_eq_card (V.linearIndependent_of_orthonormal xs.get hon)
  rw [HSpace.span_setOf_mem_eq_span_range_get]
  simpa only [Fintype.card_fin] using h.symm

/-- Every spectral bucket is orthonormal, even if its input is redundant. -/
theorem bucket_inner (V : HSpace) (S : V.carrier →ₗ[ℝ] V.carrier)
    (μ : ℝ) (xs : List V.carrier) :
    ∀ i j : Fin (bucket V S μ xs).length,
      V.innerProduct ((bucket V S μ xs).get i) ((bucket V S μ xs).get j) =
        if i = j then 1 else 0 := by
  unfold bucket
  exact normalizedLexInd_inner _ _

/-- All output vectors belong to the specified eigenspace. -/
theorem bucket_mem (V : HSpace) (S : V.carrier →ₗ[ℝ] V.carrier)
    (μ : ℝ) (xs : List V.carrier) :
    ∀ v ∈ bucket V S μ xs, v ∈ Module.End.eigenspace S μ := by
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  intro v hv
  have hs : Submodule.span ℝ {w | w ∈ bucket V S μ xs} ≤ Module.End.eigenspace S μ := by
    unfold bucket
    rw [normalizedLexInd_span_list]
    apply Submodule.span_le.mpr
    intro w hw
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw
    exact Submodule.starProjection_apply_mem _ _
  exact hs (Submodule.subset_span hv)

/-- Spanning input vectors produce a spanning orthonormal basis of each
specified eigenspace. Linear independence of the input is unnecessary. -/
theorem bucket_span (V : HSpace) (S : V.carrier →ₗ[ℝ] V.carrier)
    (μ : ℝ) (xs : List V.carrier)
    (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ bucket V S μ xs} = Module.End.eigenspace S μ := by
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  unfold bucket
  rw [normalizedLexInd_span_list]
  have hs : {v | v ∈ xs.map (spectralProjector S μ)} =
      (spectralProjector S μ) '' {v | v ∈ xs} := by
    ext v
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
  rw [hs, ← Submodule.map_span, hxs, Submodule.map_top]
  exact Submodule.range_starProjection _

section Spectrum
variable (V : HSpace)
local instance : InnerProductSpace.Core ℝ V.carrier := V.innerIsIP.toIPSCore
local instance : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance

/-- Concatenated buckets span precisely the sum of their eigenspaces. -/
theorem buckets_span (S : V.carrier →ₗ[ℝ] V.carrier) (ms : List ℝ)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ ms.flatMap (fun μ => bucket V S μ xs)} =
      ⨆ μ ∈ ms, Module.End.eigenspace S μ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨μ, hμ, hv⟩ := List.mem_flatMap.mp hv
    have hle : Module.End.eigenspace S μ ≤ ⨆ μ ∈ ms, Module.End.eigenspace S μ :=
      le_iSup_of_le μ (le_iSup_of_le hμ le_rfl)
    exact hle (bucket_mem V S μ xs v hv)
  · apply iSup₂_le
    intro μ hμ
    rw [← bucket_span V S μ xs hxs]
    apply Submodule.span_mono
    intro v hv
    exact List.mem_flatMap.mpr ⟨μ, hμ, hv⟩

/-- Distinct eigenspaces contribute mutually orthogonal ordered buckets. -/
theorem buckets_inner (S : V.carrier →ₗ[ℝ] V.carrier) (hS : S.IsSymmetric)
    (ms : List ℝ) (hms : ms.Nodup) (xs : List V.carrier) :
    ∀ i j : Fin (ms.flatMap (fun μ => bucket V S μ xs)).length,
      V.innerProduct ((ms.flatMap (fun μ => bucket V S μ xs)).get i)
        ((ms.flatMap (fun μ => bucket V S μ xs)).get j) = if i = j then 1 else 0 := by
  induction ms with
  | nil => exact BasisFSV.nil_orthonormal V
  | cons μ ms ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hms
    apply BasisFSV.concat_orthonormal V _ _ (bucket_inner V S μ xs) (ih hnodup)
    intro i j
    have hi := bucket_mem V S μ xs _ (List.get_mem _ i)
    obtain ⟨ν, hν, hj⟩ := List.mem_flatMap.mp (List.get_mem _ j)
    have hne : μ ≠ ν := by intro h; subst ν; exact hnot hν
    exact hS.orthogonalFamily_eigenspaces hne ⟨_, hi⟩ ⟨_, bucket_mem V S ν xs _ hj⟩

/-- Filtering keeps exactly the eigenspaces satisfying the actual predicate. -/
theorem buckets_filter_span (S : V.carrier →ₗ[ℝ] V.carrier) (ms : List ℝ)
    (hms : ∀ μ, μ ∈ ms ↔ Module.End.HasEigenvalue S μ) (pred : ℝ → Bool)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ (ms.filter pred).flatMap (fun μ => bucket V S μ xs)} =
      ⨆ μ, ⨆ (_ : pred μ = true), Module.End.eigenspace S μ := by
  rw [buckets_span V S _ xs hxs]
  apply le_antisymm
  · apply iSup₂_le
    intro μ hμ
    exact le_iSup_of_le μ (le_iSup_of_le (List.mem_filter.mp hμ).2 le_rfl)
  · apply iSup₂_le
    intro μ hp
    by_cases he : Module.End.HasEigenvalue S μ
    · exact le_iSup_of_le μ (le_iSup_of_le (List.mem_filter.mpr ⟨(hms μ).mpr he, hp⟩) le_rfl)
    · have hbot : Module.End.eigenspace S μ = ⊥ := by
        simpa only [Module.End.hasEigenvalue_iff, not_not] using he
      rw [hbot]
      exact bot_le

/-- All nonzero eigenspaces of a symmetric operator span the orthogonal
complement of its kernel. -/
theorem nonzero_eigenspaces_eq (S : V.carrier →ₗ[ℝ] V.carrier) (hS : S.IsSymmetric) :
    (⨆ μ, ⨆ (_ : μ ≠ (0 : ℝ)), Module.End.eigenspace S μ) = (LinearMap.ker S)ᗮ := by
  let K := ⨆ μ, ⨆ (_ : μ ≠ (0 : ℝ)), Module.End.eigenspace S μ
  let Z := Module.End.eigenspace S 0
  have hle : K ≤ Zᗮ := by
    apply iSup₂_le
    intro μ hμ v hv
    rw [Submodule.mem_orthogonal]
    intro w hw
    exact hS.orthogonalFamily_eigenspaces hμ.symm ⟨w, hw⟩ ⟨v, hv⟩
  have hsup : K ⊔ Z = ⊤ := by
    apply le_antisymm le_top
    have hall : (⨆ μ, Module.End.eigenspace S μ) = ⊤ :=
      Submodule.orthogonal_eq_bot_iff.mp hS.orthogonalComplement_iSup_eigenspaces_eq_bot
    rw [← hall]
    apply iSup_le
    intro μ
    by_cases hμ : μ = 0
    · subst μ; exact le_sup_right
    · have hm : Module.End.eigenspace S μ ≤ K :=
        le_iSup_of_le μ (le_iSup_of_le hμ le_rfl)
      exact hm.trans le_sup_left
  have heq : K = Zᗮ := by
    apply eq_of_le_of_inf_le_of_sup_le hle (z := Z)
    · rw [inf_comm, Z.inf_orthogonal_eq_bot]
      exact bot_le
    · rw [hsup]
      exact le_top
  simpa only [K, Z, Module.End.eigenspace_zero] using heq

end Spectrum

section Eigenvalues
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem eigenvaluesIncreasing_nodup (A : E →ₗ[ℝ] F) : (eigenvaluesIncreasing A).Nodup :=
  Finset.sort_nodup _ _

theorem eigenvaluesIncreasing_mem_iff (A : E →ₗ[ℝ] F) (μ : ℝ) :
    μ ∈ eigenvaluesIncreasing A ↔ Module.End.HasEigenvalue (LinearMap.adjoint A ∘ₗ A) μ := by
  simp only [eigenvaluesIncreasing, Finset.mem_sort, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact A.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl i
  · exact A.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl
end Eigenvalues

section Filtered
variable (V W : HSpace)
local instance : InnerProductSpace.Core ℝ V.carrier := V.innerIsIP.toIPSCore
local instance : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ W.carrier := W.innerIsIP.toIPSCore
local instance : NormedAddCommGroup W.carrier := W.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ W.carrier := InnerProductSpace.ofCore inferInstance

theorem filteredLeft_inner (A : V.carrier →ₗ[ℝ] W.carrier)
    (pred : ℝ → Bool) (xs : List V.carrier) :
    ∀ i j : Fin (filteredLeft V W A pred xs).length,
      V.innerProduct ((filteredLeft V W A pred xs).get i)
        ((filteredLeft V W A pred xs).get j) = if i = j then 1 else 0 := by
  exact buckets_inner V _ A.isSymmetric_adjoint_comp_self _
    ((eigenvaluesIncreasing_nodup A).filter pred) xs

theorem filteredRight_inner (A : V.carrier →ₗ[ℝ] W.carrier)
    (pred : ℝ → Bool) (xs : List W.carrier) :
    ∀ i j : Fin (filteredRight V W A pred xs).length,
      W.innerProduct ((filteredRight V W A pred xs).get i)
        ((filteredRight V W A pred xs).get j) = if i = j then 1 else 0 := by
  exact buckets_inner W _ A.isSymmetric_self_comp_adjoint _
    ((eigenvaluesIncreasing_nodup (LinearMap.adjoint A)).filter pred) xs

theorem filteredLeft_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (pred : ℝ → Bool) (xs : List V.carrier)
    (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ filteredLeft V W A pred xs} =
      ⨆ μ, ⨆ (_ : pred μ = true), Module.End.eigenspace (LinearMap.adjoint A ∘ₗ A) μ := by
  exact buckets_filter_span V _ _ (eigenvaluesIncreasing_mem_iff A) pred xs hxs

theorem filteredRight_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (pred : ℝ → Bool) (xs : List W.carrier)
    (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ filteredRight V W A pred xs} =
      ⨆ μ, ⨆ (_ : pred μ = true), Module.End.eigenspace (A ∘ₗ LinearMap.adjoint A) μ := by
  apply buckets_filter_span W _ _ _ pred xs hxs
  intro μ
  simpa only [LinearMap.adjoint_adjoint] using
    eigenvaluesIncreasing_mem_iff (LinearMap.adjoint A) μ

theorem filteredLeft_zero_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ filteredLeft V W A (fun μ => decide (μ = 0)) xs} =
      LinearMap.ker A := by
  rw [filteredLeft_span V W A _ xs hxs]
  simp only [decide_eq_true_eq, iSup_iSup_eq_left, Module.End.eigenspace_zero,
    LinearMap.ker_adjoint_comp_self]

theorem filteredLeft_nonzero_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ filteredLeft V W A (fun μ => decide (μ ≠ 0)) xs} =
      (LinearMap.ker A)ᗮ := by
  rw [filteredLeft_span V W A _ xs hxs]
  simp only [decide_eq_true_eq]
  rw [nonzero_eigenspaces_eq V _ A.isSymmetric_adjoint_comp_self,
    LinearMap.ker_adjoint_comp_self]

theorem filteredRight_zero_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List W.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ filteredRight V W A (fun μ => decide (μ = 0)) xs} =
      (LinearMap.range A)ᗮ := by
  rw [filteredRight_span V W A _ xs hxs]
  simp only [decide_eq_true_eq, iSup_iSup_eq_left, Module.End.eigenspace_zero,
    LinearMap.ker_self_comp_adjoint, LinearMap.orthogonal_range]

theorem filteredRight_nonzero_span (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List W.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ filteredRight V W A (fun μ => decide (μ ≠ 0)) xs} =
      LinearMap.range A := by
  rw [filteredRight_span V W A _ xs hxs]
  simp only [decide_eq_true_eq]
  rw [nonzero_eigenspaces_eq W _ A.isSymmetric_self_comp_adjoint,
    LinearMap.ker_self_comp_adjoint, LinearMap.orthogonal_ker, LinearMap.adjoint_adjoint]

theorem filteredLeft_zero_length (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    (filteredLeft V W A (fun μ => decide (μ = 0)) xs).length = Module.finrank ℝ (LinearMap.ker A) := by
  rw [length_eq_finrank_span V _ (filteredLeft_inner V W A _ xs), filteredLeft_zero_span V W A xs hxs]

theorem filteredLeft_nonzero_length (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    (filteredLeft V W A (fun μ => decide (μ ≠ 0)) xs).length = Module.finrank ℝ (LinearMap.ker A)ᗮ := by
  rw [length_eq_finrank_span V _ (filteredLeft_inner V W A _ xs), filteredLeft_nonzero_span V W A xs hxs]

theorem filteredRight_zero_length (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List W.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    (filteredRight V W A (fun μ => decide (μ = 0)) xs).length = Module.finrank ℝ (LinearMap.range A)ᗮ := by
  rw [length_eq_finrank_span W _ (filteredRight_inner V W A _ xs), filteredRight_zero_span V W A xs hxs]

theorem filteredRight_nonzero_length (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List W.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    (filteredRight V W A (fun μ => decide (μ ≠ 0)) xs).length = Module.finrank ℝ (LinearMap.range A) := by
  rw [length_eq_finrank_span W _ (filteredRight_inner V W A _ xs), filteredRight_nonzero_span V W A xs hxs]
/-- Domain nonzero buckets have rank many columns, independently of the metric. -/
theorem filteredLeft_nonzero_length_eq_range (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    (filteredLeft V W A (fun μ => decide (μ ≠ 0)) xs).length =
      Module.finrank ℝ (LinearMap.range A) := by
  rw [filteredLeft_nonzero_length V W A xs hxs]
  have horth := (LinearMap.ker A).finrank_add_finrank_orthogonal
  have hrank := A.finrank_range_add_finrank_ker
  omega

/-- Codomain zero buckets have codimension-of-range many columns. -/
theorem filteredRight_zero_length_eq_sub_range (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List W.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    (filteredRight V W A (fun μ => decide (μ = 0)) xs).length =
      Module.finrank ℝ W.carrier - Module.finrank ℝ (LinearMap.range A) := by
  rw [filteredRight_zero_length V W A xs hxs]
  have horth := (LinearMap.range A).finrank_add_finrank_orthogonal
  omega

theorem filteredLeft_nonzero_span_orthRel (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ filteredLeft V W A (fun μ => decide (μ ≠ 0)) xs} =
      Submodule.orthRel V.innerProduct (LinearMap.ker A) := by
  rw [filteredLeft_nonzero_span V W A xs hxs]
  ext v
  rw [HSpace.mem_orthRel_innerProduct_iff, Submodule.mem_orthogonal]
  rfl

theorem filteredRight_zero_span_orthRel (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List W.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    Submodule.span ℝ {v | v ∈ filteredRight V W A (fun μ => decide (μ = 0)) xs} =
      Submodule.orthRel W.innerProduct (LinearMap.range A) := by
  rw [filteredRight_zero_span V W A xs hxs]
  ext v
  rw [HSpace.mem_orthRel_innerProduct_iff, Submodule.mem_orthogonal]
  rfl

theorem filteredLeft_nonzero_length_orthRel (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    (filteredLeft V W A (fun μ => decide (μ ≠ 0)) xs).length =
      Module.finrank ℝ (Submodule.orthRel V.innerProduct (LinearMap.ker A)) := by
  rw [length_eq_finrank_span V _ (filteredLeft_inner V W A _ xs),
    filteredLeft_nonzero_span_orthRel V W A xs hxs]

theorem filteredRight_zero_length_orthRel (A : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List W.carrier) (hxs : Submodule.span ℝ {v | v ∈ xs} = ⊤) :
    (filteredRight V W A (fun μ => decide (μ = 0)) xs).length =
      Module.finrank ℝ (Submodule.orthRel W.innerProduct (LinearMap.range A)) := by
  rw [length_eq_finrank_span W _ (filteredRight_inner V W A _ xs),
    filteredRight_zero_span_orthRel V W A xs hxs]

end Filtered

end
end GLang.BasisSpectral
