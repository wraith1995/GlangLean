

import GLang.Proofs.Basis.OrthRelBridge
import GLang.Proofs.Basis.BasisListOrthonormal
import GLang.Numerics.Spectral.BasisFSVGSVD
import GLang.Numerics.Spectral.BasisCanonicalBlocks

namespace GLang
namespace BasisFSV

open scoped TensorProduct

inductive Side : Type
  | left
  | right
  deriving DecidableEq, Repr

/-! ## `onbList` — an orthonormal basis of a submodule, as a list -/

/-- Given an `HSpace V` and a submodule `K ⊆ V.carrier`, returns a list
    in `V.carrier` whose elements form an orthonormal basis of `K`
    (under the ambient inner product `V.innerProduct`). Length is
    `Module.finrank ℝ K`.

    Realized via Mathlib's `stdOrthonormalBasis ℝ ↥K`, then coerced from
    `K` into `V.carrier` via `Subtype.val`. -/
noncomputable def onbList (V : HSpace) (K : Submodule ℝ V.carrier) :
    List V.carrier :=
  letI _ := V.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V.carrier :=
    (V.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V.carrier :=
    InnerProductSpace.ofCore inferInstance
  List.ofFn (fun i : Fin (Module.finrank ℝ K) =>
    ((stdOrthonormalBasis ℝ K) i : V.carrier))

theorem onbList_length (V : HSpace) (K : Submodule ℝ V.carrier) :
    (onbList V K).length = Module.finrank ℝ K := by
  unfold onbList
  simp

theorem onbList_subset (V : HSpace) (K : Submodule ℝ V.carrier) :
    ∀ v ∈ onbList V K, v ∈ K := by
  letI _ := V.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V.carrier :=
    (V.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V.carrier :=
    InnerProductSpace.ofCore inferInstance
  intro v hv
  unfold onbList at hv
  rcases List.mem_ofFn.mp hv with ⟨i, hi⟩
  rw [← hi]
  exact ((stdOrthonormalBasis ℝ K) i).property

/-- The entries of `onbList V K` are orthonormal under `V.innerProduct`. -/
theorem onbList_orthonormal (V : HSpace) (K : Submodule ℝ V.carrier) :
    ∀ i j : Fin (onbList V K).length,
      V.innerProduct ((onbList V K).get i) ((onbList V K).get j) =
        if i = j then 1 else 0 := by
  letI _ := V.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V.carrier :=
    (V.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V.carrier :=
    InnerProductSpace.ofCore inferInstance
  intro i j
  -- The list has length finrank ℝ K.
  have hlen_eq : (onbList V K).length = Module.finrank ℝ K := by
    show (onbList V K).length = Module.finrank ℝ K
    unfold onbList
    simp
  have hi : i.val < Module.finrank ℝ K := hlen_eq ▸ i.isLt
  have hj : j.val < Module.finrank ℝ K := hlen_eq ▸ j.isLt
  set i' : Fin (Module.finrank ℝ K) := ⟨i.1, hi⟩ with hi'_def
  set j' : Fin (Module.finrank ℝ K) := ⟨j.1, hj⟩ with hj'_def
  -- The list's get returns the OrthonormalBasis value.
  have h_geti : (onbList V K).get i =
      ((stdOrthonormalBasis ℝ K) i' : V.carrier) := by
    unfold onbList
    rw [List.get_eq_getElem, List.getElem_ofFn]
  have h_getj : (onbList V K).get j =
      ((stdOrthonormalBasis ℝ K) j' : V.carrier) := by
    unfold onbList
    rw [List.get_eq_getElem, List.getElem_ofFn]
  rw [h_geti, h_getj]
  -- Reduce IP on V.carrier to IP on K via `Submodule.coe_inner`.
  have h_iff_K : V.innerProduct
        ((stdOrthonormalBasis ℝ K i' : V.carrier))
        ((stdOrthonormalBasis ℝ K j' : V.carrier))
      = @inner ℝ K _ (stdOrthonormalBasis ℝ K i') (stdOrthonormalBasis ℝ K j') := by
    show @inner ℝ V.carrier _ _ _ = @inner ℝ K _ _ _
    exact (Submodule.coe_inner K _ _).symm
  rw [h_iff_K]
  have h_onb : Orthonormal ℝ (stdOrthonormalBasis ℝ K) :=
    (stdOrthonormalBasis ℝ K).orthonormal
  rw [orthonormal_iff_ite] at h_onb
  rw [h_onb i' j']
  by_cases h_eq : i = j
  · have h_eq' : i' = j' := by
      apply Fin.ext
      show i.val = j.val
      exact Fin.val_eq_of_eq h_eq
    rw [if_pos h_eq, if_pos h_eq']
  · have h_neq' : i' ≠ j' := by
      intro h
      apply h_eq
      apply Fin.ext
      show i.val = j.val
      -- h : i' = j'; i' = ⟨i.val, hi⟩, j' = ⟨j.val, hj⟩; so i.val = j.val
      have : i'.val = j'.val := Fin.val_eq_of_eq h
      exact this
    rw [if_neg h_eq, if_neg h_neq']

/-! ## Bridge: `orthRel V.IP K` and `Kᗮ` (Mathlib) coincide pointwise -/

theorem mem_orthRel_iff_mem_orthogonal (V : HSpace)
    (K : Submodule ℝ V.carrier) (v : V.carrier) :
    letI _ := V.innerIsIP.toIPSCore
    letI _ : NormedAddCommGroup V.carrier :=
      (V.innerIsIP.toIPSCore).toNormedAddCommGroup
    letI _ : InnerProductSpace ℝ V.carrier :=
      InnerProductSpace.ofCore inferInstance
    v ∈ Submodule.orthRel V.innerProduct K ↔ v ∈ Kᗮ := by
  letI _ := V.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V.carrier :=
    (V.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V.carrier :=
    InnerProductSpace.ofCore inferInstance
  rw [HSpace.mem_orthRel_innerProduct_iff V K v, Submodule.mem_orthogonal]
  rfl

/-! ## Cross-orthogonality: K and orthRel(K) are mutually orthogonal -/

theorem orthRel_orthogonal_left (V : HSpace)
    (K : Submodule ℝ V.carrier)
    (u : V.carrier) (hu : u ∈ K)
    (w : V.carrier) (hw : w ∈ Submodule.orthRel V.innerProduct K) :
    V.innerProduct u w = 0 := by
  rw [HSpace.mem_orthRel_innerProduct_iff] at hw
  exact hw u hu

theorem orthRel_orthogonal_right (V : HSpace)
    (K : Submodule ℝ V.carrier)
    (u : V.carrier) (hu : u ∈ Submodule.orthRel V.innerProduct K)
    (w : V.carrier) (hw : w ∈ K) :
    V.innerProduct u w = 0 := by
  -- By symmetry of V.innerProduct.
  have := orthRel_orthogonal_left V K w hw u hu
  rw [V.innerIsIP.1 u w]
  exact this

/-! ## Generic orthonormality of `(if pred 0 then L₁ else []) ++ (if pred 1 then L₂ else [])` -/

/-- The predicate-gated concatenation of two orthonormal, mutually
    orthogonal lists is orthonormal for every predicate. -/
theorem ifconcat_orthonormal (V : HSpace) (pred : ℝ → Bool)
    (L₁ L₂ : List V.carrier)
    (h₁ : ∀ i j : Fin L₁.length,
            V.innerProduct (L₁.get i) (L₁.get j) = if i = j then 1 else 0)
    (h₂ : ∀ i j : Fin L₂.length,
            V.innerProduct (L₂.get i) (L₂.get j) = if i = j then 1 else 0)
    (h_cross : ∀ (i : Fin L₁.length) (j : Fin L₂.length),
                V.innerProduct (L₁.get i) (L₂.get j) = 0) :
    let us := (if pred 0 then L₁ else []) ++ (if pred 1 then L₂ else [])
    ∀ i j : Fin us.length,
      V.innerProduct (us.get i) (us.get j) = if i = j then 1 else 0 := by
  intro us
  by_cases h0 : pred 0 = true <;> by_cases h1 : pred 1 = true
  · have hus : us = L₁ ++ L₂ := by simp [us, h0, h1]
    rw [hus]; exact concat_orthonormal V L₁ L₂ h₁ h₂ h_cross
  · have hus : us = L₁ ++ [] := by simp [us, h0, h1]
    rw [hus]
    exact concat_orthonormal V L₁ [] h₁ (nil_orthonormal V)
      (fun _ j => absurd j.isLt (by simp))
  · have hus : us = [] ++ L₂ := by simp [us, h0, h1]
    rw [hus]
    exact concat_orthonormal V [] L₂ (nil_orthonormal V) h₂
      (fun i _ => absurd i.isLt (by simp))
  · have hus : us = [] ++ [] := by simp [us, h0, h1]
    rw [hus]
    exact concat_orthonormal V [] [] (nil_orthonormal V) (nil_orthonormal V)
      (fun i _ => absurd i.isLt (by simp))

theorem predZero_at0 : ((fun μ : ℝ => decide (μ = 0)) 0) = true := by simp
theorem predZero_at1 : ((fun μ : ℝ => decide (μ = 0)) 1) = false := by simp
theorem predNe_at0 : ((fun μ : ℝ => decide (μ ≠ 0)) 0) = false := by simp
theorem predNe_at1 : ((fun μ : ℝ => decide (μ ≠ 0)) 1) = true := by simp

/-! ## FSV — the two branches -/

/-- The `fig:sigalg` branch (Left): kernel block `UI` under `pred 0`,
    cokernel block `U` under `pred 1`. -/
noncomputable def fsvLeftGSVD {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) : List V₀.carrier :=
  (if pred 0 then hb₀.gsvdKerList hb₁ f else [])
  ++
  (if pred 1 then hb₀.gsvdCokerList hb₁ f else [])

/-- The `fig:sigalg` branch (Right): coimage block `VI` under `pred 0`,
    image block `V` under `pred 1`. -/
noncomputable def fsvRightGSVD {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) : List V₁.carrier :=
  (if pred 0 then hb₀.gsvdCoimgList hb₁ f else [])
  ++
  (if pred 1 then hb₀.gsvdImgList hb₁ f else [])

/-- The fallback branch (Left): `stdOrthonormalBasis` of `ker f` /
    `(ker f)⊥`. Only reached when the input lists are not bases. -/
noncomputable def fsvLeftONB (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) : List V₀.carrier :=
  (if pred 0 then onbList V₀ (LinearMap.ker f) else [])
  ++
  (if pred 1 then onbList V₀ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)) else [])

/-- The fallback branch (Right): `stdOrthonormalBasis` of `(range f)⊥` /
    `range f`. -/
noncomputable def fsvRightONB (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) : List V₁.carrier :=
  (if pred 0 then onbList V₁ (Submodule.orthRel V₁.innerProduct (LinearMap.range f)) else [])
  ++
  (if pred 1 then onbList V₁ (LinearMap.range f) else [])

/-! ## FSV — left side -/

noncomputable def fsvLeft (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (pred : ℝ → Bool)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    List V₀.carrier :=
  haveI := Classical.propDecidable (IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁)
  if h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁ then
    BasisPairedSpectral.left V₀ V₁ f pred vs₀
  else
    fsvLeftONB V₀ V₁ f pred

/-! ## FSV — right side -/

noncomputable def fsvRight (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (pred : ℝ → Bool)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    List V₁.carrier :=
  haveI := Classical.propDecidable (IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁)
  if h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁ then
    BasisPairedSpectral.right V₀ V₁ f pred vs₀ vs₁
  else
    fsvRightONB V₀ V₁ f pred

/-! ## Branch selection lemmas -/

theorem fsvLeft_of_bases {V₀ V₁ : HSpace} {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) :
    fsvLeft V₀ V₁ f pred vs₀ vs₁ = BasisPairedSpectral.left V₀ V₁ f pred vs₀ := by
  unfold fsvLeft
  exact dif_pos ⟨hb₀, hb₁⟩

theorem fsvLeft_of_not_bases {V₀ V₁ : HSpace} {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (h : ¬ (IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁))
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) :
    fsvLeft V₀ V₁ f pred vs₀ vs₁ = fsvLeftONB V₀ V₁ f pred := by
  unfold fsvLeft
  exact dif_neg h

theorem fsvRight_of_bases {V₀ V₁ : HSpace} {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) :
    fsvRight V₀ V₁ f pred vs₀ vs₁ = BasisPairedSpectral.right V₀ V₁ f pred vs₀ vs₁ := by
  unfold fsvRight
  exact dif_pos ⟨hb₀, hb₁⟩

theorem fsvRight_of_not_bases {V₀ V₁ : HSpace} {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (h : ¬ (IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁))
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) :
    fsvRight V₀ V₁ f pred vs₀ vs₁ = fsvRightONB V₀ V₁ f pred := by
  unfold fsvRight
  exact dif_neg h

section Shapes

variable {V₀ V₁ : HSpace} {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
  (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
  (f : V₀.carrier →ₗ[ℝ] V₁.carrier)

theorem fsvLeftGSVD_ker :
    fsvLeftGSVD hb₀ hb₁ f (fun μ => decide (μ = 0)) = hb₀.gsvdKerList hb₁ f := by
  unfold fsvLeftGSVD; rw [predZero_at0, predZero_at1]; simp

theorem fsvLeftGSVD_coker :
    fsvLeftGSVD hb₀ hb₁ f (fun μ => decide (μ ≠ 0)) = hb₀.gsvdCokerList hb₁ f := by
  unfold fsvLeftGSVD; rw [predNe_at0, predNe_at1]; simp

theorem fsvRightGSVD_img :
    fsvRightGSVD hb₀ hb₁ f (fun μ => decide (μ ≠ 0)) = hb₀.gsvdImgList hb₁ f := by
  unfold fsvRightGSVD; rw [predNe_at0, predNe_at1]; simp

theorem fsvRightGSVD_coimg :
    fsvRightGSVD hb₀ hb₁ f (fun μ => decide (μ = 0)) = hb₀.gsvdCoimgList hb₁ f := by
  unfold fsvRightGSVD; rw [predZero_at0, predZero_at1]; simp

theorem fsvLeftONB_ker :
    fsvLeftONB V₀ V₁ f (fun μ => decide (μ = 0)) = onbList V₀ (LinearMap.ker f) := by
  unfold fsvLeftONB; rw [predZero_at0, predZero_at1]; simp

theorem fsvLeftONB_coker :
    fsvLeftONB V₀ V₁ f (fun μ => decide (μ ≠ 0)) =
      onbList V₀ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)) := by
  unfold fsvLeftONB; rw [predNe_at0, predNe_at1]; simp

theorem fsvRightONB_img :
    fsvRightONB V₀ V₁ f (fun μ => decide (μ ≠ 0)) = onbList V₁ (LinearMap.range f) := by
  unfold fsvRightONB; rw [predNe_at0, predNe_at1]; simp

theorem fsvRightONB_coimg :
    fsvRightONB V₀ V₁ f (fun μ => decide (μ = 0)) =
      onbList V₁ (Submodule.orthRel V₁.innerProduct (LinearMap.range f)) := by
  unfold fsvRightONB; rw [predZero_at0, predZero_at1]; simp

end Shapes

/-! ## Exact canonical-matrix correspondence for embedding adequacy -/

section Corollaries

variable {V₀ V₁ : HSpace} {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
  (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
  (f : V₀.carrier →ₗ[ℝ] V₁.carrier)

/-- Exact source correspondence with the kernel columns of the paired SVD. -/
theorem fsvLeft_eq_canonicalUI :
    fsvLeft V₀ V₁ f (fun μ => decide (μ = 0)) vs₀ vs₁ =
      List.ofCoords vs₀ (hb₀.canonical hb₁ f).UI := by
  rw [fsvLeft_of_bases hb₀ hb₁]
  exact (ValuePairedSVD.UI_ofCoords hb₀ hb₁ f).symm

/-- Exact source correspondence with the domain-positive SVD columns. -/
theorem fsvLeft_eq_canonicalU :
    fsvLeft V₀ V₁ f (fun μ => decide (μ ≠ 0)) vs₀ vs₁ =
      List.ofCoords vs₀ (hb₀.canonical hb₁ f).U := by
  rw [fsvLeft_of_bases hb₀ hb₁]
  exact (ValuePairedSVD.U_ofCoords hb₀ hb₁ f).symm

/-- Exact source correspondence with the paired image columns. -/
theorem fsvRight_eq_canonicalV :
    fsvRight V₀ V₁ f (fun μ => decide (μ ≠ 0)) vs₀ vs₁ =
      List.ofCoords vs₁ (hb₀.canonical hb₁ f).V := by
  rw [fsvRight_of_bases hb₀ hb₁]
  exact (ValuePairedSVD.V_ofCoords hb₀ hb₁ f).symm

/-- Exact source correspondence with the independently chosen zero block. -/
theorem fsvRight_eq_canonicalVI :
    fsvRight V₀ V₁ f (fun μ => decide (μ = 0)) vs₀ vs₁ =
      List.ofCoords vs₁ (hb₀.canonical hb₁ f).VI := by
  rw [fsvRight_of_bases hb₀ hb₁]
  exact (ValuePairedSVD.VI_ofCoords hb₀ hb₁ f).symm

end Corollaries

/-! ## Subset obligations -/

/-- For `pred = (· = 0)`: every output vector lies in `ker f`. -/
theorem fsvLeft_subset_ker (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    ∀ v ∈ fsvLeft V₀ V₁ f (fun μ => decide (μ = 0)) vs₀ vs₁,
      v ∈ LinearMap.ker f := by
  intro v hv
  by_cases h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁
  · rw [fsvLeft_of_bases h.1 h.2] at hv
    have hs := BasisPairedSpectral.left_zero_span V₀ V₁ f vs₀
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.1.2)
    rw [← hs]
    exact Submodule.subset_span hv
  · rw [fsvLeft_of_not_bases h, fsvLeftONB_ker] at hv
    exact onbList_subset V₀ (LinearMap.ker f) v hv

/-- For `pred = (· ≠ 0)`: every output vector lies in `(ker f)⊥`. -/
theorem fsvLeft_subset_coker (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    ∀ v ∈ fsvLeft V₀ V₁ f (fun μ => decide (μ ≠ 0)) vs₀ vs₁,
      v ∈ Submodule.orthRel V₀.innerProduct (LinearMap.ker f) := by
  intro v hv
  by_cases h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁
  · rw [fsvLeft_of_bases h.1 h.2] at hv
    have hs := BasisPairedSpectral.left_nonzero_span_orthRel V₀ V₁ f vs₀
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.1.2)
    rw [← hs]
    exact Submodule.subset_span hv
  · rw [fsvLeft_of_not_bases h, fsvLeftONB_coker] at hv
    exact onbList_subset V₀ _ v hv

/-- For `pred = (· ≠ 0)`: every output vector lies in `range f`. -/
theorem fsvRight_subset_range (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    ∀ v ∈ fsvRight V₀ V₁ f (fun μ => decide (μ ≠ 0)) vs₀ vs₁,
      v ∈ LinearMap.range f := by
  intro v hv
  by_cases h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁
  · rw [fsvRight_of_bases h.1 h.2] at hv
    have hs := BasisPairedSpectral.right_nonzero_span V₀ V₁ f vs₀ vs₁
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.1.2)
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.2.2)
    rw [← hs]
    exact Submodule.subset_span hv
  · rw [fsvRight_of_not_bases h, fsvRightONB_img] at hv
    exact onbList_subset V₁ (LinearMap.range f) v hv

/-- For `pred = (· = 0)`: every output vector lies in `(range f)⊥`. -/
theorem fsvRight_subset_coimg (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    ∀ v ∈ fsvRight V₀ V₁ f (fun μ => decide (μ = 0)) vs₀ vs₁,
      v ∈ Submodule.orthRel V₁.innerProduct (LinearMap.range f) := by
  intro v hv
  by_cases h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁
  · rw [fsvRight_of_bases h.1 h.2] at hv
    have hs := BasisPairedSpectral.right_zero_span_orthRel V₀ V₁ f vs₀ vs₁
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.1.2)
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.2.2)
    rw [← hs]
    exact Submodule.subset_span hv
  · rw [fsvRight_of_not_bases h, fsvRightONB_coimg] at hv
    exact onbList_subset V₁ _ v hv

/-! ## Orthonormality obligations (every predicate) -/

theorem fsvLeftGSVD_orthonormal {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) :
    let us := fsvLeftGSVD hb₀ hb₁ f pred
    ∀ i j : Fin us.length,
      V₀.innerProduct (us.get i) (us.get j) = if i = j then 1 else 0 :=
  ifconcat_orthonormal V₀ pred _ _
    (hb₀.gsvdKerList_orthonormal hb₁ f)
    (hb₀.gsvdCokerList_orthonormal hb₁ f)
    (hb₀.gsvdKerList_cokerList_orthogonal hb₁ f)

theorem fsvRightGSVD_orthonormal {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) :
    let us := fsvRightGSVD hb₀ hb₁ f pred
    ∀ i j : Fin us.length,
      V₁.innerProduct (us.get i) (us.get j) = if i = j then 1 else 0 :=
  ifconcat_orthonormal V₁ pred _ _
    (hb₀.gsvdCoimgList_orthonormal hb₁ f)
    (hb₀.gsvdImgList_orthonormal hb₁ f)
    (hb₀.gsvdCoimgList_imgList_orthogonal hb₁ f)

theorem fsvLeftONB_orthonormal (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) :
    let us := fsvLeftONB V₀ V₁ f pred
    ∀ i j : Fin us.length,
      V₀.innerProduct (us.get i) (us.get j) = if i = j then 1 else 0 :=
  ifconcat_orthonormal V₀ pred _ _
    (onbList_orthonormal V₀ (LinearMap.ker f))
    (onbList_orthonormal V₀ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)))
    (fun i j => orthRel_orthogonal_left V₀ (LinearMap.ker f) _
      (onbList_subset V₀ _ _ (List.get_mem _ i)) _
      (onbList_subset V₀ _ _ (List.get_mem _ j)))

theorem fsvRightONB_orthonormal (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (pred : ℝ → Bool) :
    let us := fsvRightONB V₀ V₁ f pred
    ∀ i j : Fin us.length,
      V₁.innerProduct (us.get i) (us.get j) = if i = j then 1 else 0 :=
  ifconcat_orthonormal V₁ pred _ _
    (onbList_orthonormal V₁ (Submodule.orthRel V₁.innerProduct (LinearMap.range f)))
    (onbList_orthonormal V₁ (LinearMap.range f))
    (fun i j => orthRel_orthogonal_right V₁ (LinearMap.range f) _
      (onbList_subset V₁ _ _ (List.get_mem _ i)) _
      (onbList_subset V₁ _ _ (List.get_mem _ j)))

theorem fsvLeft_orthonormal (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (pred : ℝ → Bool)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    let us := fsvLeft V₀ V₁ f pred vs₀ vs₁
    ∀ i j : Fin us.length,
      V₀.innerProduct (us.get i) (us.get j) = if i = j then 1 else 0 := by
  by_cases h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁
  · rw [fsvLeft_of_bases h.1 h.2]
    exact BasisPairedSpectral.left_inner V₀ V₁ f pred vs₀
  · rw [fsvLeft_of_not_bases h]
    exact fsvLeftONB_orthonormal V₀ V₁ f pred

theorem fsvRight_orthonormal (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (pred : ℝ → Bool)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    let us := fsvRight V₀ V₁ f pred vs₀ vs₁
    ∀ i j : Fin us.length,
      V₁.innerProduct (us.get i) (us.get j) = if i = j then 1 else 0 := by
  by_cases h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁
  · rw [fsvRight_of_bases h.1 h.2]
    exact BasisPairedSpectral.right_inner V₀ V₁ f pred vs₀ vs₁
  · rw [fsvRight_of_not_bases h]
    exact fsvRightONB_orthonormal V₀ V₁ f pred

/-! ## Dimension obligations -/

/-- For `pred = (· = 0)`: output length = `Module.finrank ℝ (ker f)`. -/
theorem fsvLeft_dim_eq (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    (fsvLeft V₀ V₁ f (fun μ => decide (μ = 0)) vs₀ vs₁).length =
      Module.finrank ℝ (LinearMap.ker f) := by
  by_cases h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁
  · rw [fsvLeft_of_bases h.1 h.2]
    exact BasisPairedSpectral.left_zero_length V₀ V₁ f vs₀
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.1.2)
  · rw [fsvLeft_of_not_bases h, fsvLeftONB_ker, onbList_length]

/-- For `pred = (· ≠ 0)`: output length = `Module.finrank ℝ (range f)`. -/
theorem fsvRight_dim_eq (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    (fsvRight V₀ V₁ f (fun μ => decide (μ ≠ 0)) vs₀ vs₁).length =
      Module.finrank ℝ (LinearMap.range f) := by
  by_cases h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁
  · rw [fsvRight_of_bases h.1 h.2]
    exact BasisPairedSpectral.right_nonzero_length V₀ V₁ f vs₀ vs₁
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.1.2)
  · rw [fsvRight_of_not_bases h, fsvRightONB_img, onbList_length]

/-- For `pred = (· ≠ 0)`: output length =
    `Module.finrank ℝ (orthRel V₀.IP (ker f))`. -/
theorem fsvLeft_dim_eq_coker (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    (fsvLeft V₀ V₁ f (fun μ => decide (μ ≠ 0)) vs₀ vs₁).length =
      Module.finrank ℝ
        (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)) := by
  by_cases h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁
  · rw [fsvLeft_of_bases h.1 h.2]
    exact BasisPairedSpectral.left_nonzero_length_orthRel V₀ V₁ f vs₀
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.1.2)
  · rw [fsvLeft_of_not_bases h, fsvLeftONB_coker, onbList_length]

/-- For `pred = (· = 0)`: output length =
    `Module.finrank ℝ (orthRel V₁.IP (range f))`. -/
theorem fsvRight_dim_eq_coimg (V₀ V₁ : HSpace)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    (fsvRight V₀ V₁ f (fun μ => decide (μ = 0)) vs₀ vs₁).length =
      Module.finrank ℝ
        (Submodule.orthRel V₁.innerProduct (LinearMap.range f)) := by
  by_cases h : IsListBasis V₀ vs₀ ∧ IsListBasis V₁ vs₁
  · rw [fsvRight_of_bases h.1 h.2]
    exact BasisPairedSpectral.right_zero_length_orthRel V₀ V₁ f vs₀ vs₁
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.1.2)
      (by simpa only [HSpace.span_setOf_mem_eq_span_range_get] using h.2.2)
  · rw [fsvRight_of_not_bases h, fsvRightONB_coimg, onbList_length]

end BasisFSV
end GLang
