

import GLang.Proofs.Basis.OrthRelBridge
import GLang.Numerics.SVD.ValueSVD
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

namespace GLang

/-! ## The "is a basis" predicate for our `List + HSpace` setup. -/

/-- `IsListBasis V vs` — `vs`, viewed as a length-indexed family `Fin
    vs.length → V.carrier` via `List.get`, is a basis of `V` as an
    ℝ-module. -/
def IsListBasis (V : HSpace) (vs : List V.carrier) : Prop :=
  LinearIndependent ℝ (fun i : Fin vs.length => vs.get i) ∧
    Submodule.span ℝ (Set.range (fun i : Fin vs.length => vs.get i)) = ⊤

/-- **Bridge (forward direction).** An `IsListBasis V vs` gives a
    `Module.Basis (Fin vs.length) ℝ V.carrier` whose underlying function
    is `fun i => vs.get i`. Proved via Mathlib's `Module.Basis.mk`
    (which takes `LinearIndependent` + `⊤ ≤ span`). -/
noncomputable def IsListBasis.toBasis {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) : Module.Basis (Fin vs.length) ℝ V.carrier :=
  Module.Basis.mk h.1 (le_of_eq h.2.symm)

/-- `IsListBasis.toBasis` underlying function is `List.get`. -/
@[simp] theorem IsListBasis.toBasis_apply {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) (i : Fin vs.length) :
    h.toBasis i = vs.get i := by
  unfold IsListBasis.toBasis
  exact Module.Basis.mk_apply _ _ i

/-- `finrank V = vs.length` when `vs` is a list basis. -/
theorem IsListBasis.finrank_eq {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) : Module.finrank ℝ V.carrier = vs.length := by
  rw [Module.finrank_eq_card_basis h.toBasis, Fintype.card_fin]

/-! ## Gram matrix -/

/-- The Gram matrix of a list of vectors in `V` under `V`'s inner product:
    `gram V vs i j = ⟨vᵢ, vⱼ⟩`. -/
noncomputable def IsListBasis.gram (V : HSpace) (vs : List V.carrier) :
    Matrix (Fin vs.length) (Fin vs.length) ℝ :=
  fun i j => V.innerProduct (vs.get i) (vs.get j)

/-- Bilinearity expansion, two-vector form:
    `⟨Σ aᵢ vᵢ, Σ bⱼ vⱼ⟩ = a ⬝ᵥ (G *ᵥ b)`. -/
theorem IsListBasis.innerProduct_sum_smul
    (V : HSpace) (vs : List V.carrier) (a b : Fin vs.length → ℝ) :
    V.innerProduct (∑ i, a i • vs.get i) (∑ j, b j • vs.get j) =
      a ⬝ᵥ (IsListBasis.gram V vs *ᵥ b) := by
  have h_outer : V.innerProduct (∑ i, a i • vs.get i) =
      ∑ i, a i • V.innerProduct (vs.get i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.map_smul]
  rw [h_outer, LinearMap.sum_apply]
  show _ = ∑ i, a i * (IsListBasis.gram V vs *ᵥ b) i
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.smul_apply, smul_eq_mul]
  show a i * V.innerProduct (vs.get i) (∑ j, b j • vs.get j) =
       a i * (∑ j, IsListBasis.gram V vs i j * b j)
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.map_smul]
  show b j • V.innerProduct (vs.get i) (vs.get j) =
    IsListBasis.gram V vs i j * b j
  show b j * V.innerProduct (vs.get i) (vs.get j) =
    V.innerProduct (vs.get i) (vs.get j) * b j
  ring

/-- Bilinearity expansion: `x ⬝ᵥ (G *ᵥ x) = ⟨Σ xᵢ vᵢ, Σ xᵢ vᵢ⟩`. -/
theorem IsListBasis.gram_dotProduct_mulVec
    (V : HSpace) (vs : List V.carrier) (x : Fin vs.length → ℝ) :
    x ⬝ᵥ (IsListBasis.gram V vs *ᵥ x) =
      V.innerProduct (∑ i, x i • vs.get i) (∑ j, x j • vs.get j) :=
  (IsListBasis.innerProduct_sum_smul V vs x x).symm

/-- Gram matrix is Hermitian (symmetric over ℝ). -/
theorem IsListBasis.gram_isHermitian (V : HSpace) (vs : List V.carrier) :
    (IsListBasis.gram V vs).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  show star (V.innerProduct (vs.get j) (vs.get i)) = V.innerProduct (vs.get i) (vs.get j)
  show V.innerProduct (vs.get j) (vs.get i) = V.innerProduct (vs.get i) (vs.get j)
  exact V.innerIsIP.1 _ _

/-- **Gram PD**: when `vs` is a list basis of `V`, its Gram matrix is positive
    definite. -/
theorem IsListBasis.gram_posDef {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) : (IsListBasis.gram V vs).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (IsListBasis.gram_isHermitian V vs) ?_
  intro x hx
  show 0 < x ⬝ᵥ (IsListBasis.gram V vs *ᵥ x)
  rw [IsListBasis.gram_dotProduct_mulVec]
  set y := ∑ i, x i • vs.get i
  have hy_ne : y ≠ 0 := by
    intro hy
    have hxx := h.1
    rw [Fintype.linearIndependent_iff] at hxx
    have hx_zero : ∀ i, x i = 0 := hxx x hy
    apply hx
    funext i
    exact hx_zero i
  have h_nn := V.innerIsIP.2.1 y
  have h_def := V.innerIsIP.2.2 y
  rcases lt_or_eq_of_le h_nn with h_pos | h_zero
  · exact h_pos
  · exfalso
    exact hy_ne (h_def h_zero.symm)

/-! ## Mathlib `Orthonormal` bridge and orthogonal-complement dimensions -/

/-- **Bridge to Mathlib `Orthonormal`.** Our "Kronecker-delta on
    `V.innerProduct`" orthonormality predicate is equivalent to
    Mathlib's `Orthonormal ℝ` predicate under the IPS bridge. The IPS
    instance is set up inline (not via a separate `def`) to keep `rfl`
    on `inner = V.innerProduct` working — the established pattern from
    `MoorePenroseChar`. -/
theorem HSpace.orthonormal_iff_innerProduct (V : HSpace) {n : ℕ}
    (f : Fin n → V.carrier) :
    letI _ := V.innerIsIP.toIPSCore
    letI _ : NormedAddCommGroup V.carrier :=
      (V.innerIsIP.toIPSCore).toNormedAddCommGroup
    letI _ : InnerProductSpace ℝ V.carrier :=
      InnerProductSpace.ofCore inferInstance
    Orthonormal ℝ f ↔ ∀ i j, V.innerProduct (f i) (f j) = if i = j then 1 else 0 := by
  letI _ := V.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V.carrier :=
    (V.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V.carrier :=
    InnerProductSpace.ofCore inferInstance
  rw [orthonormal_iff_ite]
  refine ⟨fun h i j => ?_, fun h i j => ?_⟩
  · have hrfl : V.innerProduct (f i) (f j) = @inner ℝ V.carrier _ (f i) (f j) := rfl
    rw [hrfl]; exact h i j
  · have hrfl : V.innerProduct (f i) (f j) = @inner ℝ V.carrier _ (f i) (f j) := rfl
    rw [← hrfl]; exact h i j

/-- Orthonormal (Kronecker-delta) families are linearly independent. -/
theorem HSpace.linearIndependent_of_orthonormal (V : HSpace) {n : ℕ}
    (f : Fin n → V.carrier)
    (h : ∀ i j, V.innerProduct (f i) (f j) = if i = j then 1 else 0) :
    LinearIndependent ℝ f := by
  letI _ := V.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V.carrier :=
    (V.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V.carrier :=
    InnerProductSpace.ofCore inferInstance
  exact ((V.orthonormal_iff_innerProduct f).mpr h).linearIndependent

theorem HSpace.finrank_add_finrank_orthRel (V : HSpace) (K : Submodule ℝ V.carrier) :
    Module.finrank ℝ K +
      Module.finrank ℝ (Submodule.orthRel V.innerProduct K) =
      Module.finrank ℝ V.carrier := by
  letI _ := V.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V.carrier :=
    (V.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V.carrier :=
    InnerProductSpace.ofCore inferInstance
  have hK : Submodule.orthRel V.innerProduct K = Kᗮ := by
    ext v
    rw [HSpace.mem_orthRel_innerProduct_iff V K v, Submodule.mem_orthogonal]
    rfl
  rw [hK]
  exact Submodule.finrank_add_finrank_orthogonal K

/-- A linearly independent family of `k` vectors inside a submodule `K`
    forces `k ≤ finrank K`. -/
theorem Submodule.card_le_finrank_of_linearIndependent_mem
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (K : Submodule ℝ V) {k : ℕ} (u : Fin k → V)
    (hli : LinearIndependent ℝ u) (hmem : ∀ j, u j ∈ K) :
    k ≤ Module.finrank ℝ K := by
  let u' : Fin k → K := fun j => ⟨u j, hmem j⟩
  have hli' : LinearIndependent ℝ u' := by
    apply LinearIndependent.of_comp K.subtype
    have : K.subtype ∘ u' = u := by funext j; rfl
    rw [this]; exact hli
  have := hli'.fintype_card_le_finrank
  simpa using this

/-! ## Coordinates in a list basis -/

/-- Coordinates of `v` in the list basis `vs` (`Basis.repr` of `toBasis`). -/
noncomputable def IsListBasis.coords {V : HSpace} {vs : List V.carrier}
    (hb : IsListBasis V vs) (v : V.carrier) : Fin vs.length → ℝ :=
  hb.toBasis.repr v

/-- `Σ coordsᵢ(v) • vᵢ = v`. -/
theorem IsListBasis.sum_coords_smul {V : HSpace} {vs : List V.carrier}
    (hb : IsListBasis V vs) (v : V.carrier) :
    ∑ i, hb.coords v i • vs.get i = v := by
  have h := hb.toBasis.sum_repr v
  simp only [IsListBasis.toBasis_apply] at h
  exact h

/-- `coords (Σ cᵢ • vᵢ) = c`. -/
theorem IsListBasis.coords_sum_smul {V : HSpace} {vs : List V.carrier}
    (hb : IsListBasis V vs) (c : Fin vs.length → ℝ) :
    hb.coords (∑ i, c i • vs.get i) = c := by
  have h := hb.toBasis.repr_sum_self c
  simp only [IsListBasis.toBasis_apply] at h
  funext i
  simp only [IsListBasis.coords]
  rw [h]

noncomputable def IsListBasis.coordMatrix {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) :
    Matrix (Fin vs₁.length) (Fin vs₀.length) ℝ :=
  LinearMap.toMatrix hb₀.toBasis hb₁.toBasis f

/-- `f (Σ cᵢ • vᵢ) = Σ (A c)ⱼ • wⱼ` where `A` is the coordinate matrix. -/
theorem IsListBasis.apply_sum_smul {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (c : Fin vs₀.length → ℝ) :
    f (∑ i, c i • vs₀.get i) =
      ∑ j, ((hb₀.coordMatrix hb₁ f) *ᵥ c) j • vs₁.get j := by
  set x := ∑ i, c i • vs₀.get i with hx
  have hc : hb₀.coords x = c := hb₀.coords_sum_smul c
  have h1 : hb₀.coordMatrix hb₁ f *ᵥ (hb₀.toBasis.repr x) = hb₁.toBasis.repr (f x) :=
    LinearMap.toMatrix_mulVec_repr hb₀.toBasis hb₁.toBasis f x
  have h2 := hb₁.sum_coords_smul (f x)
  rw [← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  show hb₁.toBasis.repr (f x) j = _
  rw [← h1]
  have : (⇑(hb₀.toBasis.repr x) : Fin vs₀.length → ℝ) = c := hc
  rw [this]

/-- If `f (Σ cᵢ • vᵢ) = 0` then `A c = 0` (linear independence of `vs₁`). -/
theorem IsListBasis.coordMatrix_mulVec_eq_zero {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
    (f : V₀.carrier →ₗ[ℝ] V₁.carrier) (c : Fin vs₀.length → ℝ)
    (h : f (∑ i, c i • vs₀.get i) = 0) :
    (hb₀.coordMatrix hb₁ f) *ᵥ c = 0 := by
  rw [hb₀.apply_sum_smul hb₁ f c] at h
  have hli := hb₁.1
  rw [Fintype.linearIndependent_iff] at hli
  funext j
  exact hli _ h j

/-! ## Reading matrix columns back as vectors -/

/-- The columns of `U` read back as vectors of `V` via the list `vs`:
    `(ofCoords vs U).get j = Σᵢ U i j • vs.get i`. -/
noncomputable def List.ofCoords {V : Type*} [AddCommGroup V] [Module ℝ V]
    (vs : List V) {k : ℕ} (U : Matrix (Fin vs.length) (Fin k) ℝ) : List V :=
  List.ofFn fun j : Fin k => ∑ i, U i j • vs.get i

@[simp] theorem List.ofCoords_length {V : Type*} [AddCommGroup V] [Module ℝ V]
    (vs : List V) {k : ℕ} (U : Matrix (Fin vs.length) (Fin k) ℝ) :
    (List.ofCoords vs U).length = k := by
  simp [List.ofCoords]

theorem List.ofCoords_get {V : Type*} [AddCommGroup V] [Module ℝ V]
    (vs : List V) {k : ℕ} (U : Matrix (Fin vs.length) (Fin k) ℝ)
    (j : Fin (List.ofCoords vs U).length) :
    (List.ofCoords vs U).get j =
      ∑ i, U i (Fin.cast (List.ofCoords_length vs U) j) • vs.get i := by
  simp only [List.ofCoords, List.get_eq_getElem, List.getElem_ofFn]
  rfl

theorem List.mem_ofCoords {V : Type*} [AddCommGroup V] [Module ℝ V]
    (vs : List V) {k : ℕ} (U : Matrix (Fin vs.length) (Fin k) ℝ)
    {v : V} (hv : v ∈ List.ofCoords vs U) :
    ∃ j : Fin k, v = ∑ i, U i j • vs.get i := by
  unfold List.ofCoords at hv
  rcases List.mem_ofFn.mp hv with ⟨j, hj⟩
  exact ⟨j, hj.symm⟩

/-- `M *ᵥ (column j of N) = column j of (M * N)`. -/
theorem mulVec_col_eq {l m k : Type*} [Fintype m]
    (M : Matrix l m ℝ) (N : Matrix m k ℝ) (j : k) :
    M *ᵥ (fun i => N i j) = fun i => (M * N) i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

/-- `(column j of U) ᵥ* G ⬝ᵥ c = ((Uᵀ * G) *ᵥ c) j`. -/
theorem vecMul_dotProduct_eq_mulVec_transpose {m k : Type*} [Fintype m]
    (U : Matrix m k ℝ) (G : Matrix m m ℝ) (c : m → ℝ) (j : k) :
    ((fun i => U i j) ᵥ* G) ⬝ᵥ c = ((Uᵀ * G) *ᵥ c) j := by
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]

/-- Inner products of `ofCoords` entries are entries of `Uᵀ · G · U'`. -/
theorem IsListBasis.innerProduct_ofCoords_get (V : HSpace) (vs : List V.carrier)
    {k k' : ℕ} (U : Matrix (Fin vs.length) (Fin k) ℝ)
    (U' : Matrix (Fin vs.length) (Fin k') ℝ)
    (j : Fin (List.ofCoords vs U).length) (j' : Fin (List.ofCoords vs U').length) :
    V.innerProduct ((List.ofCoords vs U).get j) ((List.ofCoords vs U').get j') =
      (Uᵀ * IsListBasis.gram V vs * U')
        (Fin.cast (List.ofCoords_length vs U) j)
        (Fin.cast (List.ofCoords_length vs U') j') := by
  rw [List.ofCoords_get, List.ofCoords_get, IsListBasis.innerProduct_sum_smul,
    Matrix.dotProduct_mulVec, Matrix.mul_apply']
  congr 1

/-- `Uᵀ G U = 1` ⇒ the `ofCoords vs U` entries are orthonormal. -/
theorem IsListBasis.ofCoords_orthonormal (V : HSpace) (vs : List V.carrier)
    {k : ℕ} (U : Matrix (Fin vs.length) (Fin k) ℝ)
    (hU : Uᵀ * IsListBasis.gram V vs * U = 1) :
    ∀ i j : Fin (List.ofCoords vs U).length,
      V.innerProduct ((List.ofCoords vs U).get i) ((List.ofCoords vs U).get j) =
        if i = j then 1 else 0 := by
  intro i j
  rw [IsListBasis.innerProduct_ofCoords_get, hU, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij, if_neg]
    intro h
    apply hij
    simpa using h

/-- `Uᵀ G U' = 0` ⇒ the `ofCoords vs U` and `ofCoords vs U'` entries are
    mutually orthogonal. -/
theorem IsListBasis.ofCoords_cross_orthogonal (V : HSpace) (vs : List V.carrier)
    {k k' : ℕ} (U : Matrix (Fin vs.length) (Fin k) ℝ)
    (U' : Matrix (Fin vs.length) (Fin k') ℝ)
    (hU : Uᵀ * IsListBasis.gram V vs * U' = 0) :
    ∀ (i : Fin (List.ofCoords vs U).length) (j : Fin (List.ofCoords vs U').length),
      V.innerProduct ((List.ofCoords vs U).get i) ((List.ofCoords vs U').get j) = 0 := by
  intro i j
  rw [IsListBasis.innerProduct_ofCoords_get, hU]
  rfl

/-- `Uᵀ G U = 1` ⇒ the `ofCoords vs U` entries are linearly independent. -/
theorem IsListBasis.ofCoords_linearIndependent (V : HSpace) (vs : List V.carrier)
    {k : ℕ} (U : Matrix (Fin vs.length) (Fin k) ℝ)
    (hU : Uᵀ * IsListBasis.gram V vs * U = 1) :
    LinearIndependent ℝ
      (fun j : Fin (List.ofCoords vs U).length => (List.ofCoords vs U).get j) :=
  V.linearIndependent_of_orthonormal _ (IsListBasis.ofCoords_orthonormal V vs U hU)

/-! ## The GSVD of `f` relative to two list bases (`fig:sigalg`) -/

section GSVDBlocks

variable {V₀ V₁ : HSpace} {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
  (hb₀ : IsListBasis V₀ vs₀) (hb₁ : IsListBasis V₁ vs₁)
  (f : V₀.carrier →ₗ[ℝ] V₁.carrier)

/-- The GSVD of `f`'s coordinate matrix relative to the Gram matrices of
    the two list bases — the routine of `fig:sigalg` / `def:gsvd`, shared
    verbatim with the value language's `.gsvd*` arms. -/
noncomputable def IsListBasis.gsvd : GSVDecomposition vs₀.length vs₁.length :=
  matrixGSVD (hb₀.coordMatrix hb₁ f) (IsListBasis.gram V₀ vs₀) (IsListBasis.gram V₁ vs₁)

noncomputable def IsListBasis.gsvdKerList : List V₀.carrier :=
  List.ofCoords vs₀ (hb₀.gsvd hb₁ f).UI

noncomputable def IsListBasis.gsvdCokerList : List V₀.carrier :=
  List.ofCoords vs₀ (hb₀.gsvd hb₁ f).U

noncomputable def IsListBasis.gsvdImgList : List V₁.carrier :=
  List.ofCoords vs₁ (hb₀.gsvd hb₁ f).V

noncomputable def IsListBasis.gsvdCoimgList : List V₁.carrier :=
  List.ofCoords vs₁ (hb₀.gsvd hb₁ f).VI

/-! ### Lengths -/

@[simp] theorem IsListBasis.gsvdKerList_length :
    (hb₀.gsvdKerList hb₁ f).length = vs₀.length - (hb₀.gsvd hb₁ f).r := by
  simp [IsListBasis.gsvdKerList]

@[simp] theorem IsListBasis.gsvdCokerList_length :
    (hb₀.gsvdCokerList hb₁ f).length = (hb₀.gsvd hb₁ f).r := by
  simp [IsListBasis.gsvdCokerList]

@[simp] theorem IsListBasis.gsvdImgList_length :
    (hb₀.gsvdImgList hb₁ f).length = (hb₀.gsvd hb₁ f).r := by
  simp [IsListBasis.gsvdImgList]

@[simp] theorem IsListBasis.gsvdCoimgList_length :
    (hb₀.gsvdCoimgList hb₁ f).length = vs₁.length - (hb₀.gsvd hb₁ f).r := by
  simp [IsListBasis.gsvdCoimgList]

/-! ### Orthonormality (from the block-orthogonality spec) -/

theorem IsListBasis.gsvdKerList_orthonormal :
    ∀ i j : Fin (hb₀.gsvdKerList hb₁ f).length,
      V₀.innerProduct ((hb₀.gsvdKerList hb₁ f).get i) ((hb₀.gsvdKerList hb₁ f).get j) =
        if i = j then 1 else 0 :=
  IsListBasis.ofCoords_orthonormal V₀ vs₀ _
    (matrixGSVD_UI_orth _ _ _ hb₀.gram_posDef hb₁.gram_posDef)

theorem IsListBasis.gsvdCokerList_orthonormal :
    ∀ i j : Fin (hb₀.gsvdCokerList hb₁ f).length,
      V₀.innerProduct ((hb₀.gsvdCokerList hb₁ f).get i) ((hb₀.gsvdCokerList hb₁ f).get j) =
        if i = j then 1 else 0 :=
  IsListBasis.ofCoords_orthonormal V₀ vs₀ _
    (matrixGSVD_U_orth _ _ _ hb₀.gram_posDef hb₁.gram_posDef)

theorem IsListBasis.gsvdImgList_orthonormal :
    ∀ i j : Fin (hb₀.gsvdImgList hb₁ f).length,
      V₁.innerProduct ((hb₀.gsvdImgList hb₁ f).get i) ((hb₀.gsvdImgList hb₁ f).get j) =
        if i = j then 1 else 0 :=
  IsListBasis.ofCoords_orthonormal V₁ vs₁ _
    (matrixGSVD_V_orth _ _ _ hb₀.gram_posDef hb₁.gram_posDef)

theorem IsListBasis.gsvdCoimgList_orthonormal :
    ∀ i j : Fin (hb₀.gsvdCoimgList hb₁ f).length,
      V₁.innerProduct ((hb₀.gsvdCoimgList hb₁ f).get i) ((hb₀.gsvdCoimgList hb₁ f).get j) =
        if i = j then 1 else 0 :=
  IsListBasis.ofCoords_orthonormal V₁ vs₁ _
    (matrixGSVD_VI_orth _ _ _ hb₀.gram_posDef hb₁.gram_posDef)

/-- `U ⊥ UI`: kernel-block vectors are orthogonal to cokernel-block vectors. -/
theorem IsListBasis.gsvdKerList_cokerList_orthogonal :
    ∀ (i : Fin (hb₀.gsvdKerList hb₁ f).length) (j : Fin (hb₀.gsvdCokerList hb₁ f).length),
      V₀.innerProduct ((hb₀.gsvdKerList hb₁ f).get i) ((hb₀.gsvdCokerList hb₁ f).get j) = 0 := by
  intro i j
  rw [V₀.innerIsIP.1]
  exact IsListBasis.ofCoords_cross_orthogonal V₀ vs₀ _ _
    (matrixGSVD_U_UI_orth _ _ _ hb₀.gram_posDef hb₁.gram_posDef) j i

/-- `V ⊥ VI`: coimage-block vectors are orthogonal to image-block vectors. -/
theorem IsListBasis.gsvdCoimgList_imgList_orthogonal :
    ∀ (i : Fin (hb₀.gsvdCoimgList hb₁ f).length) (j : Fin (hb₀.gsvdImgList hb₁ f).length),
      V₁.innerProduct ((hb₀.gsvdCoimgList hb₁ f).get i) ((hb₀.gsvdImgList hb₁ f).get j) = 0 := by
  intro i j
  rw [V₁.innerIsIP.1]
  exact IsListBasis.ofCoords_cross_orthogonal V₁ vs₁ _ _
    (matrixGSVD_V_VI_orth _ _ _ hb₀.gram_posDef hb₁.gram_posDef) j i

/-! ### Subset facts (the four-fundamental-subspace identifications) -/

theorem IsListBasis.gsvdKerList_subset_ker :
    ∀ v ∈ hb₀.gsvdKerList hb₁ f, v ∈ LinearMap.ker f := by
  intro v hv
  obtain ⟨j, rfl⟩ := List.mem_ofCoords _ _ hv
  rw [LinearMap.mem_ker, hb₀.apply_sum_smul hb₁ f]
  have h : hb₀.coordMatrix hb₁ f * (hb₀.gsvd hb₁ f).UI = 0 :=
    matrixGSVD_mul_UI (hb₀.coordMatrix hb₁ f) _ _ hb₀.gram_posDef hb₁.gram_posDef
  have hcol : (hb₀.coordMatrix hb₁ f) *ᵥ (fun i => (hb₀.gsvd hb₁ f).UI i j) = 0 := by
    rw [mulVec_col_eq, h]
    rfl
  rw [hcol]
  simp

theorem IsListBasis.gsvdCokerList_subset_coker :
    ∀ v ∈ hb₀.gsvdCokerList hb₁ f,
      v ∈ Submodule.orthRel V₀.innerProduct (LinearMap.ker f) := by
  intro v hv
  obtain ⟨j, rfl⟩ := List.mem_ofCoords _ _ hv
  rw [HSpace.mem_orthRel_innerProduct_iff']
  intro u hu
  have hc : (hb₀.coordMatrix hb₁ f) *ᵥ hb₀.coords u = 0 := by
    apply hb₀.coordMatrix_mulVec_eq_zero hb₁ f
    rw [hb₀.sum_coords_smul u]
    exact LinearMap.mem_ker.mp hu
  have h0 : ((hb₀.gsvd hb₁ f).Uᵀ * IsListBasis.gram V₀ vs₀) *ᵥ hb₀.coords u = 0 :=
    matrixGSVD_Ut_MW_mulVec_eq_zero (hb₀.coordMatrix hb₁ f) _ _
      hb₀.gram_posDef hb₁.gram_posDef _ hc
  conv_lhs => rw [← hb₀.sum_coords_smul u]
  rw [IsListBasis.innerProduct_sum_smul, Matrix.dotProduct_mulVec,
    vecMul_dotProduct_eq_mulVec_transpose]
  show (((hb₀.gsvd hb₁ f).Uᵀ * IsListBasis.gram V₀ vs₀) *ᵥ hb₀.coords u) j = 0
  rw [h0]
  rfl

theorem IsListBasis.gsvdImgList_subset_range :
    ∀ v ∈ hb₀.gsvdImgList hb₁ f, v ∈ LinearMap.range f := by
  intro v hv
  obtain ⟨j, rfl⟩ := List.mem_ofCoords _ _ hv
  have hσ : (hb₀.gsvd hb₁ f).σ j ≠ 0 := ne_of_gt ((hb₀.gsvd hb₁ f).σ_pos j)
  have h : hb₀.coordMatrix hb₁ f * (hb₀.gsvd hb₁ f).U =
      (hb₀.gsvd hb₁ f).V * Matrix.diagonal (hb₀.gsvd hb₁ f).σ :=
    matrixGSVD_mul_U (hb₀.coordMatrix hb₁ f) _ _ hb₀.gram_posDef hb₁.gram_posDef
  refine ⟨∑ l, (((hb₀.gsvd hb₁ f).σ j)⁻¹ • fun l => (hb₀.gsvd hb₁ f).U l j) l • vs₀.get l, ?_⟩
  rw [hb₀.apply_sum_smul hb₁ f, Matrix.mulVec_smul, mulVec_col_eq, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mul_diagonal]
  rw [mul_comm ((hb₀.gsvd hb₁ f).V i j), ← mul_assoc, inv_mul_cancel₀ hσ, one_mul]

theorem IsListBasis.gsvdCoimgList_subset_coimg :
    ∀ v ∈ hb₀.gsvdCoimgList hb₁ f,
      v ∈ Submodule.orthRel V₁.innerProduct (LinearMap.range f) := by
  intro v hv
  obtain ⟨j, rfl⟩ := List.mem_ofCoords _ _ hv
  rw [HSpace.mem_orthRel_innerProduct_iff']
  intro u hu
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hu
  have h : (hb₀.gsvd hb₁ f).VIᵀ * IsListBasis.gram V₁ vs₁ * hb₀.coordMatrix hb₁ f = 0 :=
    matrixGSVD_VIt_MV_mul (hb₀.coordMatrix hb₁ f) _ _ hb₀.gram_posDef hb₁.gram_posDef
  conv_lhs => rw [← hb₀.sum_coords_smul x]
  rw [hb₀.apply_sum_smul hb₁ f, IsListBasis.innerProduct_sum_smul, Matrix.dotProduct_mulVec,
    vecMul_dotProduct_eq_mulVec_transpose, Matrix.mulVec_mulVec]
  show (((hb₀.gsvd hb₁ f).VIᵀ * IsListBasis.gram V₁ vs₁ * hb₀.coordMatrix hb₁ f) *ᵥ
    hb₀.coords x) j = 0
  rw [h]
  simp

/-! ### Linear independence -/

theorem IsListBasis.gsvdKerList_linearIndependent :
    LinearIndependent ℝ
      (fun j : Fin (hb₀.gsvdKerList hb₁ f).length => (hb₀.gsvdKerList hb₁ f).get j) :=
  V₀.linearIndependent_of_orthonormal _ (hb₀.gsvdKerList_orthonormal hb₁ f)

theorem IsListBasis.gsvdCokerList_linearIndependent :
    LinearIndependent ℝ
      (fun j : Fin (hb₀.gsvdCokerList hb₁ f).length => (hb₀.gsvdCokerList hb₁ f).get j) :=
  V₀.linearIndependent_of_orthonormal _ (hb₀.gsvdCokerList_orthonormal hb₁ f)

theorem IsListBasis.gsvdImgList_linearIndependent :
    LinearIndependent ℝ
      (fun j : Fin (hb₀.gsvdImgList hb₁ f).length => (hb₀.gsvdImgList hb₁ f).get j) :=
  V₁.linearIndependent_of_orthonormal _ (hb₀.gsvdImgList_orthonormal hb₁ f)

theorem IsListBasis.gsvdCoimgList_linearIndependent :
    LinearIndependent ℝ
      (fun j : Fin (hb₀.gsvdCoimgList hb₁ f).length => (hb₀.gsvdCoimgList hb₁ f).get j) :=
  V₁.linearIndependent_of_orthonormal _ (hb₀.gsvdCoimgList_orthonormal hb₁ f)

/-! ### Dimensions

`|UI| = m − r` linearly independent vectors in `ker f`, `|U| = r` in
`(ker f)⊥`, and `dim ker + dim ker⊥ = m` pin both dimensions; dually on
the codomain side. -/

theorem IsListBasis.finrank_ker_and_coker :
    Module.finrank ℝ (LinearMap.ker f) = vs₀.length - (hb₀.gsvd hb₁ f).r ∧
    Module.finrank ℝ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)) =
      (hb₀.gsvd hb₁ f).r := by
  have h1 := Submodule.card_le_finrank_of_linearIndependent_mem (LinearMap.ker f) _
    (hb₀.gsvdKerList_linearIndependent hb₁ f)
    (fun j => hb₀.gsvdKerList_subset_ker hb₁ f _ (List.get_mem _ _))
  have h2 := Submodule.card_le_finrank_of_linearIndependent_mem
    (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)) _
    (hb₀.gsvdCokerList_linearIndependent hb₁ f)
    (fun j => hb₀.gsvdCokerList_subset_coker hb₁ f _ (List.get_mem _ _))
  rw [IsListBasis.gsvdKerList_length] at h1
  rw [IsListBasis.gsvdCokerList_length] at h2
  have h3 := V₀.finrank_add_finrank_orthRel (LinearMap.ker f)
  rw [hb₀.finrank_eq] at h3
  have h4 := (hb₀.gsvd hb₁ f).r_le_m
  omega

theorem IsListBasis.finrank_range_and_coimg :
    Module.finrank ℝ (LinearMap.range f) = (hb₀.gsvd hb₁ f).r ∧
    Module.finrank ℝ (Submodule.orthRel V₁.innerProduct (LinearMap.range f)) =
      vs₁.length - (hb₀.gsvd hb₁ f).r := by
  have h1 := Submodule.card_le_finrank_of_linearIndependent_mem (LinearMap.range f) _
    (hb₀.gsvdImgList_linearIndependent hb₁ f)
    (fun j => hb₀.gsvdImgList_subset_range hb₁ f _ (List.get_mem _ _))
  have h2 := Submodule.card_le_finrank_of_linearIndependent_mem
    (Submodule.orthRel V₁.innerProduct (LinearMap.range f)) _
    (hb₀.gsvdCoimgList_linearIndependent hb₁ f)
    (fun j => hb₀.gsvdCoimgList_subset_coimg hb₁ f _ (List.get_mem _ _))
  rw [IsListBasis.gsvdImgList_length] at h1
  rw [IsListBasis.gsvdCoimgList_length] at h2
  have h3 := V₁.finrank_add_finrank_orthRel (LinearMap.range f)
  rw [hb₁.finrank_eq] at h3
  have h4 := (hb₀.gsvd hb₁ f).r_le_n
  omega

theorem IsListBasis.gsvdKerList_length_eq_finrank :
    (hb₀.gsvdKerList hb₁ f).length = Module.finrank ℝ (LinearMap.ker f) := by
  rw [IsListBasis.gsvdKerList_length, (hb₀.finrank_ker_and_coker hb₁ f).1]

theorem IsListBasis.gsvdCokerList_length_eq_finrank :
    (hb₀.gsvdCokerList hb₁ f).length =
      Module.finrank ℝ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)) := by
  rw [IsListBasis.gsvdCokerList_length, (hb₀.finrank_ker_and_coker hb₁ f).2]

theorem IsListBasis.gsvdImgList_length_eq_finrank :
    (hb₀.gsvdImgList hb₁ f).length = Module.finrank ℝ (LinearMap.range f) := by
  rw [IsListBasis.gsvdImgList_length, (hb₀.finrank_range_and_coimg hb₁ f).1]

theorem IsListBasis.gsvdCoimgList_length_eq_finrank :
    (hb₀.gsvdCoimgList hb₁ f).length =
      Module.finrank ℝ (Submodule.orthRel V₁.innerProduct (LinearMap.range f)) := by
  rw [IsListBasis.gsvdCoimgList_length, (hb₀.finrank_range_and_coimg hb₁ f).2]

end GSVDBlocks

end GLang
