import GLang.Numerics.Spectral.BasisSpectralProperties

/-! # Exact transport of ordered independent subsequences and Gram–Schmidt -/
noncomputable section
namespace GLang.BasisSpectral

private theorem mem_span_map_iff {V W : HSpace} (e : V.carrier ≃ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (x : V.carrier) :
    e x ∈ Submodule.span ℝ {v | v ∈ xs.map e} ↔ x ∈ Submodule.span ℝ {v | v ∈ xs} := by
  have hs : {v | v ∈ xs.map e} = e '' {v | v ∈ xs} := by
    ext v; simp only [List.mem_map, Set.mem_image, Set.mem_setOf_eq]
  rw [hs]
  exact Submodule.apply_mem_span_image_iff_mem_span (f := e.toLinearMap) e.injective

/-- Greedy selection commutes with injective coordinate changes and preserves
which input positions are chosen, not just the resulting span. -/
theorem lexIndAux_map {V W : HSpace} (e : V.carrier ≃ₗ[ℝ] W.carrier)
    (acc xs : List V.carrier) :
    HSpace.lexIndAux (V := W) (acc.map e) (xs.map e) =
      (HSpace.lexIndAux (V := V) acc xs).map e := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, HSpace.lexIndAux]
      rw [mem_span_map_iff]
      split_ifs
      · exact ih acc
      · simpa only [List.map_append, List.map_singleton] using ih (acc ++ [x])

theorem lexInd_map {V W : HSpace} (e : V.carrier ≃ₗ[ℝ] W.carrier)
    (xs : List V.carrier) : W.lexInd (xs.map e) = (V.lexInd xs).map e :=
  lexIndAux_map e [] xs

section GramSchmidt
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}

/-- The ordered Gram–Schmidt procedure commutes with linear isometries. -/
theorem gramSchmidt_map (e : E ≃ₗᵢ[ℝ] F) (f : Fin n → E) (j : Fin n) :
    InnerProductSpace.gramSchmidt ℝ (e ∘ f) j =
      e (InnerProductSpace.gramSchmidt ℝ f j) := by
  induction j using WellFoundedLT.induction with | ind j ih =>
  rw [InnerProductSpace.gramSchmidt_def, InnerProductSpace.gramSchmidt_def]
  simp only [Function.comp_apply, map_sub, map_sum, Submodule.starProjection_singleton]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [ih i (Finset.mem_Iio.mp hi)]
  simp only [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map,
    map_smul]

/-- Normalization also commutes with the same isometry, retaining signs. -/
theorem gramSchmidtNormed_map (e : E ≃ₗᵢ[ℝ] F) (f : Fin n → E) (j : Fin n) :
    InnerProductSpace.gramSchmidtNormed ℝ (e ∘ f) j =
      e (InnerProductSpace.gramSchmidtNormed ℝ f j) := by
  simp only [InnerProductSpace.gramSchmidtNormed, gramSchmidt_map,
    LinearIsometryEquiv.norm_map, map_smul]

private theorem gramSchmidtNormed_finCast {m : ℕ} (h : n = m) (f : Fin m → E) (i : Fin n) :
    InnerProductSpace.gramSchmidtNormed ℝ (fun j => f (Fin.cast h j)) i =
      InnerProductSpace.gramSchmidtNormed ℝ f (Fin.cast h i) := by
  subst m
  rfl
end GramSchmidt

section HSpaceTransport
variable {V W : HSpace}
local instance : InnerProductSpace.Core ℝ V.carrier := V.innerIsIP.toIPSCore
local instance : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ W.carrier := W.innerIsIP.toIPSCore
local instance : NormedAddCommGroup W.carrier := W.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ W.carrier := InnerProductSpace.ofCore inferInstance

/-- The complete ordered normalization stage commutes with an isometry. -/
theorem normalizedLexInd_map (e : V.carrier ≃ₗᵢ[ℝ] W.carrier) (xs : List V.carrier) :
    normalizedLexInd W (xs.map e) = (normalizedLexInd V xs).map e := by
  have hlex : W.lexInd (xs.map e) = (V.lexInd xs).map e := lexInd_map e.toLinearEquiv xs
  unfold normalizedLexInd
  calc
    List.ofFn (InnerProductSpace.gramSchmidtNormed ℝ (W.lexInd (xs.map e)).get) =
        List.ofFn (InnerProductSpace.gramSchmidtNormed ℝ ((V.lexInd xs).map e).get) :=
      congrArg (fun ys : List W.carrier =>
        List.ofFn (InnerProductSpace.gramSchmidtNormed ℝ ys.get)) hlex
    _ = _ := by
      simp only [List.map_ofFn, List.length_map]
      apply List.ext_getElem
      · simp
      · intro i hi hj
        simp only [List.getElem_ofFn]
        have hf : ((V.lexInd xs).map e).get =
            (fun j => (e ∘ (V.lexInd xs).get) (Fin.cast (List.length_map ..) j)) := by
          funext j
          simp only [List.get_eq_getElem, List.getElem_map, Function.comp_apply]
          rfl
        let j : Fin (V.lexInd xs).length := ⟨i, by simpa using hi⟩
        let k : Fin ((V.lexInd xs).map e).length := Fin.cast (List.length_map ..).symm j
        have hcast := gramSchmidtNormed_finCast (List.length_map (as := V.lexInd xs) e)
          (e ∘ (V.lexInd xs).get) k
        have hh : InnerProductSpace.gramSchmidtNormed ℝ ((V.lexInd xs).map e).get k =
            InnerProductSpace.gramSchmidtNormed ℝ (e ∘ (V.lexInd xs).get) j := by
          simpa only [hf, k, Fin.cast_cast, Fin.cast_refl] using hcast
        exact hh.trans (gramSchmidtNormed_map e (V.lexInd xs).get j)

/-- Orthogonal eigenspace projection commutes with an isometric intertwiner. -/
theorem spectralProjector_map (e : V.carrier ≃ₗᵢ[ℝ] W.carrier)
    (S : V.carrier →ₗ[ℝ] V.carrier) (T : W.carrier →ₗ[ℝ] W.carrier)
    (he : ∀ x, T (e x) = e (S x)) (μ : ℝ) (x : V.carrier) :
    spectralProjector T μ (e x) = e (spectralProjector S μ x) := by
  let K := Module.End.eigenspace S μ
  have hmem : e (spectralProjector S μ x) ∈ Module.End.eigenspace T μ := by
    rw [Module.End.mem_eigenspace_iff, he]
    have hp := Module.End.mem_eigenspace_iff.mp (Submodule.starProjection_apply_mem K x)
    simpa only [spectralProjector, K, map_smul] using congrArg e hp
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro w hw
  have hw' : e.symm w ∈ K := by
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    apply e.injective
    rw [← he, e.apply_symm_apply, hw, map_smul, e.apply_symm_apply]
  have horth := Submodule.sub_starProjection_mem_orthogonal (K := K) x
  have hi : inner ℝ (x - spectralProjector S μ x) (e.symm w) = 0 := by
    exact (real_inner_comm _ _).trans (horth _ hw')
  simpa only [← map_sub, ← e.inner_map_map, e.apply_symm_apply] using hi

/-- The full ordered spectral bucket commutes with a coordinate isometry. -/
theorem bucket_map (e : V.carrier ≃ₗᵢ[ℝ] W.carrier)
    (S : V.carrier →ₗ[ℝ] V.carrier) (T : W.carrier →ₗ[ℝ] W.carrier)
    (he : ∀ x, T (e x) = e (S x)) (μ : ℝ) (xs : List V.carrier) :
    bucket W T μ (xs.map e) = (bucket V S μ xs).map e := by
  unfold bucket
  have hm : (xs.map e).map (spectralProjector T μ) =
      (xs.map (spectralProjector S μ)).map e := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact spectralProjector_map e S T he μ x
  rw [hm]
  exact normalizedLexInd_map e _
end HSpaceTransport
end GLang.BasisSpectral
