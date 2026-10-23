import GLang.Numerics.Spectral.BasisMetricCoordinates
import GLang.Numerics.Spectral.BasisSpectralFilteredTransport

/-! Exact source/numerical canonical FSV correspondence in ordered Gram coordinates. -/
noncomputable section
namespace GLang.BasisSpectral

/-- Numeric left canonical vectors reconstruct precisely the source filtered list,
including every sign, bucket order, and within-bucket LexInd choice. -/
theorem leftVectors_coordinateChart {V W : HSpace}
    {xs : List V.carrier} {ys : List W.carrier}
    (hb : IsListBasis V xs) (hc : IsListBasis W ys)
    (A : V.carrier →ₗ[ℝ] W.carrier) (pred : ℝ → Bool) :
    (leftVectors (hb.coordMatrix hc A) (IsListBasis.gram V xs) (IsListBasis.gram W ys)
      hb.gram_posDef hc.gram_posDef pred).map (coordinateChart hb) =
        filteredLeft V W A pred xs := by
  have h := filteredLeft_map
    (V := metricSpace (IsListBasis.gram V xs) hb.gram_posDef)
    (W := metricSpace (IsListBasis.gram W ys) hc.gram_posDef)
    (V' := V) (W' := W)
    (coordinateChart hb) (coordinateChart hc)
    (Matrix.toLin' (hb.coordMatrix hc A)) A
    (fun a => (coordinateChart_intertwines hb hc A a).symm)
    pred (coordinateBasis xs.length)
  rw [coordinateChart_basis] at h
  exact h.symm

/-- Numeric right canonical vectors reconstruct precisely the source filtered list. -/
theorem rightVectors_coordinateChart {V W : HSpace}
    {xs : List V.carrier} {ys : List W.carrier}
    (hb : IsListBasis V xs) (hc : IsListBasis W ys)
    (A : V.carrier →ₗ[ℝ] W.carrier) (pred : ℝ → Bool) :
    (rightVectors (hb.coordMatrix hc A) (IsListBasis.gram V xs) (IsListBasis.gram W ys)
      hb.gram_posDef hc.gram_posDef pred).map (coordinateChart hc) =
        filteredRight V W A pred ys := by
  have h := filteredRight_map
    (V := metricSpace (IsListBasis.gram V xs) hb.gram_posDef)
    (W := metricSpace (IsListBasis.gram W ys) hc.gram_posDef)
    (V' := V) (W' := W)
    (coordinateChart hb) (coordinateChart hc)
    (Matrix.toLin' (hb.coordMatrix hc A)) A
    (fun a => (coordinateChart_intertwines hb hc A a).symm)
    pred (coordinateBasis ys.length)
  rw [coordinateChart_basis] at h
  exact h.symm

/-- Bridge to the existing adequacy convention for interpreting matrix columns. -/
theorem ofCoords_columns {V : HSpace} {xs : List V.carrier}
    (hb : IsListBasis V xs) (zs : List (Fin xs.length → ℝ)) :
    List.ofCoords xs (columns zs) = zs.map (coordinateChart hb) := by
  calc
    _ = (List.ofFn zs.get).map (coordinateChart hb) := by
      rw [List.ofCoords, List.map_ofFn]
      congr 1
      funext j
      exact (coordinateChart_apply hb (zs.get j)).symm
    _ = _ := by rw [List.ofFn_get]

/-- Left embedding correspondence in the literal `List.ofCoords` API used by
operational adequacy, with no paired-GSVD identification. -/
theorem leftMatrix_ofCoords {V W : HSpace}
    {xs : List V.carrier} {ys : List W.carrier}
    (hb : IsListBasis V xs) (hc : IsListBasis W ys)
    (A : V.carrier →ₗ[ℝ] W.carrier) (pred : ℝ → Bool) :
    List.ofCoords xs (leftMatrix (hb.coordMatrix hc A)
      (IsListBasis.gram V xs) (IsListBasis.gram W ys) hb.gram_posDef hc.gram_posDef pred) =
        filteredLeft V W A pred xs := by
  exact (ofCoords_columns hb _).trans (leftVectors_coordinateChart hb hc A pred)

/-- Right embedding correspondence in the existing column interpretation API. -/
theorem rightMatrix_ofCoords {V W : HSpace}
    {xs : List V.carrier} {ys : List W.carrier}
    (hb : IsListBasis V xs) (hc : IsListBasis W ys)
    (A : V.carrier →ₗ[ℝ] W.carrier) (pred : ℝ → Bool) :
    List.ofCoords ys (rightMatrix (hb.coordMatrix hc A)
      (IsListBasis.gram V xs) (IsListBasis.gram W ys) hb.gram_posDef hc.gram_posDef pred) =
        filteredRight V W A pred ys := by
  exact (ofCoords_columns hc _).trans (rightVectors_coordinateChart hb hc A pred)
end GLang.BasisSpectral
