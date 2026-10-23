import GLang.Numerics.SVD.ValuePairedSVD
import GLang.Numerics.Spectral.BasisCanonicalCoordinates

/-! Exact source-to-matrix correspondence for the paired SVD convention. -/
noncomputable section
namespace GLang.ValuePairedSVD
open BasisSpectral

private theorem ofCoords_family {V : HSpace} {xs : List V.carrier}
    (hb : IsListBasis V xs) {k : ℕ} (z : Fin k → Fin xs.length → ℝ) :
    List.ofCoords xs (fun i j => z j i) = (List.ofFn z).map (coordinateChart hb) := by
  rw [List.ofCoords, List.map_ofFn]
  congr 1
  funext j
  exact (coordinateChart_apply hb (z j)).symm

variable {V W : HSpace} {xs : List V.carrier} {ys : List W.carrier}
  (hb : IsListBasis V xs) (hc : IsListBasis W ys) (A : V.carrier →ₗ[ℝ] W.carrier)

theorem domainPositive_coordinateChart :
    (domainPositive (hb.coordMatrix hc A) (IsListBasis.gram V xs) (IsListBasis.gram W ys)
      hb.gram_posDef hc.gram_posDef).map (coordinateChart hb) =
        BasisPairedSpectral.left V W A (fun μ => decide (μ ≠ 0)) xs := by
  have h := BasisPairedSpectral.left_map
    (V := metricSpace (IsListBasis.gram V xs) hb.gram_posDef)
    (W := metricSpace (IsListBasis.gram W ys) hc.gram_posDef)
    (V' := V) (W' := W) (coordinateChart hb) (coordinateChart hc)
    (Matrix.toLin' (hb.coordMatrix hc A)) A
    (fun a => (coordinateChart_intertwines hb hc A a).symm)
    (fun μ => decide (μ ≠ 0)) (coordinateBasis xs.length)
  rw [coordinateChart_basis] at h
  exact h.symm

theorem domainZero_coordinateChart :
    (domainZero (hb.coordMatrix hc A) (IsListBasis.gram V xs) (IsListBasis.gram W ys)
      hb.gram_posDef hc.gram_posDef).map (coordinateChart hb) =
        BasisPairedSpectral.left V W A (fun μ => decide (μ = 0)) xs := by
  have h := BasisPairedSpectral.left_map
    (V := metricSpace (IsListBasis.gram V xs) hb.gram_posDef)
    (W := metricSpace (IsListBasis.gram W ys) hc.gram_posDef)
    (V' := V) (W' := W) (coordinateChart hb) (coordinateChart hc)
    (Matrix.toLin' (hb.coordMatrix hc A)) A
    (fun a => (coordinateChart_intertwines hb hc A a).symm)
    (fun μ => decide (μ = 0)) (coordinateBasis xs.length)
  rw [coordinateChart_basis] at h
  exact h.symm

theorem codomainPositive_coordinateChart :
    (codomainPositive (hb.coordMatrix hc A) (IsListBasis.gram V xs) (IsListBasis.gram W ys)
      hb.gram_posDef hc.gram_posDef).map (coordinateChart hc) =
        BasisPairedSpectral.right V W A (fun μ => decide (μ ≠ 0)) xs ys := by
  have h := BasisPairedSpectral.right_map
    (V := metricSpace (IsListBasis.gram V xs) hb.gram_posDef)
    (W := metricSpace (IsListBasis.gram W ys) hc.gram_posDef)
    (V' := V) (W' := W) (coordinateChart hb) (coordinateChart hc)
    (Matrix.toLin' (hb.coordMatrix hc A)) A
    (fun a => (coordinateChart_intertwines hb hc A a).symm)
    (fun μ => decide (μ ≠ 0)) (coordinateBasis xs.length) (coordinateBasis ys.length)
  rw [coordinateChart_basis, coordinateChart_basis] at h
  exact h.symm

theorem codomainZero_coordinateChart :
    (codomainZero (hb.coordMatrix hc A) (IsListBasis.gram V xs) (IsListBasis.gram W ys)
      hb.gram_posDef hc.gram_posDef).map (coordinateChart hc) =
        BasisPairedSpectral.right V W A (fun μ => decide (μ = 0)) xs ys := by
  have h := BasisPairedSpectral.right_map
    (V := metricSpace (IsListBasis.gram V xs) hb.gram_posDef)
    (W := metricSpace (IsListBasis.gram W ys) hc.gram_posDef)
    (V' := V) (W' := W) (coordinateChart hb) (coordinateChart hc)
    (Matrix.toLin' (hb.coordMatrix hc A)) A
    (fun a => (coordinateChart_intertwines hb hc A a).symm)
    (fun μ => decide (μ = 0)) (coordinateBasis xs.length) (coordinateBasis ys.length)
  rw [coordinateChart_basis, coordinateChart_basis] at h
  exact h.symm

/-- Paired GSVD domain-positive columns are exactly the source list. -/
theorem U_ofCoords :
    List.ofCoords xs (decomposition (hb.coordMatrix hc A) (IsListBasis.gram V xs)
      (IsListBasis.gram W ys) hb.gram_posDef hc.gram_posDef).U =
        BasisPairedSpectral.left V W A (fun μ => decide (μ ≠ 0)) xs := by
  change List.ofCoords xs (fun i j => u _ _ _ _ _ j i) = _
  rw [ofCoords_family hb, ofFn_u]
  exact domainPositive_coordinateChart hb hc A

/-- Paired GSVD kernel columns are exactly the source list. -/
theorem UI_ofCoords :
    List.ofCoords xs (decomposition (hb.coordMatrix hc A) (IsListBasis.gram V xs)
      (IsListBasis.gram W ys) hb.gram_posDef hc.gram_posDef).UI =
        BasisPairedSpectral.left V W A (fun μ => decide (μ = 0)) xs := by
  change List.ofCoords xs (fun i j => ui _ _ _ _ _ j i) = _
  rw [ofCoords_family hb, ofFn_ui]
  exact domainZero_coordinateChart hb hc A

/-- Paired GSVD image columns are exactly the source list. -/
theorem V_ofCoords :
    List.ofCoords ys (decomposition (hb.coordMatrix hc A) (IsListBasis.gram V xs)
      (IsListBasis.gram W ys) hb.gram_posDef hc.gram_posDef).V =
        BasisPairedSpectral.right V W A (fun μ => decide (μ ≠ 0)) xs ys := by
  change List.ofCoords ys (fun i j => v _ _ _ _ _ j i) = _
  rw [ofCoords_family hc, ofFn_v]
  exact codomainPositive_coordinateChart hb hc A

/-- Paired GSVD coimage columns are exactly the source list. -/
theorem VI_ofCoords :
    List.ofCoords ys (decomposition (hb.coordMatrix hc A) (IsListBasis.gram V xs)
      (IsListBasis.gram W ys) hb.gram_posDef hc.gram_posDef).VI =
        BasisPairedSpectral.right V W A (fun μ => decide (μ = 0)) xs ys := by
  change List.ofCoords ys (fun i j => vi _ _ _ _ _ j i) = _
  rw [ofCoords_family hc, ofFn_vi]
  exact codomainZero_coordinateChart hb hc A

end GLang.ValuePairedSVD
