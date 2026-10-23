import GLang.Proofs.Adequacy.TermsRREF
import GLang.Numerics.RREF.RREFCanonicalRep

/-! RREF selects precisely the left-to-right greedy independent columns.
The proof uses only the existing decomposition fields; no numerical coherence
axiom or extra hypothesis is needed. -/
namespace GLang
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A column belongs to the span of earlier pivot columns exactly when it is
not itself a pivot. Later pivots have zero coefficients by row-echelon shape. -/
theorem matrixRREF_column_mem_prefix_iff {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) (j : Nat) (hj : j < n) :
    matrixColumnNat A j ∈ Submodule.span ℝ
      {w | w ∈ @HSpace.keptPrefix (finRealHSpace m)
        (matrixColumnNat A) (matrixRREFKeep A) j} ↔ matrixRREFKeep A j = false := by
  classical
  let g := matrixRREF A
  let col := fun q : Fin g.rank => fun i => A i (g.pivots q)
  let previous : Set (Fin g.rank) := {q | (g.pivots q).val < j}
  have hset : {w | w ∈ @HSpace.keptPrefix (finRealHSpace m)
      (matrixColumnNat A) (matrixRREFKeep A) j} = col '' previous := by
    ext w
    change (w ∈ @HSpace.keptPrefix (finRealHSpace m)
      (matrixColumnNat A) (matrixRREFKeep A) j) ↔ ∃ q, q ∈ previous ∧ col q = w
    rw [mem_rref_keptPrefix_iff A j w]
    constructor
    · rintro ⟨q, hq, hw⟩
      exact ⟨q, hq, hw.symm⟩
    · rintro ⟨q, hq, hw⟩
      exact ⟨q, hq, hw.symm⟩
  rw [hset]
  constructor
  · intro hmem
    by_contra hk
    have hp : ∃ q : Fin g.rank, (g.pivots q).val = j := by
      simpa [matrixRREFKeep, g] using hk
    obtain ⟨q, hq⟩ := hp
    have hcol : matrixColumnNat A j = col q := by
      simp only [matrixColumnNat, dif_pos hj, col]
      funext i
      exact congrArg (A i) (Fin.ext hq.symm)
    rw [hcol] at hmem
    exact (matrixRREF_pivot_columns_linearIndependent A).notMem_span_image
      (s := previous) (x := q) (by change ¬ (g.pivots q).val < j; omega) hmem
  · intro hk
    have hnot : ¬ ∃ q : Fin g.rank, (g.pivots q).val = j := by
      simpa [matrixRREFKeep, g] using hk
    simp only [matrixColumnNat, dif_pos hj]
    rw [matrixRREF_column_eq_sum_pivots A ⟨j, hj⟩]
    apply Submodule.sum_mem
    intro q _
    by_cases hq : (g.pivots q).val < j
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        (show col q ∈ col '' previous from ⟨q, hq, rfl⟩))
    · have hlt : j < (g.pivots q).val := by
        have hne : (g.pivots q).val ≠ j := fun he => hnot ⟨q, he⟩
        omega
      have hz : g.R (Fin.castLE g.rank_le_m q) ⟨j, hj⟩ = 0 :=
        g.left_of_pivot_zero q ⟨j, hj⟩ hlt
      change g.R (Fin.castLE g.rank_le_m q) ⟨j, hj⟩ • col q ∈ _
      rw [hz, zero_smul]
      exact Submodule.zero_mem _

/-- The increasing pivot enumeration equals filtering all column indices. -/
theorem matrixRREF_pivot_indices_eq_filter {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (List.finRange (matrixRREF A).rank).map (fun q => ((matrixRREF A).pivots q).val) =
      (List.range n).filter (matrixRREFKeep A) := by
  classical
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp (fun {i k} h => (matrixRREF A).pivots_strict_mono i k h)
  · exact List.pairwise_lt_range.filter _
  · intro j
    simp only [List.mem_map, List.mem_finRange, true_and, List.mem_filter,
      List.mem_range, matrixRREFKeep, decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨hq ▸ ((matrixRREF A).pivots q).isLt, q, hq⟩
    · rintro ⟨_, h⟩
      exact h

theorem standardRREFLexInd_proved : StandardRREFLexIndContract := by
  intro m n A
  rw [matrixColumnList_eq_range,
    HSpace.lexInd_range_eq_keptPrefix _ _ _ _ (matrixRREF_column_mem_prefix_iff A)]
  unfold HSpace.keptPrefix
  rw [← matrixRREF_pivot_indices_eq_filter]
  simp only [List.map_map]
  unfold matrixPivotColumnList
  apply List.map_congr_left
  intro q _
  simp [matrixColumnNat, (matrixRREF A).pivots q |>.isLt]

/-- Every valid decomposition selects exactly the source lexInd list, in order.
This makes the existing live correspondence independent of the RREF witness. -/
theorem rref_pivot_columns_eq_lexInd_of_decomposition {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (g : RREFDecomposition m n)
    (hg : A = g.E * g.R) :
    (finRealHSpace m).lexInd (matrixColumnList A) =
      (List.ofFn g.pivots).map (fun j => fun i => A i j) := by
  calc
    _ = matrixPivotColumnList A := (standardRREFLexInd_proved A).symm
    _ = (List.ofFn (matrixRREF A).pivots).map (fun j => fun i => A i j) := by
      simp only [matrixPivotColumnList, List.ofFn_eq_map, List.map_map, Function.comp_def]
    _ = _ := congrArg (List.map (fun j => fun i => A i j))
      (matrixRREF_pivots_unique A g hg)

end GLang
