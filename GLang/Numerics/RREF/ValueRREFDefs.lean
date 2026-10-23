import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-! Exact RREF decomposition contract, separated from its constructive existence
proof so consumers and the column-extension construction share one definition. -/
namespace GLang

/-- Reduced row echelon decomposition, including the ordered pivot and zero-row
invariants consumed by value semantics and the greedy basis correspondence. -/
structure RREFDecomposition (m n : Nat) where
  /-- Number of pivot rows (rank of the original matrix). -/
  rank : Nat
  rank_le_m : rank ≤ m
  rank_le_n : rank ≤ n
  /-- The RREF form itself: an `m × n` matrix. -/
  R : Matrix (Fin m) (Fin n) ℝ
  /-- For each pivot row `i < rank`, the column index of the leading
      `1` in that row. -/
  pivots : Fin rank → Fin n
  /-- The inverse row transformation: the original matrix factors as
      `A = E * R`. -/
  E : Matrix (Fin m) (Fin m) ℝ
  /-- A left-inverse of `E`, taking the original matrix to its RREF. -/
  E_inv : Matrix (Fin m) (Fin m) ℝ
  /-- `E_inv * E = I`. -/
  E_left_inv : E_inv * E = Matrix.diagonal (fun _ : Fin m => (1 : ℝ))

  /-- Pivot column indices are strictly monotone. -/
  pivots_strict_mono : ∀ i j : Fin rank, i.val < j.val →
    (pivots i).val < (pivots j).val
  /-- Each pivot entry equals `1`.
      The pivot row index `⟨i.val, _⟩` uses `rank_le_m` to view
      `Fin rank` as `Fin m`. -/
  pivot_entries_one : ∀ i : Fin rank,
    R ⟨i.val, Nat.lt_of_lt_of_le i.isLt rank_le_m⟩ (pivots i) = 1
  /-- Every entry above OR below a pivot in its column is `0`.
      This is what makes RREF *reduced* (as opposed to plain
      row-echelon form). -/
  pivot_columns_zero : ∀ i : Fin rank, ∀ k : Fin m,
    k.val ≠ i.val → R k (pivots i) = 0
  /-- Rows at or below index `rank` are entirely zero. -/
  zero_rows_below : ∀ k : Fin m, k.val ≥ rank →
    ∀ j : Fin n, R k j = 0
  /-- Entries to the left of a pivot (in its row) are `0`. -/
  left_of_pivot_zero : ∀ i : Fin rank, ∀ j : Fin n,
    j.val < (pivots i).val →
    R ⟨i.val, Nat.lt_of_lt_of_le i.isLt rank_le_m⟩ j = 0

end GLang
