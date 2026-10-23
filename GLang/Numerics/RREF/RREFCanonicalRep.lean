import GLang.Value.Supporting.TotalDimensionSemantics

/-! Choice-independent RREF representation for the live term-basis operation.
The appended identity block makes the inverse row operation observable directly
in the reduced matrix, so nonuniqueness at deficient row rank cannot leak here. -/
namespace GLang
open scoped BigOperators Matrix

/-- Select the appended identity columns of the candidate matrix. -/
def termsCandidateRightInverse (N K : ℕ) : Matrix (Fin (K + N)) (Fin N) ℝ :=
  fun j i => if j = Fin.natAdd K i then 1 else 0

/-- The identity tail witnesses full row rank, including `N = 0`. -/
theorem termsCandidateMatrix_rightInverse (N K : ℕ) (a : ℕ → ℝ) :
    termsCandidateMatrix N K a * termsCandidateRightInverse N K = 1 := by
  ext i j
  simp only [Matrix.mul_apply, termsCandidateRightInverse, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [termsCandidateMatrix, Matrix.one_apply, Fin.ext_iff]

/-- For every valid decomposition, the inverse row operation is exactly the
identity-tail block of its reduced matrix. -/
theorem termsCandidateMatrix_inverse_eq_tail (N K : ℕ) (a : ℕ → ℝ)
    (g : RREFDecomposition N (K + N))
    (hg : termsCandidateMatrix N K a = g.E * g.R) :
    g.E_inv = fun i j => g.R i (Fin.natAdd K j) := by
  rw [g.inverse_eq_reduced_mul _ _ hg (termsCandidateMatrix_rightInverse N K a)]
  ext i j
  simp [Matrix.mul_apply, termsCandidateRightInverse]

/-- The actual operational representation is determined by the canonical reduced
form; it does not observe an arbitrary choice of auxiliary row operations. -/
theorem termsRREFRepMatrix_eq_reduced_tail (N K : ℕ) (a c : ℕ → ℝ) :
    termsRREFRepMatrix N K a c = denotAsMatrix N N c *
      (Matrix.of (fun i j => (matrixRREF (termsCandidateMatrix N K a)).R i (Fin.natAdd K j))).transpose := by
  dsimp only [termsRREFRepMatrix]
  rw [termsCandidateMatrix_inverse_eq_tail N K a _ (matrixRREF_factor _)]
  rfl

/-- Every valid RREF implementation gives the same live representation matrix. -/
theorem termsRREFRepMatrix_eq_of_decomposition (N K : ℕ) (a c : ℕ → ℝ)
    (g : RREFDecomposition N (K + N))
    (hg : termsCandidateMatrix N K a = g.E * g.R) :
    termsRREFRepMatrix N K a c = denotAsMatrix N N c * g.E_inv.transpose := by
  dsimp only [termsRREFRepMatrix]
  rw [(matrixRREF (termsCandidateMatrix N K a)).inverse_eq g _
    (termsCandidateRightInverse N K) (matrixRREF_factor _) hg
    (termsCandidateMatrix_rightInverse N K a)]
end GLang
