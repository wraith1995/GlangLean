import GLang.Numerics.RREF.RREFColumnExtension
import GLang.Numerics.RREF.RREFUniqueness

/-! # Constructive row-reduced echelon form

`RREFDecomposition` retains the exact factorization and reduced-echelon
contract. Existence is proved by induction over columns: the zero-tail case
appends a dependent column; the nonzero-tail case constructs an invertible
clear-and-swap row operation and installs the next pivot. The construction
and its shape/factorization proofs are in `RREFColumnExtension`.

`Matrix.rref` chooses one proved witness. No RREF existence or numerical
coherence axiom is required. Public definitions and theorem signatures are
unchanged; the selected witness is not asserted to be computationally executable.
-/

namespace GLang
open Matrix

namespace Matrix

/-! ### Existence by constructive column extension -/

/-- The Gauss–Jordan successor step, with the original public signature. -/
theorem exists_rrefDecomp_inductive_step {m n : Nat}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (ih : ∀ (B : Matrix (Fin m) (Fin n) ℝ),
        ∃ decomp : RREFDecomposition m n, B = decomp.E * decomp.R) :
    ∃ decomp : RREFDecomposition m (n + 1),
      A = decomp.E * decomp.R :=
  exists_rrefDecomp_inductive_step_proved A ih

/-- Existence of an `RREFDecomposition` for any real `m × n` matrix,
    proved by recursion on `n`. -/
theorem exists_rrefDecomp (m n : Nat) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ decomp : RREFDecomposition m n, A = decomp.E * decomp.R := by
  induction n with
  | zero =>
    -- Base case: 0 columns. The witness is fully explicit; every
    -- shape constraint is vacuous (over `Fin 0`).
    refine ⟨{
      rank := 0
      rank_le_m := Nat.zero_le _
      rank_le_n := Nat.zero_le _
      R := A
      pivots := fun i => i.elim0
      E := 1
      E_inv := 1
      E_left_inv := by rw [Matrix.one_mul]; exact (Matrix.diagonal_one).symm
      pivots_strict_mono := fun i _ _ => i.elim0
      pivot_entries_one := fun i => i.elim0
      pivot_columns_zero := fun i => i.elim0
      zero_rows_below := fun _ _ j => j.elim0
      left_of_pivot_zero := fun i => i.elim0
    }, ?_⟩
    -- A = 1 * A holds by `Matrix.one_mul`.
    exact (Matrix.one_mul A).symm
  | succ n ih =>
    exact exists_rrefDecomp_inductive_step A ih

/-- The RREF of `A`, realized via `Classical.choose` of
    `Matrix.exists_rrefDecomp`. -/
noncomputable def rref {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    RREFDecomposition m n :=
  Classical.choose (Matrix.exists_rrefDecomp m n A)

theorem rref_factor {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    A = (rref A).E * (rref A).R :=
  Classical.choose_spec (Matrix.exists_rrefDecomp m n A)

end Matrix

/-! ### Existence (consumer-facing form) -/

/-- Every real matrix admits an RREF factorization with the tightened
    shape constraints. Realized via `Matrix.rref` (defined via
    classical choice over `Matrix.exists_rrefDecomp`). -/
theorem Matrix.exists_rref (m n : Nat) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ rref : RREFDecomposition m n,
      A = rref.E * rref.R :=
  ⟨Matrix.rref A, Matrix.rref_factor A⟩

/-- The chosen RREF decomposition of `A`. -/
noncomputable def matrixRREF {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    RREFDecomposition m n :=
  Matrix.rref A

/-- The RREF factorization (consumer-facing form). -/
theorem matrixRREF_factor {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    A = (matrixRREF A).E * (matrixRREF A).R :=
  Matrix.rref_factor A

/-- Any valid decomposition computes the same reduced matrix as the live selector. -/
theorem matrixRREF_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (g : RREFDecomposition m n) (hg : A = g.E * g.R) :
    (matrixRREF A).R = g.R :=
  (matrixRREF A).reduced_eq g A (matrixRREF_factor A) hg

/-- Ordered pivots are independent of the selected decomposition witness. -/
theorem matrixRREF_pivots_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (g : RREFDecomposition m n) (hg : A = g.E * g.R) :
    List.ofFn (matrixRREF A).pivots = List.ofFn g.pivots :=
  (matrixRREF A).pivots_eq g A (matrixRREF_factor A) hg

/-- Reducing a reduced matrix again leaves it unchanged, including empty shapes. -/
theorem matrixRREF_idempotent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrixRREF (matrixRREF A).R).R = (matrixRREF A).R := by
  let g := matrixRREF A
  let h : RREFDecomposition m n := { g with
    E := 1
    E_inv := 1
    E_left_inv := by simp }
  exact matrixRREF_unique g.R h (by simp [h])

/-- Each pivot column index is bounded by `n` (already enforced by the
    `Fin n` return type of `pivots`; restated for completeness as a
    soundness target). -/
theorem matrixRREF_pivots_lt_n {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin (matrixRREF A).rank) :
    ((matrixRREF A).pivots i).val < n :=
  ((matrixRREF A).pivots i).isLt

end GLang
